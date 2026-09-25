//! Floating-point operations as circuits, bit for bit what bitwright's software arithmetic
//! (`fp::soft`) computes: the canonical NaN for every NaN result, IEEE 754 rounding in the
//! five modes, `min`/`max` as minimumNumber/maximumNumber with `−0 < +0`, saturating
//! conversions to integers (a NaN converts to 0).
//!
//! Every finite nonzero operand is decoded to `(−1)^s · m · 2^e` with `m` normalized to `p`
//! bits (subnormals shifted up by their leading zeros); each operation computes its exact result
//! or a truncation with a sticky bit, and [`round`] turns it into an encoding: normalize,
//! denormalize below `emin` (jamming what falls off), keep `p` bits, round by the round bit, the
//! sticky bits and the mode, carry into the exponent, overflow by the mode, pack. Special
//! operands are handled in the order the software's cases take them.

use super::Blaster;
use super::aig::{Aig, FALSE, L, TRUE};
use super::blast::{self, Bits};
use crate::error::Error;
use crate::fp::{FpFormat, FpOp, RoundingMode};

/// A format's parameters.
#[derive(Copy, Clone)]
struct F {
    eb: usize,
    p: usize,
    w: usize,
    bias: i64,
    emin: i64,
}

impl F {
    fn of(f: FpFormat) -> F {
        let (eb, p) = (f.eb() as usize, f.sb() as usize);
        let bias = (1i64 << (eb - 1)) - 1;
        F {
            eb,
            p,
            w: eb + p,
            bias,
            emin: 1 - bias,
        }
    }
}

/// Circuits over one AIG, with signed exponents of `ew` bits.
struct C<'g> {
    g: &'g mut Aig,
    ew: usize,
}

/// A decoded operand: flags, and for a finite nonzero one `sig · 2^exp` with `sig` of `p` bits,
/// its top bit set.
struct Un {
    sign: L,
    nan: L,
    inf: L,
    zero: L,
    sig: Bits,
    exp: Bits,
}

impl C<'_> {
    /// The signed constant `v` in `ew` bits.
    fn k(&self, v: i64) -> Bits {
        blast::small(self.ew, v as u64)
    }

    fn add(&mut self, a: &[L], b: &[L]) -> Bits {
        blast::add(self.g, a, b)
    }

    fn sub(&mut self, a: &[L], b: &[L]) -> Bits {
        blast::sub(self.g, a, b)
    }

    /// Signed `a < b`.
    fn slt(&mut self, a: &[L], b: &[L]) -> L {
        blast::slt(self.g, a, b)
    }

    fn mux(&mut self, c: L, t: &[L], e: &[L]) -> Bits {
        blast::mux(self.g, c, t, e)
    }

    fn and(&mut self, a: L, b: L) -> L {
        self.g.and(a, b)
    }

    fn or(&mut self, a: L, b: L) -> L {
        self.g.or(a, b)
    }

    fn any(&mut self, a: &[L]) -> L {
        self.g.or_all(a)
    }

    fn is_zero(&mut self, a: &[L]) -> L {
        self.any(a) ^ 1
    }

    /// `a` zero-extended (or truncated) to `w` bits.
    fn zext(a: &[L], w: usize) -> Bits {
        let mut v = a.to_vec();
        v.resize(w, FALSE);
        v
    }

    /// The count of leading zeros of `a`, as a nonnegative exponent-width value.
    fn clz(&mut self, a: &[L]) -> Bits {
        let c = blast::clz(self.g, a);
        Self::zext(&c, self.ew)
    }

    /// A signed amount `s` clamped to `[0, max]`, as an unsigned value of enough bits.
    fn clamp(&mut self, s: &[L], max: usize) -> Bits {
        let neg = *s.last().unwrap_or(&FALSE);
        let m = self.k(max as i64);
        let over = self.slt(&m, s);
        let bits = (usize::BITS - max.leading_zeros()) as usize + 1;
        let low: Bits = s[..bits.min(s.len())].to_vec();
        let low = Self::zext(&low, bits);
        let mb = blast::small(bits, max as u64);
        let z = vec![FALSE; bits];
        let t = self.mux(over, &mb, &low);
        self.mux(neg, &z, &t)
    }

    /// `a << s` (unsigned `s`), in `a`'s width.
    fn shl(&mut self, a: &[L], s: &[L]) -> Bits {
        blast::shift(self.g, a, s, true, FALSE)
    }

    /// `a >> s` (unsigned `s`), with the bits shifted out ORed into bit 0.
    fn shr_jam(&mut self, a: &[L], s: &[L]) -> Bits {
        let w = a.len();
        let shifted = blast::shift(self.g, a, s, false, FALSE);
        // The bits lost: a & ~(ones << s).
        let ones = vec![TRUE; w];
        let high = blast::shift(self.g, &ones, s, true, FALSE);
        let lost_bits: Bits = a
            .iter()
            .zip(&high)
            .map(|(&x, &h)| self.g.and(x, h ^ 1))
            .collect();
        let lost = self.any(&lost_bits);
        let mut out = shifted;
        if let Some(b0) = out.first_mut() {
            *b0 = self.g.or(*b0, lost);
        }
        out
    }

    // ----- encodings --------------------------------------------------------------------------

    fn pack(f: F, sign: L, field: &[L], mant: &[L]) -> Bits {
        let mut v: Bits = mant.to_vec();
        v.extend_from_slice(field);
        v.push(sign);
        debug_assert_eq!(v.len(), f.w);
        v
    }

    fn nan(f: F) -> Bits {
        let mut mant = vec![FALSE; f.p - 1];
        if f.p >= 2 {
            mant[f.p - 2] = TRUE;
        }
        Self::pack(f, FALSE, &vec![TRUE; f.eb], &mant)
    }

    fn inf(f: F, sign: L) -> Bits {
        Self::pack(f, sign, &vec![TRUE; f.eb], &vec![FALSE; f.p - 1])
    }

    fn zero(f: F, sign: L) -> Bits {
        Self::pack(f, sign, &vec![FALSE; f.eb], &vec![FALSE; f.p - 1])
    }

    fn max_finite(f: F, sign: L) -> Bits {
        let mut field = vec![TRUE; f.eb];
        field[0] = FALSE;
        Self::pack(f, sign, &field, &vec![TRUE; f.p - 1])
    }

    fn unpack(&mut self, f: F, x: &[L]) -> Un {
        let sign = x[f.w - 1];
        let t: Bits = x[..f.p - 1].to_vec();
        let e: Bits = x[f.p - 1..f.p - 1 + f.eb].to_vec();
        let e_ones = self.g.and_all(&e);
        let e_zero = self.is_zero(&e);
        let t_zero = self.is_zero(&t);
        let nan = self.and(e_ones, t_zero ^ 1);
        let inf = self.and(e_ones, t_zero);
        let zero = self.and(e_zero, t_zero);
        // Normal: 1.t, exp = e − bias − p + 1.
        let mut sig_n = t.clone();
        sig_n.push(TRUE);
        let ez = Self::zext(&e, self.ew);
        let kn = self.k(f.bias + f.p as i64 - 1);
        let exp_n = self.sub(&ez, &kn);
        // Subnormal: t shifted up by its leading zeros in p bits.
        let mut tp = t.clone();
        tp.push(FALSE);
        let lz = blast::clz(self.g, &tp);
        let sig_s = self.shl(&tp, &lz);
        let lze = Self::zext(&lz, self.ew);
        let ks = self.k(f.emin - f.p as i64 + 1);
        let exp_s = self.sub(&ks, &lze);
        let sub = e_zero;
        let sig = self.mux(sub, &sig_s, &sig_n);
        let exp = self.mux(sub, &exp_s, &exp_n);
        Un {
            sign,
            nan,
            inf,
            zero,
            sig,
            exp,
        }
    }

    fn is_nan(&mut self, f: F, x: &[L]) -> L {
        let t: Bits = x[..f.p - 1].to_vec();
        let e: Bits = x[f.p - 1..f.p - 1 + f.eb].to_vec();
        let e_ones = self.g.and_all(&e);
        let t_zero = self.is_zero(&t);
        self.and(e_ones, t_zero ^ 1)
    }

    /// Whether to round up, by the mode.
    fn round_up(&mut self, rm: RoundingMode, sign: L, lsb: L, r: L, s: L) -> L {
        let rs = self.or(r, s);
        match rm {
            RoundingMode::Rne => {
                let t = self.or(s, lsb);
                self.and(r, t)
            }
            RoundingMode::Rna => r,
            RoundingMode::Rtp => self.and(sign ^ 1, rs),
            RoundingMode::Rtn => self.and(sign, rs),
            _ => FALSE,
        }
    }

    /// `(−1)^sign · (sig + δ) · 2^exp` rounded to `f`, `δ ∈ [0, 1)` nonzero exactly when
    /// `sticky`; `sig` nonzero, of at least `p + 1` bits.
    #[allow(clippy::too_many_arguments)]
    fn round(&mut self, f: F, rm: RoundingMode, sign: L, sig: &[L], exp: &[L], sticky: L) -> Bits {
        // Room for a round bit and a sticky bit below the kept p (zeros on top change nothing:
        // the normalization shifts them out).
        let sig = Self::zext(sig, sig.len().max(f.p + 2));
        let n = sig.len();
        let lz = self.clz(&sig);
        let nb = (usize::BITS - n.leading_zeros()) as usize + 1;
        let lzs: Bits = lz[..nb.min(lz.len())].to_vec();
        let sn = self.shl(&sig, &lzs);
        // e: the exponent of the leading one.
        let top = self.k(n as i64 - 1);
        let e0 = self.add(exp, &top);
        let e = self.sub(&e0, &lz);
        // Denormalize below emin.
        let kmin = self.k(f.emin);
        let ds_s = self.sub(&kmin, &e);
        let denorm = {
            let z = self.k(0);
            self.slt(&z, &ds_s)
        };
        let ds = self.clamp(&ds_s, n + 1);
        let sh = self.shr_jam(&sn, &ds);
        let m: Bits = sh[n - f.p..].to_vec();
        let r = sh[n - f.p - 1];
        let below = self.any(&sh[..n - f.p - 1]);
        let s = self.or(below, sticky);
        let up = self.round_up(rm, sign, m[0], r, s);
        let mut inc = vec![FALSE; f.p + 1];
        inc[0] = up;
        let m1 = self.add(&Self::zext(&m, f.p + 1), &inc);
        let carry = m1[f.p];
        let m2 = self.mux(carry, &m1[1..=f.p], &m1[..f.p]);
        let e_base = self.mux(denorm, &kmin, &e);
        let mut cinc = vec![FALSE; self.ew];
        cinc[0] = carry;
        let e_res = self.add(&e_base, &cinc);
        let normal = m2[f.p - 1];
        let kb = self.k(f.bias);
        let biased = self.add(&e_res, &kb);
        let kmax = self.k((1i64 << f.eb) - 2);
        let over_field = self.slt(&kmax, &biased);
        let over = self.and(normal, over_field);
        let zf = vec![FALSE; f.eb];
        let field = self.mux(normal, &biased[..f.eb], &zf);
        let packed = Self::pack(f, sign, &field, &m2[..f.p - 1]);
        let ovf = self.overflow(f, rm, sign);
        self.mux(over, &ovf, &packed)
    }

    fn overflow(&mut self, f: F, rm: RoundingMode, sign: L) -> Bits {
        let (i, m) = (Self::inf(f, sign), Self::max_finite(f, sign));
        match rm {
            RoundingMode::Rne | RoundingMode::Rna => i,
            RoundingMode::Rtp => self.mux(sign, &m, &i),
            RoundingMode::Rtn => self.mux(sign, &i, &m),
            _ => m,
        }
    }

    // ----- operations ---------------------------------------------------------------------------

    /// `x + y` of finite nonzero operands (the guard-and-jam alignment).
    fn add_finite(&mut self, f: F, rm: RoundingMode, x: &Un, y: &Un) -> Bits {
        // The operand with the larger exponent first.
        let y_bigger = self.slt(&x.exp, &y.exp);
        let (sa, sb) = (
            self.g.mux(y_bigger, y.sign, x.sign),
            self.g.mux(y_bigger, x.sign, y.sign),
        );
        let ma = self.mux(y_bigger, &y.sig, &x.sig);
        let mb = self.mux(y_bigger, &x.sig, &y.sig);
        let ea = self.mux(y_bigger, &y.exp, &x.exp);
        let eb = self.mux(y_bigger, &x.exp, &y.exp);
        let wide = f.p + 4;
        let mut a3 = vec![FALSE; 3];
        a3.extend_from_slice(&ma);
        let a3 = Self::zext(&a3, wide);
        let mut b3 = vec![FALSE; 3];
        b3.extend_from_slice(&mb);
        let b3 = Self::zext(&b3, wide);
        let diff = self.sub(&ea, &eb);
        let d = self.clamp(&diff, wide + 1);
        let bj = self.shr_jam(&b3, &d);
        let same = self.g.xnor(sa, sb);
        let sum = self.add(&a3, &bj);
        let a_ge = blast::ult(self.g, &a3, &bj) ^ 1;
        let d1 = self.sub(&a3, &bj);
        let d2 = self.sub(&bj, &a3);
        let dsel = self.mux(a_ge, &d1, &d2);
        let dsign = self.g.mux(a_ge, sa, sb);
        let s = self.mux(same, &sum, &dsel);
        let sign = self.g.mux(same, sa, dsign);
        let k3 = self.k(3);
        let base = self.sub(&ea, &k3);
        let rounded = self.round(f, rm, sign, &s, &base, FALSE);
        let zero_sum = self.is_zero(&s);
        let z = Self::zero(f, if rm == RoundingMode::Rtn { TRUE } else { FALSE });
        self.mux(zero_sum, &z, &rounded)
    }

    fn fadd(&mut self, f: F, rm: RoundingMode, a: &[L], b: &[L]) -> Bits {
        let (x, y) = (self.unpack(f, a), self.unpack(f, b));
        let fin = self.add_finite(f, rm, &x, &y);
        // Special cases, the software's order read backwards (later ones overridden first).
        let mut r = fin;
        r = self.mux(y.zero, a, &r);
        r = self.mux(x.zero, b, &r);
        let both_zero = self.and(x.zero, y.zero);
        let same_sign = self.g.xnor(x.sign, y.sign);
        let zz_same = Self::zero(f, x.sign);
        let zz_diff = Self::zero(f, if rm == RoundingMode::Rtn { TRUE } else { FALSE });
        let zz = self.mux(same_sign, &zz_same, &zz_diff);
        r = self.mux(both_zero, &zz, &r);
        let iy = Self::inf(f, y.sign);
        r = self.mux(y.inf, &iy, &r);
        let ix = Self::inf(f, x.sign);
        r = self.mux(x.inf, &ix, &r);
        let both_inf = self.and(x.inf, y.inf);
        let opposite = self.and(both_inf, same_sign ^ 1);
        let n = Self::nan(f);
        r = self.mux(opposite, &n, &r);
        let any_nan = self.or(x.nan, y.nan);
        self.mux(any_nan, &n, &r)
    }

    fn fmul(&mut self, f: F, rm: RoundingMode, a: &[L], b: &[L]) -> Bits {
        let (x, y) = (self.unpack(f, a), self.unpack(f, b));
        let sign = self.g.xor(x.sign, y.sign);
        let prod = blast::mul(
            self.g,
            &Self::zext(&x.sig, 2 * f.p),
            &Self::zext(&y.sig, 2 * f.p),
        );
        let e = self.add(&x.exp, &y.exp);
        let mut r = self.round(f, rm, sign, &prod, &e, FALSE);
        let any_zero = self.or(x.zero, y.zero);
        let z = Self::zero(f, sign);
        r = self.mux(any_zero, &z, &r);
        let any_inf = self.or(x.inf, y.inf);
        let i = Self::inf(f, sign);
        r = self.mux(any_inf, &i, &r);
        let zi = self.and(any_zero, any_inf);
        let n = Self::nan(f);
        r = self.mux(zi, &n, &r);
        let any_nan = self.or(x.nan, y.nan);
        self.mux(any_nan, &n, &r)
    }

    fn fdiv(&mut self, f: F, rm: RoundingMode, a: &[L], b: &[L]) -> Bits {
        let (x, y) = (self.unpack(f, a), self.unpack(f, b));
        let sign = self.g.xor(x.sign, y.sign);
        // (mx · 2^(p+2)) / my.
        let wq = 2 * f.p + 2;
        let mut num = vec![FALSE; f.p + 2];
        num.extend_from_slice(&x.sig);
        let num = Self::zext(&num, wq);
        let den = Self::zext(&y.sig, wq);
        let (q, rem) = blast::udivrem(self.g, &num, &den);
        let sticky = self.any(&rem);
        let e0 = self.sub(&x.exp, &y.exp);
        let kp = self.k(f.p as i64 + 2);
        let e = self.sub(&e0, &kp);
        let mut r = self.round(f, rm, sign, &q, &e, sticky);
        // Order (later overrides first): zero result, inf result, NaN.
        let zero_res = self.or(y.inf, x.zero);
        let z = Self::zero(f, sign);
        r = self.mux(zero_res, &z, &r);
        let inf_res = self.or(x.inf, y.zero);
        let i = Self::inf(f, sign);
        r = self.mux(inf_res, &i, &r);
        let zz = self.and(x.zero, y.zero);
        let ii = self.and(x.inf, y.inf);
        let nan_res0 = self.or(zz, ii);
        let any_nan = self.or(x.nan, y.nan);
        let nan_res = self.or(nan_res0, any_nan);
        let n = Self::nan(f);
        self.mux(nan_res, &n, &r)
    }

    /// The integer square root of `n` (an even number of bits) and whether it is inexact.
    fn isqrt(&mut self, n: &[L]) -> (Bits, L) {
        let half = n.len() / 2;
        // The remainder stays at most twice the root: `half + 1` bits, `half + 3` shifted.
        let w = half + 4;
        let mut rem: Bits = vec![FALSE; w];
        let mut root: Bits = vec![FALSE; half];
        for i in (0..half).rev() {
            // rem = rem · 4 + next two bits.
            let mut r4 = vec![n[2 * i], n[2 * i + 1]];
            r4.extend_from_slice(&rem[..w - 2]);
            // trial = root · 4 + 1.
            let mut trial = vec![TRUE, FALSE];
            trial.extend_from_slice(&root);
            let trial = Self::zext(&trial, w);
            let ge = blast::ult(self.g, &r4, &trial) ^ 1;
            let d = self.sub(&r4, &trial);
            rem = self.mux(ge, &d, &r4);
            // root = root · 2 + ge.
            let mut nr = vec![ge];
            nr.extend_from_slice(&root[..half - 1]);
            root = nr;
        }
        let inexact = self.any(&rem);
        (root, inexact)
    }

    fn fsqrt(&mut self, f: F, rm: RoundingMode, a: &[L]) -> Bits {
        let x = self.unpack(f, a);
        // An even exponent: m = sig · 2 when exp is odd.
        let odd = x.exp[0];
        let sig1 = Self::zext(&x.sig, f.p + 1);
        let mut sig2 = vec![FALSE];
        sig2.extend_from_slice(&x.sig);
        let m = self.mux(odd, &sig2, &sig1);
        let mut oddk = vec![FALSE; self.ew];
        oddk[0] = odd;
        let e = self.sub(&x.exp, &oddk);
        // Scale so the root has at least p + 2 bits.
        let k = (f.p + 4).div_ceil(2);
        let mut n = vec![FALSE; 2 * k];
        n.extend_from_slice(&m);
        if n.len() % 2 == 1 {
            n.push(FALSE);
        }
        let (root, sticky) = self.isqrt(&n);
        // e / 2 (e even) − k.
        let half_e: Bits = {
            let mut v = e[1..].to_vec();
            v.push(*e.last().unwrap_or(&FALSE));
            v
        };
        let kk = self.k(k as i64);
        let ee = self.sub(&half_e, &kk);
        let mut r = self.round(f, rm, FALSE, &root, &ee, sticky);
        // Order (later overrides first): negative → NaN, +∞ → itself, zero → itself, NaN.
        let n_ = Self::nan(f);
        let neg_fin = {
            let nz = self.or(x.zero, x.nan);
            let not_special = self.or(nz, x.inf) ^ 1;
            self.and(x.sign, not_special)
        };
        r = self.mux(neg_fin, &n_, &r);
        let neg_inf = self.and(x.inf, x.sign);
        r = self.mux(neg_inf, &n_, &r);
        let pos_inf = self.and(x.inf, x.sign ^ 1);
        r = self.mux(pos_inf, a, &r);
        r = self.mux(x.zero, a, &r);
        self.mux(x.nan, &n_, &r)
    }

    fn ffma(&mut self, f: F, rm: RoundingMode, a: &[L], b: &[L], c: &[L]) -> Bits {
        let (x, y, z) = (self.unpack(f, a), self.unpack(f, b), self.unpack(f, c));
        let sp = self.g.xor(x.sign, y.sign);
        let fw = 2 * f.p + 6;
        let mp = blast::mul(
            self.g,
            &Self::zext(&x.sig, 2 * f.p),
            &Self::zext(&y.sig, 2 * f.p),
        );
        let ep = self.add(&x.exp, &y.exp);
        // hp = bits(mp) − 1 + ep; hc = p − 1 + ec.
        let lzp = self.clz(&mp);
        let kp = self.k(2 * f.p as i64 - 1);
        let hp0 = self.add(&ep, &kp);
        let hp = self.sub(&hp0, &lzp);
        let kc = self.k(f.p as i64 - 1);
        let hc = self.add(&z.exp, &kc);
        let k2 = self.k(2);
        let hp2 = self.add(&hp, &k2);
        let c_big = self.slt(&hp2, &hc);
        let k3 = self.k(3);
        // Alternative 1: the addend larger, x = mc << 3 at base ec − 3, y = product jammed.
        let base1 = self.sub(&z.exp, &k3);
        let mut x1 = vec![FALSE; 3];
        x1.extend_from_slice(&z.sig);
        let x1 = Self::zext(&x1, fw);
        let d1s = self.sub(&base1, &ep);
        let d1 = self.clamp(&d1s, fw + 1);
        let y1 = self.shr_jam(&Self::zext(&mp, fw), &d1);
        // Alternative 2: the product larger, x = mp << 3 at base ep − 3, y = mc aligned.
        let base2 = self.sub(&ep, &k3);
        let mut x2 = vec![FALSE; 3];
        x2.extend_from_slice(&mp);
        let x2 = Self::zext(&x2, fw);
        let up_s = self.sub(&z.exp, &base2);
        let neg_up = *up_s.last().unwrap_or(&FALSE);
        let up_amt = self.clamp(&up_s, fw);
        let yl = self.shl(&Self::zext(&z.sig, fw), &up_amt);
        let dn_s = self.sub(&base2, &z.exp);
        let dn_amt = self.clamp(&dn_s, fw + 1);
        let yr = self.shr_jam(&Self::zext(&z.sig, fw), &dn_amt);
        let y2 = self.mux(neg_up, &yr, &yl);
        let xv = self.mux(c_big, &x1, &x2);
        let yv = self.mux(c_big, &y1, &y2);
        let sx = self.g.mux(c_big, z.sign, sp);
        let sy = self.g.mux(c_big, sp, z.sign);
        let base = self.mux(c_big, &base1, &base2);
        let same = self.g.xnor(sx, sy);
        let xw = Self::zext(&xv, fw + 1);
        let yw = Self::zext(&yv, fw + 1);
        let sum = self.add(&xw, &yw);
        let x_ge = blast::ult(self.g, &xw, &yw) ^ 1;
        let dd1 = self.sub(&xw, &yw);
        let dd2 = self.sub(&yw, &xw);
        let dsel = self.mux(x_ge, &dd1, &dd2);
        let dsign = self.g.mux(x_ge, sx, sy);
        let s = self.mux(same, &sum, &dsel);
        let sign = self.g.mux(same, sx, dsign);
        let finite = self.round(f, rm, sign, &s, &base, FALSE);
        let zero_sum = self.is_zero(&s);
        let rtn = if rm == RoundingMode::Rtn { TRUE } else { FALSE };
        let zr = Self::zero(f, rtn);
        let mut r = self.mux(zero_sum, &zr, &finite);
        // The addend zero (and the product not): the product rounded alone.
        let prod_only = self.round(f, rm, sp, &mp, &ep, FALSE);
        r = self.mux(z.zero, &prod_only, &r);
        // A zero product: exactly c + (±0).
        let zero_prod = self.or(x.zero, y.zero);
        let zc_same = self.g.xnor(z.sign, sp);
        let zsame = Self::zero(f, z.sign);
        let zz = self.mux(zc_same, &zsame, &zr);
        let zp = self.mux(z.zero, &zz, c);
        r = self.mux(zero_prod, &zp, &r);
        // The addend infinite (the product finite): c.
        r = self.mux(z.inf, c, &r);
        // An infinite product.
        let inf_prod = self.or(x.inf, y.inf);
        let ip = Self::inf(f, sp);
        let n = Self::nan(f);
        let c_opp = {
            let d = self.g.xor(z.sign, sp);
            self.and(z.inf, d)
        };
        let ipr = self.mux(c_opp, &n, &ip);
        r = self.mux(inf_prod, &ipr, &r);
        // 0 · ∞ and NaN operands.
        let zi1 = self.and(x.inf, y.zero);
        let zi2 = self.and(x.zero, y.inf);
        let zi = self.or(zi1, zi2);
        let nans0 = self.or(x.nan, y.nan);
        let nans1 = self.or(nans0, z.nan);
        let nans = self.or(nans1, zi);
        self.mux(nans, &n, &r)
    }

    /// `(−1)^sign · mag · 2^exp` exactly (nonzero, representable).
    fn exact(&mut self, f: F, sign: L, mag: &[L], exp: &[L]) -> Bits {
        self.round(f, RoundingMode::Rne, sign, mag, exp, FALSE)
    }

    fn frem(&mut self, f: F, a: &[L], b: &[L]) -> Result<Bits, Error> {
        let (x, y) = (self.unpack(f, a), self.unpack(f, b));
        let steps = ((1usize << f.eb) + 2 * f.p) as u64;
        if steps * (f.p as u64) > 1 << 20 {
            return Err(Error::Unsupported(
                "the remainder of so wide an exponent range".into(),
            ));
        }
        let pw = f.p + 2;
        let my = Self::zext(&y.sig, pw);
        let two_my = {
            let mut v = vec![FALSE];
            v.extend_from_slice(&y.sig);
            Self::zext(&v, pw)
        };
        // d = ex − ey ≥ 0: (mx · 2^d) mod 2my by repeated doubling.
        let d_s = self.sub(&x.exp, &y.exp);
        let max_d = (1usize << f.eb) + 2 * f.p;
        let d = self.clamp(&d_s, max_d);
        let mut r = Self::zext(&x.sig, pw);
        // mx < 2my (both p-bit normalized, mx < 2^p ≤ 2my): already reduced.
        for i in 0..max_d {
            // Active while i < d.
            let ik = blast::small(d.len(), i as u64);
            let active = blast::ult(self.g, &ik, &d);
            let mut dbl = vec![FALSE];
            dbl.extend_from_slice(&r[..pw - 1]);
            let ge = blast::ult(self.g, &dbl, &two_my) ^ 1;
            let sub = self.sub(&dbl, &two_my);
            let red = self.mux(ge, &sub, &dbl);
            r = self.mux(active, &red, &r);
        }
        let r2 = r;
        let odd = blast::ult(self.g, &r2, &my) ^ 1;
        let r2m = self.sub(&r2, &my);
        let rr = self.mux(odd, &r2m, &r2);
        let mut twice = vec![FALSE];
        twice.extend_from_slice(&rr[..pw - 1]);
        let gt = blast::ult(self.g, &my, &twice);
        let eq = blast::eq(self.g, &twice, &my);
        let tie_odd = self.and(eq, odd);
        let down = self.or(gt, tie_odd);
        let mdown = self.sub(&my, &rr);
        let mag = self.mux(down, &mdown, &rr);
        let sign = self.g.xor(x.sign, down);
        let mag_zero = self.is_zero(&mag);
        let ex_r = self.exact(f, sign, &mag, &y.exp);
        let zx = Self::zero(f, x.sign);
        let r_ge = self.mux(mag_zero, &zx, &ex_r);
        // ex < ey: ey − ex ≥ 2 gives a; ey = ex + 1 compares mx with my.
        let k1 = self.k(1);
        let ex1 = self.add(&x.exp, &k1);
        let adjacent = blast::eq(self.g, &ex1, &y.exp);
        let mx_gt = blast::ult(self.g, &my, &Self::zext(&x.sig, pw));
        let two_minus = self.sub(&two_my, &Self::zext(&x.sig, pw));
        let flip = self.exact(f, x.sign ^ 1, &two_minus, &x.exp);
        let adj_r = self.mux(mx_gt, &flip, a);
        let less_r = self.mux(adjacent, &adj_r, a);
        let ex_lt = self.slt(&x.exp, &y.exp);
        let mut res = self.mux(ex_lt, &less_r, &r_ge);
        // Specials: zero a or infinite b give a; NaNs, infinite a or zero b give NaN.
        let keep_a = self.or(x.zero, y.inf);
        res = self.mux(keep_a, a, &res);
        let n = Self::nan(f);
        let bad0 = self.or(x.nan, y.nan);
        let bad1 = self.or(bad0, x.inf);
        let bad = self.or(bad1, y.zero);
        Ok(self.mux(bad, &n, &res))
    }

    fn fround(&mut self, f: F, rm: RoundingMode, a: &[L]) -> Bits {
        let x = self.unpack(f, a);
        // d = −exp; the integer part and the round and sticky bits below it.
        let zero_e = self.k(0);
        let d_s = self.sub(&zero_e, &x.exp);
        let d = self.clamp(&d_s, f.p + 1);
        let w = f.p + 2;
        let mut ext = vec![FALSE; 2];
        ext.extend_from_slice(&x.sig);
        let ext = Self::zext(&ext, w + 2);
        // ext = sig · 4; shifting right by d keeps the integer part above bit 2, the round bit
        // at bit 1 and the jammed rest at bit 0.
        let sh = self.shr_jam(&ext, &d);
        let hi: Bits = sh[2..].to_vec();
        let r = sh[1];
        let s = sh[0];
        let up = self.round_up(rm, x.sign, hi[0], r, s);
        let mut inc = vec![FALSE; hi.len()];
        inc[0] = up;
        let k = self.add(&hi, &inc);
        let k_zero = self.is_zero(&k);
        let zero_e2 = self.k(0);
        let rounded = self.round(f, rm, x.sign, &k, &zero_e2, FALSE);
        let zs = Self::zero(f, x.sign);
        let mut res = self.mux(k_zero, &zs, &rounded);
        // exp ≥ 0: already integral.
        let neg_exp = self.slt(&x.exp, &zero_e);
        res = self.mux(neg_exp, &res, a);
        let keep = self.or(x.inf, x.zero);
        res = self.mux(keep, a, &res);
        let n = Self::nan(f);
        self.mux(x.nan, &n, &res)
    }

    /// Sign-magnitude comparison of non-NaN encodings (`−0 < +0`): `a < b`.
    fn total_lt(&mut self, f: F, a: &[L], b: &[L]) -> L {
        let (sa, sb) = (a[f.w - 1], b[f.w - 1]);
        let (ma, mb) = (&a[..f.w - 1], &b[..f.w - 1]);
        let pos_lt = blast::ult(self.g, ma, mb);
        let neg_lt = blast::ult(self.g, mb, ma);
        let both_pos = self.and(sa ^ 1, sb ^ 1);
        let both_neg = self.and(sa, sb);
        let t1 = self.and(both_pos, pos_lt);
        let t2 = self.and(both_neg, neg_lt);
        let t3 = self.and(sa, sb ^ 1);
        let t = self.or(t1, t2);
        self.or(t, t3)
    }

    fn fminmax(&mut self, f: F, a: &[L], b: &[L], max: bool) -> Bits {
        let (na, nb) = (self.is_nan(f, a), self.is_nan(f, b));
        let pick_b = if max {
            self.total_lt(f, a, b)
        } else {
            self.total_lt(f, b, a)
        };
        let mut r = self.mux(pick_b, b, a);
        r = self.mux(nb, a, &r);
        r = self.mux(na, b, &r);
        let both = self.and(na, nb);
        let n = Self::nan(f);
        self.mux(both, &n, &r)
    }

    fn fcmp(&mut self, f: F, op: FpOp, a: &[L], b: &[L]) -> L {
        let (na, nb) = (self.is_nan(f, a), self.is_nan(f, b));
        let unordered = self.or(na, nb);
        let za = self.is_zero(&a[..f.w - 1]);
        let zb = self.is_zero(&b[..f.w - 1]);
        let both_zero = self.and(za, zb);
        let same = blast::eq(self.g, a, b);
        let eq = self.or(same, both_zero);
        let lt0 = self.total_lt(f, a, b);
        let lt = self.and(lt0, both_zero ^ 1);
        let r = match op {
            FpOp::Eq => eq,
            FpOp::Lt => lt,
            _ => self.or(lt, eq),
        };
        self.and(r, unordered ^ 1)
    }

    fn fconvert(&mut self, from: F, to: F, rm: RoundingMode, a: &[L]) -> Bits {
        let x = self.unpack(from, a);
        let mut r = self.round(to, rm, x.sign, &x.sig, &x.exp, FALSE);
        let z = Self::zero(to, x.sign);
        r = self.mux(x.zero, &z, &r);
        let i = Self::inf(to, x.sign);
        r = self.mux(x.inf, &i, &r);
        let n = Self::nan(to);
        self.mux(x.nan, &n, &r)
    }

    fn of_int(&mut self, f: F, rm: RoundingMode, v: &[L], signed: bool) -> Bits {
        let neg = if signed {
            *v.last().unwrap_or(&FALSE)
        } else {
            FALSE
        };
        let nv = blast::neg(self.g, v);
        let mag = self.mux(neg, &nv, v);
        let zero = self.is_zero(&mag);
        let e0 = self.k(0);
        let r = self.round(f, rm, neg, &mag, &e0, FALSE);
        let z = Self::zero(f, FALSE);
        self.mux(zero, &z, &r)
    }

    fn int_of(&mut self, f: F, rm: RoundingMode, a: &[L], n: usize, signed: bool) -> Bits {
        let x = self.unpack(f, a);
        let cap = n + 1;
        // exp ≥ 0: sig · 2^exp, huge when bits(sig) + exp > cap (bits(sig) = p).
        let zero_e = self.k(0);
        let nonneg = self.slt(&x.exp, &zero_e) ^ 1;
        let big_k = self.k(cap as i64 - f.p as i64);
        let too_big = self.slt(&big_k, &x.exp);
        let amt = self.clamp(&x.exp, cap);
        let wide = cap + f.p + 1;
        let shifted = self.shl(&Self::zext(&x.sig, wide), &amt);
        let mag_hi: Bits = shifted[..cap].to_vec();
        // exp < 0: rounded to an integer.
        let d_s = self.sub(&zero_e, &x.exp);
        let d = self.clamp(&d_s, f.p + 1);
        let mut ext = vec![FALSE; 2];
        ext.extend_from_slice(&x.sig);
        let ext = Self::zext(&ext, f.p + 4);
        let sh = self.shr_jam(&ext, &d);
        let hi: Bits = sh[2..].to_vec();
        let up = self.round_up(rm, x.sign, hi[0], sh[1], sh[0]);
        let mut inc = vec![FALSE; hi.len() + 1];
        inc[0] = up;
        let k = self.add(&Self::zext(&hi, hi.len() + 1), &inc);
        let kw = Self::zext(&k, cap.max(k.len()));
        let k_huge = self.any(&kw[cap..]);
        let k_mag: Bits = Self::zext(&kw, cap);
        let mag = self.mux(nonneg, &mag_hi, &k_mag);
        let huge = self.g.mux(nonneg, too_big, k_huge);
        // Saturation.
        let (maxv, minv) = if signed {
            let mut mx = vec![TRUE; n];
            mx[n - 1] = FALSE;
            let mut mn = vec![FALSE; n];
            mn[n - 1] = TRUE;
            (mx, mn)
        } else {
            (vec![TRUE; n], vec![FALSE; n])
        };
        let limit = if signed { n - 1 } else { n };
        let over_pos = self.any(&mag[limit..]);
        let low: Bits = mag[..n].to_vec();
        let pos = self.mux(over_pos, &maxv, &low);
        // Negative: 0 for a zero magnitude, min for unsigned or past 2^(n−1), else −mag.
        let mag_zero = self.is_zero(&mag);
        let neg_low = blast::neg(self.g, &low);
        let neg_val = if signed {
            // mag > 2^(n−1)?
            let mut half = vec![FALSE; cap];
            half[n - 1] = TRUE;
            let past = blast::ult(self.g, &half, &mag);
            self.mux(past, &minv, &neg_low)
        } else {
            minv.clone()
        };
        let zn = vec![FALSE; n];
        let neg = self.mux(mag_zero, &zn, &neg_val);
        let fin = self.mux(x.sign, &neg, &pos);
        let huge_v = self.mux(x.sign, &minv, &maxv);
        let mut r = self.mux(huge, &huge_v, &fin);
        r = self.mux(x.zero, &zn, &r);
        let inf_v = self.mux(x.sign, &minv, &maxv);
        r = self.mux(x.inf, &inf_v, &r);
        self.mux(x.nan, &zn, &r)
    }
}

/// The bits of floating-point node `i`, from its operands' `kids`.
pub(super) fn blast(b: &mut Blaster<'_>, i: u32, kids: &[Bits]) -> Result<Bits, Error> {
    let d =
        b.cx.fp_desc(i)
            .ok_or_else(|| Error::Unsupported("an operation the prover does not know".into()))?;
    circuit(&mut b.g, d, kids)
}

/// The circuit of the operation `d` over its operands' bits.
pub(crate) fn circuit(g: &mut Aig, d: crate::fp::node::Desc, kids: &[Bits]) -> Result<Bits, Error> {
    let f = F::of(d.format);
    let ew = f.eb + 14 + (usize::BITS - (4 * f.p + 16).leading_zeros()) as usize;
    let mut c = C { g, ew };
    Ok(match d.op {
        FpOp::Add(rm) => c.fadd(f, rm, &kids[0], &kids[1]),
        FpOp::Mul(rm) => c.fmul(f, rm, &kids[0], &kids[1]),
        FpOp::Div(rm) => c.fdiv(f, rm, &kids[0], &kids[1]),
        FpOp::Fma(rm) => c.ffma(f, rm, &kids[0], &kids[1], &kids[2]),
        FpOp::Sqrt(rm) => c.fsqrt(f, rm, &kids[0]),
        FpOp::Rem => c.frem(f, &kids[0], &kids[1])?,
        FpOp::RoundToIntegral(rm) => c.fround(f, rm, &kids[0]),
        FpOp::Min => c.fminmax(f, &kids[0], &kids[1], false),
        FpOp::Max => c.fminmax(f, &kids[0], &kids[1], true),
        FpOp::Eq | FpOp::Lt | FpOp::Le => vec![c.fcmp(f, d.op, &kids[0], &kids[1])],
        FpOp::Convert { to, rm } => {
            let t = F::of(to);
            let ew = ew.max(t.eb + 14 + (usize::BITS - (4 * t.p + 16).leading_zeros()) as usize);
            let mut c = C { g: c.g, ew };
            c.fconvert(f, t, rm, &kids[0])
        }
        FpOp::FromSInt(rm) | FpOp::FromUInt(rm) => {
            let n = kids[0].len();
            let ew = ew.max((usize::BITS - n.leading_zeros()) as usize + 4 + f.eb + 8);
            let mut c = C { g: c.g, ew };
            c.of_int(f, rm, &kids[0], matches!(d.op, FpOp::FromSInt(_)))
        }
        FpOp::ToSInt(rm, w) | FpOp::ToUInt(rm, w) => {
            let n = usize::from(w.bits());
            let ew = ew.max((usize::BITS - n.leading_zeros()) as usize + 4 + f.eb + 8);
            let mut c = C { g: c.g, ew };
            c.int_of(f, rm, &kids[0], n, matches!(d.op, FpOp::ToSInt(..)))
        }
    })
}

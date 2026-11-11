//! Bit-vectors wider than a value of the library holds (512 bits): read as limbs, low first,
//! of [`LIMB`] bits each but the last. The operators that are limb by limb, or a chain of
//! carries, or a choice of limbs, are read, and a division by the schoolbook. Only a solver session reads
//! them: an import lists each declared name with one expression, which a wide one is not.

use super::*;

/// The bits of a limb. A sum of two limbs with its carry, and a product of two, fit a value.
pub(super) const LIMB: u32 = 256;
/// The widest bit-vector read.
pub(super) const MAX_WIDE: u32 = 1 << 16;

/// A wide bit-vector: its limbs, low first, each of [`LIMB`] bits but the last.
#[derive(Clone, Debug)]
pub(in crate::smtlib) struct Wide {
    pub(in crate::smtlib) limbs: Vec<Expr>,
    pub(in crate::smtlib) bits: u32,
}

fn width(n: u32) -> Result<Width, Error> {
    u16::try_from(n)
        .ok()
        .and_then(|n| Width::new(n).ok())
        .ok_or_else(|| Error::Unsupported(format!("a bit-vector of {n} bits")))
}

impl<'a, 's> State<'a, 's> {
    /// The limbs of a bit-vector value of any width (`None` for a value of another sort).
    pub(super) fn wide_of(&mut self, v: Val) -> Result<Option<Wide>, Error> {
        match v {
            Val::Wide(k) => Ok(Some(self.env.wides[k as usize].clone())),
            Val::Bv(e) => {
                let bits = u32::from(self.cx.width(e)?.bits());
                Ok(Some(self.wide_slice(&[e], 0, bits)?))
            }
            _ => Ok(None),
        }
    }

    /// A value of `w`: a bit-vector of the library when it fits one.
    pub(super) fn wide_val(&mut self, w: Wide) -> Result<Val, Error> {
        if w.bits <= 512 {
            let mut acc = w.limbs[0];
            for &l in &w.limbs[1..] {
                acc = self.cx.concat(l, acc)?;
            }
            return Ok(Val::Bv(acc));
        }
        if !self.env.session {
            return Err(Error::Unsupported(
                "a bit-vector above 512 bits outside a solver session".into(),
            ));
        }
        self.env.wides.push(w);
        Ok(Val::Wide(self.env.wides.len() as u32 - 1))
    }

    /// The bits of a wide value (0 for one that is not there).
    pub(super) fn wide_bits(&self, v: Val) -> u32 {
        match v {
            Val::Wide(k) => self.env.wides[k as usize].bits,
            _ => 0,
        }
    }

    /// Bits `[lo, lo + len)` of the pieces (low first, of any widths), as limbs.
    fn wide_slice(&mut self, pieces: &[Expr], lo: u32, len: u32) -> Result<Wide, Error> {
        let mut limbs = Vec::with_capacity(len.div_ceil(LIMB) as usize);
        let (mut pos, end) = (lo, lo + len);
        while pos < end {
            let take = LIMB.min(end - pos);
            let mut limb: Option<Expr> = None;
            let mut base = 0u32;
            for &p in pieces {
                let pw = u32::from(self.cx.width(p)?.bits());
                let (s, e) = (pos.max(base), (pos + take).min(base + pw));
                if s < e {
                    let part = self.cx.extract(p, (s - base) as u16, width(e - s)?)?;
                    limb = Some(match limb {
                        Some(low) => self.cx.concat(part, low)?,
                        None => part,
                    });
                }
                base += pw;
                if base >= pos + take {
                    break;
                }
            }
            limbs.extend(limb);
            pos += take;
        }
        Ok(Wide { limbs, bits: len })
    }

    /// A constant from 64-bit limbs, low first.
    pub(super) fn wide_constant(&mut self, limbs: &[u64], bits: u32) -> Result<Wide, Error> {
        let mut out = Vec::with_capacity(bits.div_ceil(LIMB) as usize);
        let per = (LIMB / 64) as usize;
        for k in 0..bits.div_ceil(LIMB) {
            let w = width(LIMB.min(bits - k * LIMB))?;
            let from = (k as usize * per).min(limbs.len());
            let to = (from + per).min(limbs.len());
            out.push(
                self.cx
                    .constant(&BitVec::wrapping_from_limbs(w, &limbs[from..to]))?,
            );
        }
        Ok(Wide { limbs: out, bits })
    }

    fn wide_fill(&mut self, bit: bool, bits: u32) -> Result<Wide, Error> {
        let limbs = vec![if bit { u64::MAX } else { 0 }; bits.div_ceil(64) as usize];
        self.wide_constant(&limbs, bits)
    }

    /// `hi` above `lo`.
    fn wide_concat(&mut self, hi: &Wide, lo: &Wide) -> Result<Wide, Error> {
        let pieces: Vec<Expr> = lo.limbs.iter().chain(&hi.limbs).copied().collect();
        self.wide_slice(&pieces, 0, hi.bits + lo.bits)
    }

    fn wide_extract(&mut self, a: &Wide, lo: u32, len: u32) -> Result<Wide, Error> {
        self.wide_slice(&a.limbs, lo, len)
    }

    fn wide_zip(&mut self, op: BinOp, a: &Wide, b: &Wide) -> Result<Wide, Error> {
        let mut limbs = Vec::with_capacity(a.limbs.len());
        for (&x, &y) in a.limbs.iter().zip(&b.limbs) {
            limbs.push(self.cx.bin(op, x, y)?);
        }
        Ok(Wide {
            limbs,
            bits: a.bits,
        })
    }

    fn wide_not(&mut self, a: &Wide) -> Result<Wide, Error> {
        let mut limbs = Vec::with_capacity(a.limbs.len());
        for &x in &a.limbs {
            limbs.push(self.cx.un(UnOp::Not, x)?);
        }
        Ok(Wide {
            limbs,
            bits: a.bits,
        })
    }

    /// `a + b + carry` (the carry one bit), limb by limb with the carry between.
    fn wide_add(&mut self, a: &Wide, b: &Wide, carry: Expr) -> Result<Wide, Error> {
        let mut carry = carry;
        let mut limbs = Vec::with_capacity(a.limbs.len());
        for (&x, &y) in a.limbs.iter().zip(&b.limbs) {
            let w = self.cx.width(x)?;
            let wider = width(u32::from(w.bits()) + 1)?;
            let (x, y, c) = (
                self.cx.zext(x, wider)?,
                self.cx.zext(y, wider)?,
                self.cx.zext(carry, wider)?,
            );
            let s = self.cx.bin(BinOp::Add, x, y)?;
            let s = self.cx.bin(BinOp::Add, s, c)?;
            limbs.push(self.cx.extract(s, 0, w)?);
            carry = self.cx.extract(s, w.bits(), Width::W1)?;
        }
        Ok(Wide {
            limbs,
            bits: a.bits,
        })
    }

    fn wide_sub(&mut self, a: &Wide, b: &Wide) -> Result<Wide, Error> {
        let (nb, one) = (self.wide_not(b)?, self.cx.bool(true)?);
        self.wide_add(a, &nb, one)
    }

    fn wide_eq(&mut self, a: &Wide, b: &Wide) -> Result<Expr, Error> {
        let mut acc = self.cx.bool(true)?;
        for (&x, &y) in a.limbs.iter().zip(&b.limbs) {
            let e = self.cx.cmp(CmpOpExt::Eq, x, y)?;
            acc = self.cx.bin(BinOp::And, acc, e)?;
        }
        Ok(acc)
    }

    /// `a <u b`: the highest limbs that differ decide.
    fn wide_ult(&mut self, a: &Wide, b: &Wide) -> Result<Expr, Error> {
        let mut lt = self.cx.bool(false)?;
        for (&x, &y) in a.limbs.iter().zip(&b.limbs) {
            let same = self.cx.cmp(CmpOpExt::Eq, x, y)?;
            let below = self.cx.cmp(CmpOpExt::Ult, x, y)?;
            lt = self.cx.select(same, lt, below)?;
        }
        Ok(lt)
    }

    /// `a` with its sign bit flipped: the signed order of two is the unsigned order of these.
    fn wide_biased(&mut self, a: &Wide) -> Result<Wide, Error> {
        let mut out = a.clone();
        let k = out.limbs.len() - 1;
        let w = self.cx.width(out.limbs[k])?;
        let sign = self.cx.constant(&BitVec::smin(w))?;
        out.limbs[k] = self.cx.bin(BinOp::Xor, out.limbs[k], sign)?;
        Ok(out)
    }

    fn wide_ite(&mut self, c: Expr, a: &Wide, b: &Wide) -> Result<Wide, Error> {
        let mut limbs = Vec::with_capacity(a.limbs.len());
        for (&x, &y) in a.limbs.iter().zip(&b.limbs) {
            limbs.push(self.cx.select(c, x, y)?);
        }
        Ok(Wide {
            limbs,
            bits: a.bits,
        })
    }

    fn wide_sign(&mut self, a: &Wide) -> Result<Expr, Error> {
        let top = a.limbs[a.limbs.len() - 1];
        let w = self.cx.width(top)?.bits();
        self.cx.extract(top, w - 1, Width::W1)
    }

    /// `a` shifted by the constant `k` (`left`, or right with `fill` coming in at the top).
    fn wide_shift_by(&mut self, a: &Wide, k: u32, left: bool, fill: &Wide) -> Result<Wide, Error> {
        if k == 0 {
            return Ok(a.clone());
        }
        if k >= a.bits {
            return Ok(fill.clone());
        }
        let moved = if left {
            self.wide_extract(a, 0, a.bits - k)?
        } else {
            self.wide_extract(a, k, a.bits - k)?
        };
        let rest = self.wide_extract(fill, 0, k)?;
        if left {
            self.wide_concat(&moved, &rest)
        } else {
            self.wide_concat(&rest, &moved)
        }
    }

    /// `a` shifted by `by` (a value of the same width): a stage for each bit of an amount
    /// below the width, and all `fill` for an amount at or above it.
    fn wide_shift(&mut self, a: &Wide, by: &Wide, left: bool, fill: &Wide) -> Result<Wide, Error> {
        let mut acc = a.clone();
        let stages = 32 - (a.bits - 1).leading_zeros();
        for s in 0..stages {
            let bit = self.cx.extract(by.limbs[0], s as u16, Width::W1)?;
            let shifted = self.wide_shift_by(&acc, 1 << s, left, fill)?;
            acc = self.wide_ite(bit, &shifted, &acc)?;
        }
        let n = self.wide_constant(&[u64::from(a.bits)], a.bits)?;
        let within = self.wide_ult(by, &n)?;
        self.wide_ite(within, &acc, fill)
    }

    /// `a * b`: each pair of limbs whose product reaches below the width, added in place.
    fn wide_mul(&mut self, a: &Wide, b: &Wide) -> Result<Wide, Error> {
        let mut acc = self.wide_fill(false, a.bits)?;
        let zero = self.cx.bool(false)?;
        let double = width(2 * LIMB)?;
        for i in 0..a.limbs.len() {
            for j in 0..b.limbs.len() {
                let at = LIMB * (i + j) as u32;
                if at >= a.bits {
                    break;
                }
                let (x, y) = (
                    self.cx.zext(a.limbs[i], double)?,
                    self.cx.zext(b.limbs[j], double)?,
                );
                let p = self.cx.bin(BinOp::Mul, x, y)?;
                // The product at its place: zeros below it, what fits of it, zeros above.
                let mut pieces = Vec::new();
                if at > 0 {
                    pieces.extend(self.wide_fill(false, at)?.limbs);
                }
                pieces.push(p);
                let have = at + 2 * LIMB;
                if have < a.bits {
                    pieces.extend(self.wide_fill(false, a.bits - have)?.limbs);
                }
                let term = self.wide_slice(&pieces, 0, a.bits)?;
                acc = self.wide_add(&acc, &term, zero)?;
            }
        }
        Ok(acc)
    }

    /// `a / b` and `a % b`, unsigned, by the schoolbook: a bit of the quotient at a time, the
    /// divisor taken from the remainder where it fits. For a divisor of zero the quotient is
    /// all ones and the remainder is `a`, as SMT-LIB has them, with nothing said apart.
    fn wide_divide(&mut self, a: &Wide, b: &Wide) -> Result<(Wide, Wide), Error> {
        let n = a.bits;
        // One bit more: the remainder shifted up by a bit may reach twice the divisor.
        let zero = self.cx.bool(false)?;
        let mut divisor = b.limbs.clone();
        divisor.push(zero);
        let divisor = self.wide_slice(&divisor, 0, n + 1)?;
        let mut rest = self.wide_fill(false, n + 1)?;
        let mut quotient = Vec::with_capacity(n as usize);
        for i in (0..n).rev() {
            let bit = self.wide_extract(a, i, 1)?.limbs[0];
            let mut shifted = vec![bit];
            shifted.extend(rest.limbs.iter().copied());
            let shifted = self.wide_slice(&shifted, 0, n + 1)?;
            let below = self.wide_ult(&shifted, &divisor)?;
            let less = self.wide_sub(&shifted, &divisor)?;
            rest = self.wide_ite(below, &shifted, &less)?;
            quotient.push(self.cx.un(UnOp::Not, below)?);
        }
        quotient.reverse();
        let quotient = self.wide_slice(&quotient, 0, n)?;
        let rest = self.wide_extract(&rest, 0, n)?;
        Ok((quotient, rest))
    }

    fn wide_negated(&mut self, a: &Wide) -> Result<Wide, Error> {
        let zero = self.wide_fill(false, a.bits)?;
        self.wide_sub(&zero, a)
    }

    /// A signed division of wide values: by the unsigned one of the magnitudes.
    fn wide_signed(&mut self, op: &str, a: &Wide, b: &Wide) -> Result<Wide, Error> {
        let (sa, sb) = (self.wide_sign(a)?, self.wide_sign(b)?);
        let (na, nb) = (self.wide_negated(a)?, self.wide_negated(b)?);
        let (ma, mb) = (self.wide_ite(sa, &na, a)?, self.wide_ite(sb, &nb, b)?);
        let (q, r) = self.wide_divide(&ma, &mb)?;
        match op {
            "bvsdiv" => {
                // Negative exactly when one of the two is.
                let differ = self.cx.bin(BinOp::Xor, sa, sb)?;
                let nq = self.wide_negated(&q)?;
                self.wide_ite(differ, &nq, &q)
            }
            "bvsrem" => {
                // The sign of the dividend.
                let nr = self.wide_negated(&r)?;
                self.wide_ite(sa, &nr, &r)
            }
            _ => {
                // `bvsmod`: the sign of the divisor, and a remainder of zero is zero.
                let zero = self.wide_fill(false, a.bits)?;
                let none = self.wide_eq(&r, &zero)?;
                let nr = self.wide_negated(&r)?;
                let up = self.wide_sub(b, &r)?;
                let carry = self.cx.bool(false)?;
                let down = self.wide_add(&r, b, carry)?;
                // a >= 0, b >= 0: r;  a < 0, b >= 0: b - r;  a >= 0, b < 0: r + b;  else -r.
                let positive = self.wide_ite(sa, &up, &r)?;
                let negative = self.wide_ite(sa, &nr, &down)?;
                let signed = self.wide_ite(sb, &negative, &positive)?;
                self.wide_ite(none, &r, &signed)
            }
        }
    }

    /// Whether an application is of wide values: an operand is one, or a concatenation makes
    /// one.
    pub(super) fn wide_case(&self, op: &str, args: &[(u32, Val)]) -> Result<bool, Error> {
        if args.iter().any(|&(_, v)| matches!(v, Val::Wide(_))) {
            return Ok(true);
        }
        if op == "concat" {
            let mut total = 0u32;
            for &(_, v) in args {
                if let Val::Bv(e) = v {
                    total += u32::from(self.cx.width(e)?.bits());
                }
            }
            return Ok(total > 512);
        }
        Ok(false)
    }

    /// An operator over wide bit-vectors.
    pub(super) fn apply_wide(
        &mut self,
        sx: &Sx<'s>,
        id: u32,
        op: &str,
        args: &[(u32, Val)],
    ) -> Result<Val, Error> {
        if op == "ite" {
            let [c, t, f] = args else {
                return Err(sx.err(id, "wrong number of operands"));
            };
            let c = self.boolean(sx, c.0, c.1)?;
            let (Some(t), Some(f)) = (self.wide_of(t.1)?, self.wide_of(f.1)?) else {
                return Err(sx.err(id, "ite arms of different sorts"));
            };
            if t.bits != f.bits {
                return Err(sx.err(id, "ite arms of different sorts"));
            }
            let r = self.wide_ite(c, &t, &f)?;
            return self.wide_val(r);
        }
        let mut xs = Vec::with_capacity(args.len());
        for &(a, v) in args {
            let Some(w) = self.wide_of(v)? else {
                return Err(sx.err(a, "expected a bit-vector"));
            };
            xs.push(w);
        }
        if xs.is_empty() {
            return Err(sx.err(id, "wrong number of operands"));
        }
        if op == "concat" {
            // The first operand is the highest.
            let mut acc = xs[xs.len() - 1].clone();
            for x in xs[..xs.len() - 1].iter().rev() {
                if acc.bits + x.bits > MAX_WIDE {
                    return Err(Error::Unsupported(format!(
                        "a bit-vector above {MAX_WIDE} bits"
                    )));
                }
                acc = self.wide_concat(x, &acc)?;
            }
            return self.wide_val(acc);
        }
        if xs.iter().any(|x| x.bits != xs[0].bits) {
            return Err(sx.err(id, "operands of different widths"));
        }
        let arity = |n: usize| {
            if xs.len() == n {
                Ok(())
            } else {
                Err(sx.err(id, "wrong number of operands"))
            }
        };
        let bits = xs[0].bits;
        let value = match op {
            "bvnot" => {
                arity(1)?;
                self.wide_not(&xs[0])?
            }
            "bvneg" => {
                arity(1)?;
                let zero = self.wide_fill(false, bits)?;
                self.wide_sub(&zero, &xs[0])?
            }
            "bvand" | "bvor" | "bvxor" | "bvadd" | "bvmul" => {
                let mut acc = xs[0].clone();
                for x in &xs[1..] {
                    acc = match op {
                        "bvand" => self.wide_zip(BinOp::And, &acc, x)?,
                        "bvor" => self.wide_zip(BinOp::Or, &acc, x)?,
                        "bvxor" => self.wide_zip(BinOp::Xor, &acc, x)?,
                        "bvadd" => {
                            let zero = self.cx.bool(false)?;
                            self.wide_add(&acc, x, zero)?
                        }
                        _ => self.wide_mul(&acc, x)?,
                    };
                }
                acc
            }
            "bvnand" | "bvnor" | "bvxnor" => {
                arity(2)?;
                let inner = match op {
                    "bvnand" => BinOp::And,
                    "bvnor" => BinOp::Or,
                    _ => BinOp::Xor,
                };
                let r = self.wide_zip(inner, &xs[0], &xs[1])?;
                self.wide_not(&r)?
            }
            "bvsub" => {
                arity(2)?;
                self.wide_sub(&xs[0], &xs[1])?
            }
            "bvudiv" | "bvurem" => {
                arity(2)?;
                let (q, r) = self.wide_divide(&xs[0], &xs[1])?;
                if op == "bvudiv" { q } else { r }
            }
            "bvsdiv" | "bvsrem" | "bvsmod" => {
                arity(2)?;
                self.wide_signed(op, &xs[0], &xs[1])?
            }
            "bvshl" | "bvlshr" | "bvashr" => {
                arity(2)?;
                let fill = if op == "bvashr" {
                    let sign = self.wide_sign(&xs[0])?;
                    let (ones, zeros) = (self.wide_fill(true, bits)?, self.wide_fill(false, bits)?);
                    self.wide_ite(sign, &ones, &zeros)?
                } else {
                    self.wide_fill(false, bits)?
                };
                self.wide_shift(&xs[0], &xs[1], op == "bvshl", &fill)?
            }
            "=" | "distinct" | "bvcomp" => {
                if op == "bvcomp" {
                    arity(2)?;
                }
                // `=` chains; `distinct` is pairwise.
                let mut acc = self.cx.bool(true)?;
                for i in 0..xs.len() {
                    let others = if op == "distinct" {
                        i + 1..xs.len()
                    } else {
                        i + 1..(i + 2).min(xs.len())
                    };
                    for j in others {
                        let mut e = self.wide_eq(&xs[i], &xs[j])?;
                        if op == "distinct" {
                            e = self.cx.un(UnOp::Not, e)?;
                        }
                        acc = self.cx.bin(BinOp::And, acc, e)?;
                    }
                }
                return Ok(if op == "bvcomp" {
                    Val::Bv(acc)
                } else {
                    Val::Bool(acc)
                });
            }
            "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
                arity(2)?;
                let (mut a, mut b) = (xs[0].clone(), xs[1].clone());
                if op.starts_with("bvs") {
                    (a, b) = (self.wide_biased(&a)?, self.wide_biased(&b)?);
                }
                // `a > b` is `b < a`, and `a <= b` is not `b < a`.
                let r = match &op[3..] {
                    "lt" => self.wide_ult(&a, &b)?,
                    "gt" => self.wide_ult(&b, &a)?,
                    "le" => {
                        let lt = self.wide_ult(&b, &a)?;
                        self.cx.un(UnOp::Not, lt)?
                    }
                    _ => {
                        let lt = self.wide_ult(&a, &b)?;
                        self.cx.un(UnOp::Not, lt)?
                    }
                };
                return Ok(Val::Bool(r));
            }
            _ => {
                return Err(Error::Unsupported(format!("{op} above 512 bits")));
            }
        };
        self.wide_val(value)
    }

    /// An indexed operator of one wide operand, or one whose result is wide.
    pub(super) fn indexed_wide(
        &mut self,
        sx: &Sx<'s>,
        id: u32,
        op: &str,
        nums: &[u32],
        x: Wide,
    ) -> Result<Val, Error> {
        let w = x.bits;
        let too_wide = || Error::Unsupported(format!("a bit-vector above {MAX_WIDE} bits"));
        let value = match (op, nums) {
            ("extract", &[hi, lo]) => {
                if lo > hi || hi >= w {
                    return Err(sx.err(id, "extract out of range"));
                }
                self.wide_extract(&x, lo, hi - lo + 1)?
            }
            ("zero_extend" | "sign_extend", &[k]) => {
                if k == 0 {
                    x
                } else {
                    if w.saturating_add(k) > MAX_WIDE {
                        return Err(too_wide());
                    }
                    let top = if op == "zero_extend" {
                        self.wide_fill(false, k)?
                    } else {
                        let sign = self.wide_sign(&x)?;
                        let (ones, zeros) = (self.wide_fill(true, k)?, self.wide_fill(false, k)?);
                        self.wide_ite(sign, &ones, &zeros)?
                    };
                    self.wide_concat(&top, &x)?
                }
            }
            ("repeat", &[k]) => {
                if k == 0 {
                    return Err(sx.err(id, "repeat 0"));
                }
                if w.saturating_mul(k) > MAX_WIDE {
                    return Err(too_wide());
                }
                let mut acc = x.clone();
                for _ in 1..k {
                    acc = self.wide_concat(&acc, &x)?;
                }
                acc
            }
            ("rotate_left" | "rotate_right", &[k]) => {
                // A rotation left by `k` is one right by the width less `k`.
                let k = if op == "rotate_left" {
                    (w - k % w) % w
                } else {
                    k % w
                };
                if k == 0 {
                    x
                } else {
                    let (low, high) = (
                        self.wide_extract(&x, 0, k)?,
                        self.wide_extract(&x, k, w - k)?,
                    );
                    self.wide_concat(&low, &high)?
                }
            }
            _ => return Err(Error::Unsupported(format!("{op} above 512 bits"))),
        };
        self.wide_val(value)
    }
}

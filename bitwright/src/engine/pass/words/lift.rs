//! Each node's value as an integer form (see [`super::form`]).

use super::form::{Algebra, Form, FormId, Iv, Over, R, bit_len, max_shift};
use super::int::Int;
use crate::engine::pass::facts;
use crate::engine::{Fin, Runner, Stop};
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;

/// What the facts say of a node of at most 64 bits: bounds of its value and its bits known 0.
#[derive(Clone, Copy)]
struct Known {
    lo: Int,
    hi: Int,
    zero: u128,
}

/// How long a chain of sums an equality is read through.
const MAX_CHAIN: u32 = 48;
/// The widest node read as an integer: wider ones are values of their own.
pub(super) const WORD: u32 = 128;

/// The forms of a call's nodes.
#[derive(Default)]
pub(super) struct Lift {
    pub(super) alg: Algebra,
    forms: IdMap<u32, Form>,
    known: IdMap<u32, Known>,
    /// What the facts read so far relied on, and whether a cap cut one short.
    pub(super) fin: Option<Fin>,
    /// Forms that are an unsigned comparison `−floor(D / 2^k)`, with `D` and `k`.
    less: IdMap<FormId, (Form, u32)>,
    /// Forms that are `[G = 0]`, with `G`, and `k` such that `|G| < 2^k`.
    zero: IdMap<FormId, (Form, u32)>,
    /// Forms that are `[E = −1]·C` for a `C` that is 0 or 1, with `E`, `C` and `k`.
    carry: IdMap<FormId, (Form, Form, u32)>,
}

fn mask(w: u32) -> Int {
    (Int::ONE << w) - 1
}

impl Lift {
    /// Reads the facts of node `n` (of at most 64 bits), once.
    pub(super) fn learn(
        &mut self,
        r: &mut Runner<'_, '_>,
        cx: &mut Context,
        n: u32,
    ) -> Result<(), Stop> {
        let w = u32::from(cx.node(n).width);
        if w > WORD || self.known.contains_key(&n) {
            return Ok(());
        }
        let full = mask(w);
        let mut k = Known {
            lo: Int::from(0),
            hi: full,
            zero: 0,
        };
        let (f, fin) = facts(r, cx, n)?;
        self.fin = Some(self.fin.map_or(fin, |x| x.and(fin)));
        if let Some(f) = f {
            let u = f.urange();
            let limbs = f.known().known_zero();
            let limbs = limbs.limbs();
            let zero = u128::from(limbs[0]) | u128::from(limbs.get(1).copied().unwrap_or(0)) << 64;
            if let (Some(lo), Some(hi)) = (u.lo().to_u128(), u.hi().to_u128())
                && lo <= hi
            {
                k = Known {
                    lo: Int::from(lo),
                    hi: Int::from(hi).min(full & !Int::from(zero)),
                    zero,
                };
                if k.hi < k.lo {
                    k.lo = k.hi;
                }
            }
        }
        self.known.insert(n, k);
        Ok(())
    }

    fn known(&self, cx: &Context, n: u32) -> Option<Known> {
        self.known.get(&n).copied().or_else(|| {
            let w = u32::from(cx.node(n).width);
            (w <= WORD).then(|| Known {
                lo: Int::from(0),
                hi: mask(w),
                zero: 0,
            })
        })
    }

    /// Bounds of node `n`'s value.
    fn range(&self, cx: &Context, n: u32) -> Option<Iv> {
        self.known(cx, n).map(|k| Iv::new(k.lo, k.hi))
    }

    fn leaf(&mut self, cx: &Context, n: u32) -> R<Form> {
        let iv = self.range(cx, n).unwrap_or(Iv {
            lo: Some(Int::from(0)),
            hi: None,
        });
        self.alg.leaf(n, cx.meta[n as usize].shash, iv)
    }

    /// The form of node `n`, read before (see [`read`](Self::read)); a node not read is the
    /// atom it is.
    pub(super) fn value(&mut self, cx: &Context, n: u32) -> R<Form> {
        match self.forms.get(&n) {
            Some(f) => Ok(f.clone()),
            None => self.leaf(cx, n),
        }
    }

    pub(super) fn has(&self, n: u32) -> bool {
        self.forms.contains_key(&n)
    }

    /// Reads node `n`, whose operands were read (or are atoms).
    pub(super) fn read(&mut self, cx: &Context, n: u32) {
        if self.forms.contains_key(&n) {
            return;
        }
        let f = match self.translate(cx, n) {
            Ok(f) => Some(f),
            Err(Over) => self.leaf(cx, n).ok(),
        };
        if let Some(f) = f {
            self.forms.insert(n, f);
        }
    }

    fn translate(&mut self, cx: &Context, n: u32) -> R<Form> {
        let node = cx.node(n);
        let w = u32::from(node.width);
        if w > WORD {
            return self.leaf(cx, n);
        }
        let full = mask(w);
        let konst = |x: u32| cx.const_val(x).and_then(|v| v.to_u128());
        match node.op {
            OpCode::Const => match konst(n) {
                Some(v) => Ok(Form::konst(Int::from(v))),
                None => self.leaf(cx, n),
            },
            OpCode::Zext => self.value(cx, node.a),
            OpCode::Sext => {
                let wa = u32::from(cx.node(node.a).width);
                let a = self.value(cx, node.a)?;
                let sign = self.alg.floor(&a, wa - 1, self.range(cx, node.a))?;
                self.alg.add(&a, &sign, (Int::ONE << w) - (Int::ONE << wa))
            }
            OpCode::Extract => {
                let a = self.value(cx, node.a)?;
                self.alg.slice(&a, node.b, w, self.range(cx, node.a))
            }
            OpCode::Concat => {
                let wl = u32::from(cx.node(node.b).width);
                let (hi, lo) = (self.value(cx, node.a)?, self.value(cx, node.b)?);
                self.alg.add(&lo, &hi, Int::ONE << wl)
            }
            OpCode::Add | OpCode::Sub => {
                let (a, b) = (self.value(cx, node.a)?, self.value(cx, node.b)?);
                let (ra, rb) = (self.range(cx, node.a), self.range(cx, node.b));
                let sub = node.op == OpCode::Sub;
                let d = self
                    .alg
                    .add(&a, &b, if sub { Int::from(-1) } else { Int::from(1) })?;
                let hint = ra
                    .zip(rb)
                    .map(|(x, y)| match (x.lo.zip(x.hi), y.lo.zip(y.hi)) {
                        (Some((xl, xh)), Some((yl, yh))) if sub => Iv::new(xl - yh, xh - yl),
                        (Some((xl, xh)), Some((yl, yh))) => Iv::new(xl + yl, xh + yh),
                        _ => Iv::ALL,
                    });
                self.alg.wrap(&d, w, hint)
            }
            OpCode::Neg => {
                let a = self.value(cx, node.a)?;
                let d = self.alg.scale(&a, Int::from(-1))?;
                let hint = self.known(cx, node.a).map(|k| Iv::new(-k.hi, -k.lo));
                self.alg.wrap(&d, w, hint)
            }
            OpCode::Not => {
                let a = self.value(cx, node.a)?;
                self.alg.add(&Form::konst(full), &a, Int::from(-1))
            }
            OpCode::Mul => {
                let (x, c) = match (konst(node.a), konst(node.b)) {
                    (_, Some(c)) => (node.a, c),
                    (Some(c), None) => (node.b, c),
                    _ => return self.leaf(cx, n),
                };
                let a = self.value(cx, x)?;
                let d = self.alg.scale(&a, Int::from(c))?;
                let hint = self.known(cx, x).and_then(|k| {
                    Some(Iv::new(
                        k.lo.checked_mul(Int::from(c))?,
                        k.hi.checked_mul(Int::from(c))?,
                    ))
                });
                self.alg.wrap(&d, w, hint)
            }
            OpCode::Shl | OpCode::LShr | OpCode::AShr => {
                let Some(k) = konst(node.b) else {
                    return self.leaf(cx, n);
                };
                if k >= u128::from(w) && node.op != OpCode::AShr {
                    return Ok(Form::default());
                }
                let a = self.value(cx, node.a)?;
                let ra = self.range(cx, node.a);
                match node.op {
                    OpCode::Shl => {
                        let k = k as u32;
                        let d = self.alg.scale(&a, Int::ONE << k)?;
                        let hint = self
                            .known(cx, node.a)
                            .map(|x| Iv::new(x.lo << k, x.hi << k));
                        self.alg.wrap(&d, w, hint)
                    }
                    OpCode::LShr => self.alg.floor(&a, k as u32, ra),
                    _ => {
                        // The sign bit fills what the shift leaves.
                        let k = (k.min(u128::from(w) - 1)) as u32;
                        let low = self.alg.floor(&a, k, ra)?;
                        let sign = self.alg.floor(&a, w - 1, ra)?;
                        self.alg
                            .add(&low, &sign, (Int::ONE << w) - (Int::ONE << (w - k)))
                    }
                }
            }
            OpCode::And | OpCode::Or | OpCode::Xor => {
                let (a, b) = (self.value(cx, node.a)?, self.value(cx, node.b)?);
                // (Of values that are 0 or 1 at any width, as of single bits.)
                let bit = |k: Option<Known>| k.is_some_and(|k| k.hi <= 1);
                if w == 1 || (bit(self.known(cx, node.a)) && bit(self.known(cx, node.b))) {
                    return self.gate(node.op, &a, &b);
                }
                if node.op == OpCode::And {
                    return self.alg.band(w, &a, &b);
                }
                // No bit set in both: the sum.
                let apart = matches!(
                    (self.known(cx, node.a), self.known(cx, node.b)),
                    (Some(x), Some(y)) if Int::from(x.zero | y.zero) & full == full
                );
                let sum = self.alg.add(&a, &b, Int::from(1))?;
                if apart {
                    return Ok(sum);
                }
                let and = self.alg.band(w, &a, &b)?;
                self.alg.add(
                    &sum,
                    &and,
                    if node.op == OpCode::Or {
                        Int::from(-1)
                    } else {
                        Int::from(-2)
                    },
                )
            }
            OpCode::Ult | OpCode::Ule | OpCode::Slt | OpCode::Sle | OpCode::Eq | OpCode::Ne => {
                self.compare(cx, node.op, node.a, node.b)
            }
            OpCode::Select => {
                let c = self.value(cx, node.a)?;
                let (a, b) = (self.value(cx, node.b)?, self.value(cx, node.c)?);
                // Two arms a constant apart modulo `2^w` (`x − t` and `x + ~t`, each wrapped
                // on its own): the one plus the constant where the condition holds, wrapped.
                let d = self.alg.add(&a, &b, Int::from(-1))?;
                let apart = self.alg.reduce(&d, w);
                if apart.is_const() && !d.is_const() {
                    let sum = self.alg.add(&b, &c, apart.c)?;
                    return self.alg.wrap(&sum, w, None);
                }
                self.alg.sel(&c, &a, &b)
            }
            _ => self.leaf(cx, n),
        }
    }

    fn compare(&mut self, cx: &Context, op: OpCode, x: u32, y: u32) -> R<Form> {
        let w = u32::from(cx.node(x).width);
        let (Some(kx), Some(ky)) = (self.known(cx, x), self.known(cx, y)) else {
            return Err(Over);
        };
        let (mut fx, mut fy) = (self.value(cx, x)?, self.value(cx, y)?);
        let (mut rx, mut ry) = (Iv::new(kx.lo, kx.hi), Iv::new(ky.lo, ky.hi));
        // Any width both sides fit in decides an unsigned comparison.
        let mut k = bit_len(kx.hi).max(bit_len(ky.hi)).max(1);
        if matches!(op, OpCode::Slt | OpCode::Sle) {
            // The sign bits flipped: an unsigned comparison at the width.
            k = w;
            let h = Int::ONE << (w - 1);
            let flip = |s: &mut Self, f: &Form, r: Iv| -> R<Form> {
                let g = s.alg.shift(f, h)?;
                s.alg.wrap(
                    &g,
                    w,
                    Some(Iv::new(
                        r.lo.unwrap_or(Int::from(0)) + h,
                        r.hi.unwrap_or(Int::from(0)) + h,
                    )),
                )
            };
            fx = flip(self, &fx, rx)?;
            fy = flip(self, &fy, ry)?;
            rx = Iv::new(Int::from(0), mask(w));
            ry = rx;
        }
        let span = |a: Iv, b: Iv| {
            Iv::new(
                a.lo.unwrap_or(Int::from(0)) - b.hi.unwrap_or(Int::from(0)),
                a.hi.unwrap_or(Int::from(0)) - b.lo.unwrap_or(Int::from(0)),
            )
        };
        match op {
            OpCode::Ult | OpCode::Slt => {
                // [x < y] = −floor((x − y) / 2^k)
                let d = self.alg.add(&fx, &fy, Int::from(-1))?;
                let fl = self.alg.floor(&d, k, Some(span(rx, ry)))?;
                let out = self.alg.scale(&fl, Int::from(-1))?;
                let id = self.alg.intern(&out)?;
                self.less.entry(id).or_insert((d, k));
                Ok(out)
            }
            OpCode::Ule | OpCode::Sle => {
                // [x <= y] = 1 + floor((y − x) / 2^k)
                let d = self.alg.add(&fy, &fx, Int::from(-1))?;
                let fl = self.alg.floor(&d, k, Some(span(ry, rx)))?;
                // (Its complement is `[y < x]`, however that is spelled.)
                let not = self.alg.scale(&fl, Int::from(-1))?;
                let id = self.alg.intern(&not)?;
                self.less.entry(id).or_insert((d, k));
                self.alg.shift(&fl, Int::from(1))
            }
            _ => {
                // Equal when the difference is 0 modulo 2^w. A sum on either side is read
                // without its wrap (it is congruent), and where the difference then lies
                // within (−2^k, 2^k), it is 0 exactly when it is 0 modulo 2^w.
                let (cx_, ix) = self.unwrapped(cx, x, 0)?;
                let (cy_, iy) = self.unwrapped(cx, y, 0)?;
                let d = self.alg.add(&cx_, &cy_, Int::from(-1))?;
                let iv = span(ix, iy).meet(self.alg.interval(&d));
                let top = mask(w);
                let (d, k, iv) = match (iv.lo, iv.hi) {
                    (Some(lo), Some(hi)) if lo >= -top && hi <= top && lo <= hi => {
                        let k = bit_len(hi.max(Int::from(0)))
                            .max(bit_len((-lo).max(Int::from(0))))
                            .max(1);
                        (d, k, iv)
                    }
                    _ => (self.alg.add(&fx, &fy, Int::from(-1))?, w, span(rx, ry)),
                };
                // [d = 0] = floor(d / 2^k) − floor((d − 1) / 2^k)
                let below = self.alg.shift(&d, Int::from(-1))?;
                let a = self.alg.floor(&d, k, Some(iv))?;
                let down = Iv {
                    lo: iv.lo.map(|x| x - 1),
                    hi: iv.hi.map(|x| x - 1),
                };
                let b = self.alg.floor(&below, k, Some(down))?;
                let e = self.alg.add(&a, &b, Int::from(-1))?;
                let id = self.alg.intern(&e)?;
                self.zero.entry(id).or_insert((d, k));
                if op == OpCode::Eq {
                    Ok(e)
                } else {
                    self.alg.add(&Form::konst(Int::from(1)), &e, Int::from(-1))
                }
            }
        }
    }

    /// A form congruent to node `n` modulo `2^w`, and bounds of it: sums, differences and
    /// negations left unwrapped.
    fn unwrapped(&mut self, cx: &Context, n: u32, depth: u32) -> R<(Form, Iv)> {
        let node = cx.node(n);
        let top = mask(u32::from(node.width).min(max_shift()));
        let plain = |s: &mut Self| -> R<(Form, Iv)> {
            let iv = s.range(cx, n).ok_or(Over)?;
            Ok((s.value(cx, n)?, iv))
        };
        if depth >= MAX_CHAIN || u32::from(node.width) > WORD {
            return plain(self);
        }
        let out = match node.op {
            OpCode::Add | OpCode::Sub => {
                let (a, ia) = self.unwrapped(cx, node.a, depth + 1)?;
                let (b, ib) = self.unwrapped(cx, node.b, depth + 1)?;
                let sub = node.op == OpCode::Sub;
                let f = self
                    .alg
                    .add(&a, &b, if sub { Int::from(-1) } else { Int::from(1) })?;
                let (Some(al), Some(ah), Some(bl), Some(bh)) = (ia.lo, ia.hi, ib.lo, ib.hi) else {
                    return plain(self);
                };
                let iv = if sub {
                    Iv::new(al - bh, ah - bl)
                } else {
                    Iv::new(al + bl, ah + bh)
                };
                (f, iv)
            }
            OpCode::Neg => {
                let (a, ia) = self.unwrapped(cx, node.a, depth + 1)?;
                let (Some(al), Some(ah)) = (ia.lo, ia.hi) else {
                    return plain(self);
                };
                (self.alg.scale(&a, Int::from(-1))?, Iv::new(-ah, -al))
            }
            _ => return plain(self),
        };
        if out.1.within(-top, top) {
            Ok(out)
        } else {
            plain(self)
        }
    }

    /// `u op v` for values that are 0 or 1.
    fn gate(&mut self, op: OpCode, u: &Form, v: &Form) -> R<Form> {
        let and = |s: &mut Self| s.alg.band(1, u, v);
        match op {
            OpCode::And => {
                let mut out = and(self)?;
                // `[G = 0]·c` is the carry of `(G − 1) + c` out of k bits: `floor((G − 1 + c) /
                // 2^k) − floor((G − 1) / 2^k)`.
                for (p, c) in [(u, v), (v, u)] {
                    let id = self.alg.intern(p)?;
                    let Some((g, k)) = self.zero.get(&id).cloned() else {
                        continue;
                    };
                    let e = self.alg.shift(&g, Int::from(-1))?;
                    if k <= 32 {
                        let with = self.alg.add(&e, c, Int::from(1))?;
                        let a = self.alg.floor(&with, k, None)?;
                        let b = self.alg.floor(&e, k, None)?;
                        out = self.alg.add(&a, &b, Int::from(-1))?;
                    }
                    let id = self.alg.intern(&out)?;
                    self.carry.entry(id).or_insert((e, c.clone(), k));
                    break;
                }
                Ok(out)
            }
            OpCode::Or => {
                if let Some(sum) = self.apart(u, v)? {
                    return Ok(sum);
                }
                let sum = self.alg.add(u, v, Int::from(1))?;
                let both = and(self)?;
                self.alg.add(&sum, &both, Int::from(-1))
            }
            _ => {
                let sum = self.alg.add(u, v, Int::from(1))?;
                let both = and(self)?;
                self.alg.add(&sum, &both, Int::from(-2))
            }
        }
    }

    /// Whether `a − b` is 0 modulo `2^k`, coefficient by coefficient.
    fn congruent(&mut self, a: &Form, b: &Form, k: u32) -> R<bool> {
        let d = self.alg.add(a, b, Int::from(-1))?;
        let d = self.alg.reduce(&d, k);
        Ok(d.is_const() && d.c == 0)
    }

    /// `u + v` when the two (each 0 or 1) are never both 1, so that it is `u | v`.
    fn apart(&mut self, u: &Form, v: &Form) -> R<Option<Form>> {
        let sum = self.alg.add(u, v, Int::from(1))?;
        for (a, b) in [(u, v), (v, u)] {
            let ia = self.alg.intern(a)?;
            let Some((d, k)) = self.less.get(&ia).cloned() else {
                continue;
            };
            let ib = self.alg.intern(b)?;
            // `a` is `[x < y]` with `d = x − y` and `|d| < 2^k`. `b` is 1 only where a form
            // congruent to `d` modulo `2^k` is 0: there `d` is 0, and `a` is 0.
            if let Some((e, c, ki)) = self.carry.get(&ib).cloned() {
                // `b` is `[e = −1]·c`, the carry of `e + c` out of `ki` bits; and as well that
                // of `e' + c` for `e' = −e − 2`, which is −1 where `e` is (the borrow of a
                // difference with a borrow in: the digit taken away all ones, and the borrow).
                // (Written as the one the high digits meet.)
                let other = self
                    .alg
                    .scale(&e, Int::from(-1))
                    .and_then(|x| self.alg.shift(&x, Int::from(-2)))?;
                for e in [e, other] {
                    let with = self.alg.add(&e, &c, Int::from(1))?;
                    if self.congruent(&d, &with, k)? {
                        let up = self.alg.floor(&with, ki, None)?;
                        let base = self.alg.floor(&e, ki, None)?;
                        let carry = self.alg.add(&up, &base, Int::from(-1))?;
                        return Ok(Some(self.alg.add(a, &carry, Int::from(1))?));
                    }
                }
            }
            if let Some((g, kg)) = self.zero.get(&ib).cloned() {
                let neg = self.alg.scale(&g, Int::from(-1))?;
                if self.congruent(&d, &g, k)? || self.congruent(&d, &neg, k)? {
                    // Where `g` is as small as `d`, the two are 0 together and the sum is
                    // `[d <= 0]`: its complement is `[−d < 0]`, however that is spelled.
                    if kg <= k {
                        let not = self
                            .alg
                            .add(&Form::konst(Int::from(1)), &sum, Int::from(-1))?;
                        let id = self.alg.intern(&not)?;
                        let back = self.alg.scale(&d, Int::from(-1))?;
                        self.less.entry(id).or_insert((back, k));
                    }
                    return Ok(Some(sum));
                }
            }
        }
        Ok(self
            .alg
            .interval(&sum)
            .within(Int::from(0), Int::from(1))
            .then_some(sum))
    }
}

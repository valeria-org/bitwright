//! Each node's value as an integer form (see [`super::form`]).

use super::form::{Algebra, Form, FormId, Iv, MAX_SHIFT, Over, R, bit_len};
use crate::engine::pass::facts;
use crate::engine::{Fin, Runner, Stop};
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;

/// What the facts say of a node of at most 64 bits: bounds of its value and its bits known 0.
#[derive(Clone, Copy)]
struct Known {
    lo: i128,
    hi: i128,
    zero: u64,
}

/// How long a chain of sums an equality is read through.
const MAX_CHAIN: u32 = 48;
/// The most nodes of a chain of ANDs or of ORs whose operands are read in one order.
const MAX_LINKS: usize = 256;

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

fn mask(w: u32) -> i128 {
    (1i128 << w) - 1
}

impl Lift {
    /// The forms with XORs as sums without twice the AND (see `Algebra::plain`).
    pub(super) fn plain() -> Self {
        let mut lift = Self::default();
        lift.alg.plain = true;
        lift
    }

    /// The forms with XORs over the values as they are (see `Algebra::values`).
    pub(super) fn values() -> Self {
        let mut lift = Self::default();
        lift.alg.values = true;
        lift
    }

    /// Reads the facts of node `n` (of at most 64 bits), once.
    pub(super) fn learn(
        &mut self,
        r: &mut Runner<'_, '_>,
        cx: &mut Context,
        n: u32,
    ) -> Result<(), Stop> {
        let w = u32::from(cx.node(n).width);
        if w > 64 || self.known.contains_key(&n) {
            return Ok(());
        }
        let full = (u64::MAX >> (64 - w)) as i128;
        let mut k = Known {
            lo: 0,
            hi: full,
            zero: 0,
        };
        let (f, fin) = facts(r, cx, n)?;
        self.fin = Some(self.fin.map_or(fin, |x| x.and(fin)));
        if let Some(f) = f {
            let u = f.urange();
            let zero = f.known().known_zero().limbs()[0];
            if let (Some(lo), Some(hi)) = (u.lo().to_u64(), u.hi().to_u64())
                && lo <= hi
            {
                k = Known {
                    lo: i128::from(lo),
                    hi: i128::from(hi).min(full & !i128::from(zero)),
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
            (w <= 64).then(|| Known {
                lo: 0,
                hi: (u64::MAX >> (64 - w)) as i128,
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
            lo: Some(0),
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
            // The form has the node's value, so the node's bounds.
            if let Some(iv) = self.range(cx, n) {
                self.alg.bound(&f, iv);
            }
            self.forms.insert(n, f);
        }
        // Arithmetic on an XOR is what the plain forms may read better.
        let node = cx.node(n);
        let operands = match node.op {
            _ if self.alg.plain => [None, None],
            OpCode::Add
            | OpCode::Sub
            | OpCode::Mul
            | OpCode::Ult
            | OpCode::Ule
            | OpCode::Slt
            | OpCode::Sle
            | OpCode::Eq
            | OpCode::Ne => [Some(node.a), Some(node.b)],
            OpCode::Neg => [Some(node.a), None],
            _ => [None, None],
        };
        for x in operands.into_iter().flatten() {
            if let Some(f) = self.forms.get(&x) {
                self.alg.mark(f);
            }
        }
    }

    fn translate(&mut self, cx: &Context, n: u32) -> R<Form> {
        let node = cx.node(n);
        let w = u32::from(node.width);
        if w > 64 {
            return self.leaf(cx, n);
        }
        let full = mask(w);
        let konst = |x: u32| cx.const_val(x).and_then(|v| v.to_u64());
        match node.op {
            OpCode::Const => match konst(n) {
                Some(v) => Ok(Form::konst(i128::from(v))),
                None => self.leaf(cx, n),
            },
            OpCode::Zext => self.value(cx, node.a),
            OpCode::Sext => {
                let wa = u32::from(cx.node(node.a).width);
                let a = self.value(cx, node.a)?;
                let sign = self.alg.floor(&a, wa - 1, self.range(cx, node.a))?;
                self.alg.add(&a, &sign, (1i128 << w) - (1i128 << wa))
            }
            OpCode::Extract => {
                let a = self.value(cx, node.a)?;
                self.alg.slice(&a, node.b, w, self.range(cx, node.a))
            }
            OpCode::Concat => {
                let wl = u32::from(cx.node(node.b).width);
                let (hi, lo) = (self.value(cx, node.a)?, self.value(cx, node.b)?);
                self.alg.add(&lo, &hi, 1i128 << wl)
            }
            OpCode::Add | OpCode::Sub => {
                let (a, b) = (self.value(cx, node.a)?, self.value(cx, node.b)?);
                let (ra, rb) = (self.range(cx, node.a), self.range(cx, node.b));
                let sub = node.op == OpCode::Sub;
                let d = self.alg.add(&a, &b, if sub { -1 } else { 1 })?;
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
                let d = self.alg.scale(&a, -1)?;
                let hint = self.known(cx, node.a).map(|k| Iv::new(-k.hi, -k.lo));
                self.alg.wrap(&d, w, hint)
            }
            OpCode::Not => {
                let a = self.value(cx, node.a)?;
                self.alg.add(&Form::konst(full), &a, -1)
            }
            OpCode::Mul => {
                let (x, c) = match (konst(node.a), konst(node.b)) {
                    (_, Some(c)) => (node.a, c),
                    (Some(c), None) => (node.b, c),
                    _ => return self.leaf(cx, n),
                };
                let a = self.value(cx, x)?;
                let d = self.alg.scale(&a, i128::from(c))?;
                let hint = self.known(cx, x).and_then(|k| {
                    Some(Iv::new(
                        k.lo.checked_mul(i128::from(c))?,
                        k.hi.checked_mul(i128::from(c))?,
                    ))
                });
                self.alg.wrap(&d, w, hint)
            }
            OpCode::Shl | OpCode::LShr | OpCode::AShr => {
                let Some(k) = konst(node.b) else {
                    return self.leaf(cx, n);
                };
                if k >= u64::from(w) && node.op != OpCode::AShr {
                    return Ok(Form::default());
                }
                let a = self.value(cx, node.a)?;
                let ra = self.range(cx, node.a);
                match node.op {
                    OpCode::Shl => {
                        let k = k as u32;
                        let d = self.alg.scale(&a, 1i128 << k)?;
                        let hint = self
                            .known(cx, node.a)
                            .map(|x| Iv::new(x.lo << k, x.hi << k));
                        self.alg.wrap(&d, w, hint)
                    }
                    OpCode::LShr => self.alg.floor(&a, k as u32, ra),
                    _ => {
                        // The sign bit fills what the shift leaves.
                        let k = (k.min(u64::from(w) - 1)) as u32;
                        let low = self.alg.floor(&a, k, ra)?;
                        let sign = self.alg.floor(&a, w - 1, ra)?;
                        self.alg.add(&low, &sign, (1i128 << w) - (1i128 << (w - k)))
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
                if !self.alg.plain
                    && node.op != OpCode::Xor
                    && let Some(f) = self.chain(cx, n)?
                {
                    return Ok(f);
                }
                if node.op == OpCode::And {
                    return self.alg.band(w, &a, &b);
                }
                // No bit set in both: the sum.
                let apart = matches!(
                    (self.known(cx, node.a), self.known(cx, node.b)),
                    (Some(x), Some(y)) if (x.zero | y.zero) as i128 & full == full
                );
                if apart {
                    return self.alg.add(&a, &b, 1);
                }
                if node.op == OpCode::Xor {
                    return self.alg.bxor(w, &[a, b]);
                }
                let sum = self.alg.add(&a, &b, 1)?;
                let and = self.alg.band(w, &a, &b)?;
                self.alg.add(&sum, &and, -1)
            }
            OpCode::Ult | OpCode::Ule | OpCode::Slt | OpCode::Sle | OpCode::Eq | OpCode::Ne => {
                self.compare(cx, node.op, node.a, node.b)
            }
            OpCode::Select => {
                let c = self.value(cx, node.a)?;
                let (a, b) = (self.value(cx, node.b)?, self.value(cx, node.c)?);
                // Two arms a constant apart modulo `2^w` (`x − t` and `x + ~t`, each wrapped
                // on its own): the one plus the constant where the condition holds, wrapped.
                let d = self.alg.add(&a, &b, -1)?;
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

    /// Whether node `x` is a link of a chain of `op` at `w` bits: that operation on two
    /// values that are not constants nor single bits, nor, for an OR, without a bit in
    /// common (which is their sum).
    fn link(&self, cx: &Context, x: u32, op: OpCode, w: u32) -> bool {
        let node = cx.node(x);
        if node.op != op || u32::from(node.width) != w || w == 1 {
            return false;
        }
        if cx.const_val(node.a).is_some() || cx.const_val(node.b).is_some() {
            return false;
        }
        let (ka, kb) = (self.known(cx, node.a), self.known(cx, node.b));
        let bit = |k: Option<Known>| k.is_some_and(|k| k.hi <= 1);
        if bit(ka) && bit(kb) {
            return false;
        }
        let full = mask(w);
        !(op == OpCode::Or
            && matches!((ka, kb), (Some(x), Some(y)) if (x.zero | y.zero) as i128 & full == full))
    }

    /// The form of the chain of ANDs or of ORs that ends at `n`, where it has three operands
    /// or more: they are taken in one order (by structure), each once, whatever the order
    /// and the grouping they were written in. (Through the nodes that were read: one that
    /// was not is an operand.)
    fn chain(&mut self, cx: &Context, n: u32) -> R<Option<Form>> {
        let root = cx.node(n);
        let (op, w) = (root.op, u32::from(root.width));
        if !self.link(cx, n, op, w) {
            return Ok(None);
        }
        let mut seen: IdMap<u32, ()> = IdMap::default();
        let mut leaves: Vec<u32> = Vec::new();
        let mut stack = vec![root.b, root.a];
        while let Some(x) = stack.pop() {
            if seen.insert(x, ()).is_some() {
                continue;
            }
            if seen.len() > MAX_LINKS {
                return Ok(None);
            }
            if self.has(x) && self.link(cx, x, op, w) {
                let node = cx.node(x);
                stack.push(node.b);
                stack.push(node.a);
            } else {
                leaves.push(x);
            }
        }
        if leaves.len() < 3 {
            return Ok(None);
        }
        let mut forms = Vec::with_capacity(leaves.len());
        for &x in &leaves {
            let f = self.value(cx, x)?;
            forms.push((self.alg.place(&f)?, f));
        }
        forms.sort_by_key(|x| x.0);
        forms.dedup_by_key(|x| x.0);
        let mut acc = forms[0].1.clone();
        for (_, f) in &forms[1..] {
            let and = self.alg.band(w, &acc, f)?;
            acc = match op {
                OpCode::And => and,
                _ => {
                    let sum = self.alg.add(&acc, f, 1)?;
                    self.alg.add(&sum, &and, -1)?
                }
            };
        }
        self.alg.fork();
        Ok(Some(acc))
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
            let h = 1i128 << (w - 1);
            let flip = |s: &mut Self, f: &Form, r: Iv| -> R<Form> {
                let g = s.alg.shift(f, h)?;
                s.alg.wrap(
                    &g,
                    w,
                    Some(Iv::new(r.lo.unwrap_or(0) + h, r.hi.unwrap_or(0) + h)),
                )
            };
            fx = flip(self, &fx, rx)?;
            fy = flip(self, &fy, ry)?;
            rx = Iv::new(0, mask(w));
            ry = rx;
        }
        let span = |a: Iv, b: Iv| {
            Iv::new(
                a.lo.unwrap_or(0) - b.hi.unwrap_or(0),
                a.hi.unwrap_or(0) - b.lo.unwrap_or(0),
            )
        };
        match op {
            OpCode::Ult | OpCode::Slt => {
                // [x < y] = −floor((x − y) / 2^k)
                let d = self.alg.add(&fx, &fy, -1)?;
                let fl = self.alg.floor(&d, k, Some(span(rx, ry)))?;
                let out = self.alg.scale(&fl, -1)?;
                let id = self.alg.intern(&out)?;
                self.less.entry(id).or_insert((d, k));
                Ok(out)
            }
            OpCode::Ule | OpCode::Sle => {
                // [x <= y] = 1 + floor((y − x) / 2^k)
                let d = self.alg.add(&fy, &fx, -1)?;
                let fl = self.alg.floor(&d, k, Some(span(ry, rx)))?;
                // (Its complement is `[y < x]`, however that is spelled.)
                let not = self.alg.scale(&fl, -1)?;
                let id = self.alg.intern(&not)?;
                self.less.entry(id).or_insert((d, k));
                self.alg.shift(&fl, 1)
            }
            _ => {
                // Equal when the difference is 0 modulo 2^w. A sum on either side is read
                // without its wrap (it is congruent), and where the difference then lies
                // within (−2^k, 2^k), it is 0 exactly when it is 0 modulo 2^w.
                let (cx_, ix) = self.unwrapped(cx, x, 0)?;
                let (cy_, iy) = self.unwrapped(cx, y, 0)?;
                let d = self.alg.add(&cx_, &cy_, -1)?;
                let iv = span(ix, iy).meet(self.alg.interval(&d));
                let top = mask(w);
                let (d, k, iv) = match (iv.lo, iv.hi) {
                    (Some(lo), Some(hi)) if lo >= -top && hi <= top && lo <= hi => {
                        let k = bit_len(hi.max(0)).max(bit_len((-lo).max(0))).max(1);
                        (d, k, iv)
                    }
                    _ => (self.alg.add(&fx, &fy, -1)?, w, span(rx, ry)),
                };
                // [d = 0] = floor(d / 2^k) − floor((d − 1) / 2^k)
                let below = self.alg.shift(&d, -1)?;
                let a = self.alg.floor(&d, k, Some(iv))?;
                let down = Iv {
                    lo: iv.lo.map(|x| x - 1),
                    hi: iv.hi.map(|x| x - 1),
                };
                let b = self.alg.floor(&below, k, Some(down))?;
                let e = self.alg.add(&a, &b, -1)?;
                let id = self.alg.intern(&e)?;
                self.zero.entry(id).or_insert((d, k));
                if op == OpCode::Eq {
                    Ok(e)
                } else {
                    self.alg.add(&Form::konst(1), &e, -1)
                }
            }
        }
    }

    /// A form congruent to node `n` modulo `2^w`, and bounds of it: sums, differences and
    /// negations left unwrapped.
    fn unwrapped(&mut self, cx: &Context, n: u32, depth: u32) -> R<(Form, Iv)> {
        let node = cx.node(n);
        let top = mask(u32::from(node.width).min(MAX_SHIFT));
        let plain = |s: &mut Self| -> R<(Form, Iv)> {
            let iv = s.range(cx, n).ok_or(Over)?;
            Ok((s.value(cx, n)?, iv))
        };
        if depth >= MAX_CHAIN || node.width > 64 {
            return plain(self);
        }
        let out = match node.op {
            OpCode::Add | OpCode::Sub => {
                let (a, ia) = self.unwrapped(cx, node.a, depth + 1)?;
                let (b, ib) = self.unwrapped(cx, node.b, depth + 1)?;
                let sub = node.op == OpCode::Sub;
                let f = self.alg.add(&a, &b, if sub { -1 } else { 1 })?;
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
                (self.alg.scale(&a, -1)?, Iv::new(-ah, -al))
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
                    let e = self.alg.shift(&g, -1)?;
                    if k <= 32 {
                        let with = self.alg.add(&e, c, 1)?;
                        let a = self.alg.floor(&with, k, None)?;
                        let b = self.alg.floor(&e, k, None)?;
                        out = self.alg.add(&a, &b, -1)?;
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
                let sum = self.alg.add(u, v, 1)?;
                let both = and(self)?;
                self.alg.add(&sum, &both, -1)
            }
            _ => {
                let sum = self.alg.add(u, v, 1)?;
                let both = and(self)?;
                self.alg.add(&sum, &both, -2)
            }
        }
    }

    /// Whether `a − b` is 0 modulo `2^k`, coefficient by coefficient.
    fn congruent(&mut self, a: &Form, b: &Form, k: u32) -> R<bool> {
        let d = self.alg.add(a, b, -1)?;
        let d = self.alg.reduce(&d, k);
        Ok(d.is_const() && d.c == 0)
    }

    /// `u + v` when the two (each 0 or 1) are never both 1, so that it is `u | v`.
    fn apart(&mut self, u: &Form, v: &Form) -> R<Option<Form>> {
        let sum = self.alg.add(u, v, 1)?;
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
                    .scale(&e, -1)
                    .and_then(|x| self.alg.shift(&x, -2))?;
                for e in [e, other] {
                    let with = self.alg.add(&e, &c, 1)?;
                    if self.congruent(&d, &with, k)? {
                        let up = self.alg.floor(&with, ki, None)?;
                        let base = self.alg.floor(&e, ki, None)?;
                        let carry = self.alg.add(&up, &base, -1)?;
                        return Ok(Some(self.alg.add(a, &carry, 1)?));
                    }
                }
            }
            if let Some((g, kg)) = self.zero.get(&ib).cloned() {
                let neg = self.alg.scale(&g, -1)?;
                if self.congruent(&d, &g, k)? || self.congruent(&d, &neg, k)? {
                    // Where `g` is as small as `d`, the two are 0 together and the sum is
                    // `[d <= 0]`: its complement is `[−d < 0]`, however that is spelled.
                    if kg <= k {
                        let not = self.alg.add(&Form::konst(1), &sum, -1)?;
                        let id = self.alg.intern(&not)?;
                        let back = self.alg.scale(&d, -1)?;
                        self.less.entry(id).or_insert((back, k));
                    }
                    return Ok(Some(sum));
                }
            }
        }
        Ok(self.alg.interval(&sum).within(0, 1).then_some(sum))
    }
}

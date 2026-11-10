//! Integer forms: `c + Σ kᵢ·aᵢ` over the integers, the atoms being values of the context,
//! `floor(F / 2^k)` of a form, the AND of two forms modulo `2^p`, and a choice between two
//! forms. Every function here is an identity of the integers; see the module above for what
//! they are used for.

use core::cmp::Ordering;

use crate::hash::{IdMap, combine};

pub(super) type AtomId = u32;
pub(super) type FormId = u32;

/// The pass's own bounds were left: a coefficient too large, a form of too many terms, too
/// many atoms. What was being read is then not read (it stays the value it is).
#[derive(Debug)]
pub(super) struct Over;

pub(super) type R<T> = Result<T, Over>;

/// Coefficients stay below this in magnitude.
const BIG: i128 = 1 << 100;
/// The widest shift of a floor, and the most bits of an AND.
pub(super) const MAX_SHIFT: u32 = 96;
/// The most terms of a form.
const MAX_TERMS: usize = 40;
/// The most atoms and forms of a call.
const MAX_ATOMS: usize = 1 << 17;
/// How deep the functions below call one another.
const MAX_DEPTH: u32 = 48;
/// How deep the search for bounds goes, and how many ways it tries at each level.
const BOUND_DEPTH: u8 = 3;

fn ck(c: i128) -> R<i128> {
    if c > -BIG && c < BIG {
        Ok(c)
    } else {
        Err(Over)
    }
}

fn mul(a: i128, b: i128) -> R<i128> {
    a.checked_mul(b).ok_or(Over).and_then(ck)
}

fn plus(a: i128, b: i128) -> R<i128> {
    a.checked_add(b).ok_or(Over).and_then(ck)
}

/// The number of bits of a value that is not negative.
pub(super) fn bit_len(v: i128) -> u32 {
    debug_assert!(v >= 0);
    128 - v.leading_zeros()
}

/// `c + Σ kᵢ·aᵢ`: the terms in the atoms' order, no coefficient zero.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub(super) struct Form {
    pub(super) c: i128,
    pub(super) t: Vec<(AtomId, i128)>,
}

impl Form {
    pub(super) fn konst(c: i128) -> Form {
        Form { c, t: Vec::new() }
    }

    pub(super) fn is_const(&self) -> bool {
        self.t.is_empty()
    }

    /// The atom when the form is one atom (coefficient 1, constant 0).
    pub(super) fn single(&self) -> Option<AtomId> {
        match self.t[..] {
            [(a, 1)] if self.c == 0 => Some(a),
            _ => None,
        }
    }

    pub(super) fn coeff(&self, a: AtomId) -> i128 {
        self.t.iter().find(|x| x.0 == a).map_or(0, |x| x.1)
    }

    /// The form without atom `a`.
    pub(super) fn without(&self, a: AtomId) -> Form {
        Form {
            c: self.c,
            t: self.t.iter().copied().filter(|x| x.0 != a).collect(),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(super) enum Atom {
    /// A node of the context: its value as an unsigned integer.
    Leaf(u32),
    /// `floor(F / 2^k)`.
    Floor(FormId, u8),
    /// `(X mod 2^p) & (Y mod 2^p)`.
    And(u8, FormId, FormId),
    /// `C ? A : B`, with `C` 0 or 1.
    Sel(FormId, FormId, FormId),
}

/// Bounds of a value: `None` is no bound.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) struct Iv {
    pub(super) lo: Option<i128>,
    pub(super) hi: Option<i128>,
}

impl Iv {
    pub(super) const ALL: Iv = Iv { lo: None, hi: None };

    pub(super) fn new(lo: i128, hi: i128) -> Iv {
        Iv {
            lo: Some(lo),
            hi: Some(hi),
        }
    }

    pub(super) fn point(c: i128) -> Iv {
        Iv::new(c, c)
    }

    /// Both bounds hold.
    pub(super) fn meet(self, o: Iv) -> Iv {
        let lo = match (self.lo, o.lo) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (a, b) => a.or(b),
        };
        let hi = match (self.hi, o.hi) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        };
        Iv { lo, hi }
    }

    /// The bounds of either.
    fn hull(self, o: Iv) -> Iv {
        Iv {
            lo: self.lo.zip(o.lo).map(|(a, b)| a.min(b)),
            hi: self.hi.zip(o.hi).map(|(a, b)| a.max(b)),
        }
    }

    fn scaled(self, c: i128) -> Iv {
        let m = |x: Option<i128>| x.and_then(|x| x.checked_mul(c));
        if c >= 0 {
            Iv {
                lo: m(self.lo),
                hi: m(self.hi),
            }
        } else {
            Iv {
                lo: m(self.hi),
                hi: m(self.lo),
            }
        }
    }

    fn plus(self, o: Iv) -> Iv {
        Iv {
            lo: self.lo.zip(o.lo).and_then(|(a, b)| a.checked_add(b)),
            hi: self.hi.zip(o.hi).and_then(|(a, b)| a.checked_add(b)),
        }
    }

    /// Of the floor of the value over `2^k`.
    fn floored(self, k: u32) -> Iv {
        Iv {
            lo: self.lo.map(|x| x >> k),
            hi: self.hi.map(|x| x >> k),
        }
    }

    /// Whether the value is known to lie in `[lo, hi]`.
    pub(super) fn within(self, lo: i128, hi: i128) -> bool {
        self.lo.is_some_and(|x| x >= lo) && self.hi.is_some_and(|x| x <= hi)
    }

    /// The one value, when the bounds meet.
    fn value(self) -> Option<i128> {
        match (self.lo, self.hi) {
            (Some(a), Some(b)) if a == b => Some(a),
            _ => None,
        }
    }

    /// The bits of the value when it is known not to be negative.
    pub(super) fn bits(self) -> Option<u32> {
        match (self.lo, self.hi) {
            (Some(l), Some(h)) if l >= 0 && h >= l => Some(bit_len(h).max(1)),
            _ => None,
        }
    }
}

/// The atoms and forms of a call.
#[derive(Default)]
pub(super) struct Algebra {
    atoms: Vec<Atom>,
    /// Each atom's place in the order of terms: its kind and its structural hash (which does
    /// not depend on node indices).
    key: Vec<(u8, u64)>,
    bounds: Vec<Iv>,
    ids: IdMap<Atom, AtomId>,
    forms: Vec<Form>,
    hashes: Vec<u64>,
    form_ids: IdMap<Form, FormId>,
    /// Bounds of forms found, with the depth of the search they were found at.
    found: IdMap<Form, (Iv, u8)>,
    depth: u32,
    /// Terms handled, for the meter.
    pub(super) work: u64,
}

impl Algebra {
    pub(super) fn atom(&self, a: AtomId) -> Atom {
        self.atoms[a as usize]
    }

    pub(super) fn form(&self, f: FormId) -> &Form {
        &self.forms[f as usize]
    }

    pub(super) fn bounds(&self, a: AtomId) -> Iv {
        self.bounds[a as usize]
    }

    /// The order of terms: by kind, then by structure; the index only where two hashes meet.
    pub(super) fn order(&self, a: AtomId, b: AtomId) -> Ordering {
        self.key[a as usize]
            .cmp(&self.key[b as usize])
            .then(a.cmp(&b))
    }

    fn hash_of(&self, f: &Form) -> u64 {
        let mut h = combine(0x666f_726d, f.c as u64);
        h = combine(h, (f.c >> 64) as u64);
        for &(a, c) in &f.t {
            h = combine(h, self.key[a as usize].1);
            h = combine(h, c as u64);
            h = combine(h, (c >> 64) as u64);
        }
        h
    }

    pub(super) fn intern(&mut self, f: &Form) -> R<FormId> {
        if let Some(&i) = self.form_ids.get(f) {
            return Ok(i);
        }
        if self.forms.len() >= MAX_ATOMS {
            return Err(Over);
        }
        let i = self.forms.len() as FormId;
        self.hashes.push(self.hash_of(f));
        self.forms.push(f.clone());
        self.form_ids.insert(f.clone(), i);
        Ok(i)
    }

    /// The atom, with `iv` bounds of it (kept beside the ones it has).
    fn make(&mut self, a: Atom, hash: u64, iv: Iv) -> R<AtomId> {
        if let Some(&i) = self.ids.get(&a) {
            let b = &mut self.bounds[i as usize];
            let met = b.meet(iv);
            // (Bounds that cross are of a value that does not occur.)
            if !matches!((met.lo, met.hi), (Some(l), Some(h)) if l > h) {
                *b = met;
            }
            return Ok(i);
        }
        if self.atoms.len() >= MAX_ATOMS {
            return Err(Over);
        }
        let rank = match a {
            Atom::Leaf(_) => 0u8,
            Atom::Sel(..) => 1,
            Atom::And(..) => 2,
            Atom::Floor(..) => 3,
        };
        let i = self.atoms.len() as AtomId;
        self.atoms.push(a);
        self.key.push((rank, hash));
        self.bounds.push(iv);
        self.ids.insert(a, i);
        Ok(i)
    }

    /// The value of node `n` (whose structural hash is `shash`), within `iv`.
    pub(super) fn leaf(&mut self, n: u32, shash: u64, iv: Iv) -> R<Form> {
        let a = self.make(Atom::Leaf(n), combine(0x6c65_6166, shash), iv)?;
        Ok(Form {
            c: 0,
            t: vec![(a, 1)],
        })
    }

    fn one(a: AtomId) -> Form {
        Form {
            c: 0,
            t: vec![(a, 1)],
        }
    }

    /// `x + m·y`.
    pub(super) fn add(&mut self, x: &Form, y: &Form, m: i128) -> R<Form> {
        if m == 0 {
            return Ok(x.clone());
        }
        let mut t = Vec::with_capacity(x.t.len() + y.t.len());
        let (mut i, mut j) = (0, 0);
        while i < x.t.len() || j < y.t.len() {
            let o = if i == x.t.len() {
                Ordering::Greater
            } else if j == y.t.len() {
                Ordering::Less
            } else {
                self.order(x.t[i].0, y.t[j].0)
            };
            match o {
                Ordering::Less => {
                    t.push(x.t[i]);
                    i += 1;
                }
                Ordering::Greater => {
                    t.push((y.t[j].0, mul(y.t[j].1, m)?));
                    j += 1;
                }
                Ordering::Equal => {
                    let c = plus(x.t[i].1, mul(y.t[j].1, m)?)?;
                    if c != 0 {
                        t.push((x.t[i].0, c));
                    }
                    i += 1;
                    j += 1;
                }
            }
        }
        self.work += t.len() as u64 + 1;
        if t.len() > MAX_TERMS {
            return Err(Over);
        }
        Ok(Form {
            c: plus(x.c, mul(y.c, m)?)?,
            t,
        })
    }

    pub(super) fn scale(&mut self, x: &Form, m: i128) -> R<Form> {
        if m == 0 {
            return Ok(Form::default());
        }
        let mut t = Vec::with_capacity(x.t.len());
        for &(a, c) in &x.t {
            t.push((a, mul(c, m)?));
        }
        Ok(Form { c: mul(x.c, m)?, t })
    }

    pub(super) fn shift(&mut self, x: &Form, c: i128) -> R<Form> {
        Ok(Form {
            c: plus(x.c, c)?,
            t: x.t.clone(),
        })
    }

    /// The form with every coefficient the residue modulo `2^p` nearest 0 (`2^(p−1)` itself
    /// stays), and the constant in `[0, 2^p)`: equal to the form modulo `2^p`.
    pub(super) fn reduce(&mut self, f: &Form, p: u32) -> Form {
        if p > MAX_SHIFT {
            return f.clone();
        }
        let m = (1i128 << p) - 1;
        let half = 1i128 << (p - 1);
        let mut t = Vec::with_capacity(f.t.len());
        for &(a, c) in &f.t {
            let mut r = c & m;
            if r > half {
                r -= 1 << p;
            }
            if r != 0 {
                t.push((a, r));
            }
        }
        self.work += f.t.len() as u64 + 1;
        Form { c: f.c & m, t }
    }

    // ----- bounds -----------------------------------------------------------------------

    /// Bounds of the form's value.
    pub(super) fn interval(&mut self, f: &Form) -> Iv {
        self.interval_at(f, 0)
    }

    fn interval_at(&mut self, f: &Form, depth: u8) -> Iv {
        if f.t.is_empty() {
            return Iv::point(f.c);
        }
        if let Some(&(iv, d)) = self.found.get(f)
            && d <= depth
        {
            return iv;
        }
        let iv = self.search(f, depth);
        if self.found.len() >= MAX_ATOMS {
            self.found.clear();
        }
        self.found.insert(f.clone(), (iv, depth));
        iv
    }

    fn search(&mut self, f: &Form, depth: u8) -> Iv {
        let mut iv = Iv::point(f.c);
        for &(a, c) in &f.t {
            iv = iv.plus(self.bounds[a as usize].scaled(c));
        }
        self.work += f.t.len() as u64 + 1;
        if depth >= BOUND_DEPTH || iv.value().is_some() {
            return iv;
        }
        // A bitwise combination: `α·x + β·y + γ·(x & y)` takes, bit by bit, one of the values
        // 0, α, β and α + β + γ times the bit's weight.
        let mut tried = 0;
        for &(m, g) in &f.t {
            let Atom::And(p, xi, yi) = self.atom(m) else {
                continue;
            };
            // (An operand is read by its low `p` bits: an atom that is wider, as those.)
            let top = (1i128 << p) - 1;
            let mut ops = [self.form(xi).clone(), self.form(yi).clone()];
            let mut ivs = [Iv::point(0); 2];
            for (z, iz) in ops.iter_mut().zip(&mut ivs) {
                *iz = self.interval_at(z, depth + 1);
                if !iz.within(0, top)
                    && z.single().is_some()
                    && depth + 1 < BOUND_DEPTH
                    && let Ok(low) = self.wrap(z, u32::from(p), None)
                {
                    *iz = self.interval_at(&low, depth + 1);
                    *z = low;
                }
            }
            let [x, y] = ops;
            let [ix, iy] = ivs;
            if !ix.within(0, top) || !iy.within(0, top) {
                continue;
            }
            tried += 1;
            if tried > 2 {
                break;
            }
            let lead = |z: &Form| match z.t.first() {
                Some(&(a0, z0)) => {
                    let c = f.coeff(a0);
                    if c % z0 == 0 { c / z0 } else { 0 }
                }
                None => 0,
            };
            let half = if g % 2 == 0 { -(g / 2) } else { 0 };
            let mut cands = [(lead(&x), lead(&y)), (-g, -g), (half, half)];
            cands.sort_unstable();
            for (k, &(al, be)) in cands.iter().enumerate() {
                if k > 0 && cands[k - 1] == (al, be) {
                    continue;
                }
                let Ok(rest) = self.add(f, &x, -al).and_then(|r| self.add(&r, &y, -be)) else {
                    continue;
                };
                let rest = rest.without(m);
                if rest.t.len() >= f.t.len() {
                    continue;
                }
                let ir = self.interval_at(&rest, depth + 1);
                let (xh, yh) = (ix.hi.unwrap_or(0), iy.hi.unwrap_or(0));
                let bits = bit_len(xh).max(bit_len(yh));
                let (mut lo, mut hi) = (Some(0i128), Some(0i128));
                for i in 0..bits {
                    // The bit of a constant is the bit it has; one above the value's highest
                    // is 0.
                    let of = |z: &Form, zh: i128| -> (i128, i128) {
                        if z.is_const() {
                            let b = (z.c >> i) & 1;
                            (b, b)
                        } else if bit_len(zh) <= i {
                            (0, 0)
                        } else {
                            (0, 1)
                        }
                    };
                    let ((x0, x1), (y0, y1)) = (of(&x, xh), of(&y, yh));
                    let (mut least, mut most) = (i128::MAX, i128::MIN);
                    for xb in [x0, x1] {
                        for yb in [y0, y1] {
                            let v = al
                                .checked_mul(xb)
                                .zip(be.checked_mul(yb))
                                .and_then(|(a, b)| a.checked_add(b))
                                .and_then(|s| s.checked_add(g * (xb & yb)));
                            match v {
                                Some(v) => {
                                    least = least.min(v);
                                    most = most.max(v);
                                }
                                None => {
                                    least = i128::MIN;
                                    most = i128::MAX;
                                }
                            }
                        }
                    }
                    let at = |acc: Option<i128>, v: i128| {
                        acc.and_then(|a| v.checked_mul(1i128 << i).and_then(|v| a.checked_add(v)))
                    };
                    lo = if least == i128::MIN {
                        None
                    } else {
                        at(lo, least)
                    };
                    hi = if most == i128::MAX {
                        None
                    } else {
                        at(hi, most)
                    };
                }
                iv = iv.meet(ir.plus(Iv { lo, hi }));
            }
        }
        // A remainder: `λ·(R − 2^k·floor(R / 2^k))` lies in `λ·[0, 2^k − 1]`.
        let mut tried = 0;
        for &(a, g) in &f.t {
            let Atom::Floor(ri, k) = self.atom(a) else {
                continue;
            };
            if g % (1i128 << k) != 0 {
                continue;
            }
            let lam = -(g >> k);
            let r = self.form(ri).clone();
            let Ok(rest) = self.add(f, &r, -lam) else {
                continue;
            };
            let rest = rest.without(a);
            tried += 1;
            if tried > 3 {
                break;
            }
            let ir = self.interval_at(&rest, depth + 1);
            let digit = Iv::new(0, (1i128 << k) - 1).scaled(lam);
            iv = iv.meet(ir.plus(digit));
        }
        // A digit: `λ·(floor(R / 2^a) − 2^(b − a)·floor(R / 2^b))` lies in `λ·[0, 2^(b − a) − 1]`.
        let mut tried = 0;
        'digits: for &(hi, g) in &f.t {
            let Atom::Floor(ri, b) = self.atom(hi) else {
                continue;
            };
            for &(lo, _) in &f.t {
                let Atom::Floor(rj, a) = self.atom(lo) else {
                    continue;
                };
                if rj != ri || a >= b || g % (1i128 << (b - a)) != 0 {
                    continue;
                }
                let lam = -(g >> (b - a));
                let Ok(rest) = self.add(f, &Self::one(lo), -lam) else {
                    continue;
                };
                let rest = rest.without(hi);
                tried += 1;
                if tried > 3 {
                    break 'digits;
                }
                let ir = self.interval_at(&rest, depth + 1);
                let digit = Iv::new(0, (1i128 << (b - a)) - 1).scaled(lam);
                iv = iv.meet(ir.plus(digit));
            }
        }
        iv
    }

    // ----- floor ------------------------------------------------------------------------

    fn enter(&mut self) -> R<()> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(Over);
        }
        Ok(())
    }

    /// `floor(f / 2^k)`; `hint` bounds `f`.
    pub(super) fn floor(&mut self, f: &Form, k: u32, hint: Option<Iv>) -> R<Form> {
        self.enter()?;
        let r = self.floor_in(f, k, hint);
        self.depth -= 1;
        r
    }

    fn floor_in(&mut self, f: &Form, mut k: u32, hint: Option<Iv>) -> R<Form> {
        if k == 0 {
            return Ok(f.clone());
        }
        if k > MAX_SHIFT {
            return Err(Over);
        }
        // floor((E + 2^k·Q) / 2^k) = floor(E / 2^k) + Q: every coefficient leaves its multiple
        // of 2^k outside, and keeps the residue nearest 0.
        let m = (1i128 << k) - 1;
        let half = 1i128 << (k - 1);
        let mut out = Form::konst(f.c >> k);
        let mut rest: Vec<(AtomId, i128)> = Vec::new();
        for &(a, c) in &f.t {
            let (mut q, mut r) = (c >> k, c & m);
            if r > half {
                q += 1;
                r -= 1 << k;
            }
            if q != 0 {
                out.t.push((a, q));
            }
            if r != 0 {
                rest.push((a, r));
            }
        }
        self.work += f.t.len() as u64 + 1;
        if rest.is_empty() {
            return Ok(out);
        }
        let whole = out.t.is_empty();
        let shift = k;
        // floor(2^t·E / 2^k) = floor(E / 2^(k − t)); what of the constant is below 2^t cannot
        // carry.
        let mut rc = f.c & m;
        let t = rest.iter().map(|x| x.1.trailing_zeros()).min().unwrap_or(0);
        if t > 0 {
            for x in &mut rest {
                x.1 >>= t;
            }
            rc >>= t;
            k -= t;
        }
        let r = Form { c: rc, t: rest };
        // floor((−E − 1) / 2^k) = −floor(E / 2^k) − 1: the form whose first atom is positive
        // stays.
        if r.t[0].1 < 0 {
            let e = self.scale(&r, -1)?;
            let e = self.shift(&e, -1)?;
            let neg = self.floor(&e, k, None)?;
            let out = self.shift(&out, -1)?;
            return self.add(&out, &neg, -1);
        }
        let mut iv = self.interval(&r);
        if let Some(h) = hint
            && whole
        {
            // `f` lies in the hint, and `r` is `floor((f − 2^K·q) / 2^t)`.
            let base = out.c.checked_mul(1i128 << shift);
            let of = |x: Option<i128>| {
                x.zip(base)
                    .and_then(|(x, b)| x.checked_sub(b))
                    .map(|x| x >> t)
            };
            iv = iv.meet(Iv {
                lo: of(h.lo),
                hi: of(h.hi),
            });
        }
        let fl = iv.floored(k);
        if let Some(v) = fl.value() {
            return self.shift(&out, v);
        }
        // One atom that takes two values, `l` and `l + 1` (a bit, a carry, a borrow): the
        // floor takes two, and is `v(l) + (v(l + 1) − v(l))·(a − l)`.
        if let [(a, ra)] = r.t[..]
            && let (Some(l), Some(h)) = (self.bounds(a).lo, self.bounds(a).hi)
            && h == l + 1
        {
            let at = |x: i128| mul(ra, x).and_then(|p| plus(r.c, p)).map(|v| v >> k);
            let (v0, v1) = (at(l)?, at(h)?);
            let d = v1 - v0;
            let out = self.shift(&out, plus(v0, -mul(d, l)?)?)?;
            return self.add(&out, &Self::one(a), d);
        }
        // A floor inside a floor: floor((floor(E / 2^a) + R) / 2^k) = floor((E + 2^a·R) / 2^(a + k)).
        let inner = r.t.iter().find_map(|&(a, c)| match self.atom(a) {
            Atom::Floor(e, ak) if c == 1 => Some((a, e, u32::from(ak))),
            _ => None,
        });
        if let Some((a, e, ak)) = inner {
            let e = self.form(e).clone();
            let others = r.without(a);
            let g = self.add(&e, &others, 1i128 << ak)?;
            let fl = self.floor(&g, ak + k, None)?;
            return self.add(&out, &fl, 1);
        }
        // The floor of an AND with a constant is the AND of the floor.
        if let Some(a) = r.single()
            && let Atom::And(q, xi, yi) = self.atom(a)
        {
            let (x, y) = (self.form(xi).clone(), self.form(yi).clone());
            let (x, y) = if x.is_const() { (y, x) } else { (x, y) };
            if y.is_const() {
                let q = u32::from(q);
                if q <= k {
                    return Ok(out);
                }
                let fx = self.floor(&x, k, None)?;
                let and = self.band(q - k, &fx, &Form::konst(y.c >> k))?;
                return self.add(&out, &and, 1);
            }
        }
        let ri = self.intern(&r)?;
        let hash = combine(combine(0x666c_6f6f, self.hashes[ri as usize]), u64::from(k));
        let a = self.make(Atom::Floor(ri, k as u8), hash, fl)?;
        self.add(&out, &Self::one(a), 1)
    }

    /// Bits `[lo, lo + len)` of `f`: `floor(f / 2^lo) − 2^len·floor(f / 2^(lo + len))`.
    pub(super) fn slice(&mut self, f: &Form, lo: u32, len: u32, hint: Option<Iv>) -> R<Form> {
        if len > MAX_SHIFT {
            return Err(Over);
        }
        let a = self.floor(f, lo, hint)?;
        let b = self.floor(f, lo + len, hint)?;
        self.add(&a, &b, -(1i128 << len))
    }

    /// `f` modulo `2^w`: `f − 2^w·floor(f / 2^w)`.
    pub(super) fn wrap(&mut self, f: &Form, w: u32, hint: Option<Iv>) -> R<Form> {
        if w > MAX_SHIFT {
            return Err(Over);
        }
        let fl = self.floor(f, w, hint)?;
        self.add(f, &fl, -(1i128 << w))
    }

    // ----- and --------------------------------------------------------------------------

    /// Each way `f` is `floor(E / 2^k)`: `Q + floor(R / 2^k)` is `floor((R + 2^k·Q) / 2^k)`.
    fn as_floors(&mut self, f: &Form) -> R<Vec<(u32, Form)>> {
        let mut out: Vec<(u32, Form)> = Vec::new();
        for &(a, c) in &f.t {
            if c != 1 {
                continue;
            }
            let Atom::Floor(ri, k) = self.atom(a) else {
                continue;
            };
            let k = u32::from(k);
            if out.iter().any(|x| x.0 == k) {
                continue;
            }
            let r = self.form(ri).clone();
            let q = f.without(a);
            let Ok(e) = self.add(&r, &q, 1i128 << k) else {
                continue;
            };
            out.push((k, e));
        }
        Ok(out)
    }

    /// `(x mod 2^p) & (y mod 2^p)`.
    pub(super) fn band(&mut self, p: u32, x: &Form, y: &Form) -> R<Form> {
        self.enter()?;
        let r = self.band_in(p, x, y);
        self.depth -= 1;
        r
    }

    fn band_in(&mut self, p: u32, x: &Form, y: &Form) -> R<Form> {
        if p == 0 {
            return Ok(Form::default());
        }
        if p > MAX_SHIFT {
            return Err(Over);
        }
        let (mut x, mut y) = (self.reduce(x, p), self.reduce(y, p));
        if x.is_const() && y.is_const() {
            return Ok(Form::konst(x.c & y.c));
        }
        if x.is_const() {
            core::mem::swap(&mut x, &mut y);
        }
        if y.is_const() {
            let c = y.c;
            if c == 0 {
                return Ok(Form::default());
            }
            // One run of bits: a slice.
            let lo = c.trailing_zeros();
            let run = c >> lo;
            if run & (run + 1) == 0 {
                let s = self.slice(&x, lo, bit_len(run), None)?;
                return self.scale(&s, 1i128 << lo);
            }
        }
        if x == y {
            return self.wrap(&x, p, None);
        }
        // An operand below 2^q makes the AND one modulo 2^q.
        let (ix, iy) = (self.interval(&x), self.interval(&y));
        let q = [ix, iy].iter().filter_map(|i| i.bits()).fold(p, u32::min);
        if q < p {
            return self.band(q, &x, &y);
        }
        // Both the same floor of two forms: the floor of the AND.
        if !y.is_const() {
            let (fx, fy) = (self.as_floors(&x)?, self.as_floors(&y)?);
            let common = fx
                .iter()
                .filter_map(|(k, ex)| fy.iter().find(|f| f.0 == *k).map(|f| (*k, ex, &f.1)))
                .max_by_key(|c| c.0);
            if let Some((k, ex, ey)) = common {
                let and = self.band(p + k, ex, ey)?;
                return self.floor(&and, k, None);
            }
        }
        let (xi, yi) = (self.intern(&x)?, self.intern(&y)?);
        let (hx, hy) = (self.hashes[xi as usize], self.hashes[yi as usize]);
        let (xi, yi, hx, hy) = if (hy, yi) < (hx, xi) {
            (yi, xi, hy, hx)
        } else {
            (xi, yi, hx, hy)
        };
        let mut hi = (1i128 << p) - 1;
        for i in [ix, iy] {
            if let (Some(l), Some(h)) = (i.lo, i.hi)
                && l >= 0
            {
                hi = hi.min(h);
            }
        }
        let hash = combine(combine(combine(0x0061_6e64, u64::from(p)), hx), hy);
        let a = self.make(Atom::And(p as u8, xi, yi), hash, Iv::new(0, hi))?;
        Ok(Self::one(a))
    }

    // ----- choice -----------------------------------------------------------------------

    /// `(E, k, len)` when `f` is `floor(E / 2^k)` (`len` none) or the slice `floor(E / 2^k) −
    /// 2^len·floor(E / 2^(k + len))` (with `k = 0`: `E − 2^len·floor(E / 2^len)`, the low
    /// `len` bits of `E`); `E` none for the form 0, which is either of 0.
    fn shape(&mut self, f: &Form) -> Option<(Option<Form>, u32, Option<u32>)> {
        if f.is_const() {
            return (f.c == 0).then_some((None, 0, None));
        }
        if f.c == 0 {
            match f.t[..] {
                [(a, 1)] => {
                    if let Atom::Floor(e, k) = self.atom(a) {
                        return Some((Some(self.form(e).clone()), u32::from(k), None));
                    }
                }
                [(a, ca), (b, cb)] => {
                    let ((a, ca), (b, cb)) = if ca == 1 {
                        ((a, ca), (b, cb))
                    } else {
                        ((b, cb), (a, ca))
                    };
                    if let (Atom::Floor(ea, ka), Atom::Floor(eb, kb)) = (self.atom(a), self.atom(b))
                        && ca == 1
                        && ea == eb
                        && kb > ka
                    {
                        let len = u32::from(kb - ka);
                        if cb == -(1i128 << len) {
                            return Some((Some(self.form(ea).clone()), u32::from(ka), Some(len)));
                        }
                    }
                }
                _ => {}
            }
        }
        // The low bits of the rest: `G − 2^len·floor(G / 2^len)`.
        for i in 0..f.t.len() {
            let (a, c) = f.t[i];
            let Atom::Floor(_, k) = self.atom(a) else {
                continue;
            };
            let len = u32::from(k);
            if c != -(1i128 << len) {
                continue;
            }
            let g = f.without(a);
            if self.floor(&g, len, None).ok().and_then(|fl| fl.single()) == Some(a) {
                return Some((Some(g), 0, Some(len)));
            }
        }
        None
    }

    /// `c ? a : b`, for `c` that is 0 or 1.
    pub(super) fn sel(&mut self, c: &Form, a: &Form, b: &Form) -> R<Form> {
        self.enter()?;
        let r = self.sel_in(c, a, b);
        self.depth -= 1;
        r
    }

    fn sel_in(&mut self, c: &Form, a: &Form, b: &Form) -> R<Form> {
        if c.is_const() {
            return Ok(if c.c != 0 { a.clone() } else { b.clone() });
        }
        if a == b {
            return Ok(a.clone());
        }
        let d = self.add(a, b, -1)?;
        if d.is_const() {
            return self.add(b, c, d.c);
        }
        // The same floor, or the same slice, of the two arms: of the choice between them. One
        // taken from higher up than the other is taken from where the other is, of a floor
        // (a register chosen between the low half of one and the high half of another).
        if let (Some(sa), Some(sb)) = (self.shape(a), self.shape(b))
            && (sa.0.is_some() || sb.0.is_some())
        {
            let k = match (&sa.0, &sb.0) {
                (Some(_), Some(_)) => sa.1.min(sb.1),
                (Some(_), None) => sa.1,
                _ => sb.1,
            };
            // (A floor that is below `2^len` is its own low `len` bits.)
            let len = [&sa, &sb].iter().find_map(|s| s.0.as_ref().and(s.2));
            let (ia, ib) = (self.interval(a), self.interval(b));
            let fits = |s: &(Option<Form>, u32, Option<u32>), iv: Iv| {
                s.0.is_none()
                    || s.2 == len
                    || (s.2.is_none() && len.is_some_and(|l| iv.within(0, (1i128 << l) - 1)))
            };
            let (fa, fb) = (fits(&sa, ia), fits(&sb, ib));
            if (k > 0 || len.is_some()) && fa && fb {
                let mut arms = [Form::default(), Form::default()];
                for (arm, s) in arms.iter_mut().zip([sa, sb]) {
                    *arm = match s.0 {
                        None => Form::default(),
                        Some(e) if s.1 == k => e,
                        Some(e) => self.floor(&e, s.1 - k, None)?,
                    };
                }
                let s = self.sel(c, &arms[0], &arms[1])?;
                return match len {
                    None => self.floor(&s, k, None),
                    Some(len) => self.slice(&s, k, len, None),
                };
            }
        }
        let iv = self.interval(a).hull(self.interval(b));
        let (ci, ai, bi) = (self.intern(c)?, self.intern(a)?, self.intern(b)?);
        let hash = combine(
            combine(
                combine(0x0073_656c, self.hashes[ci as usize]),
                self.hashes[ai as usize],
            ),
            self.hashes[bi as usize],
        );
        let s = self.make(Atom::Sel(ci, ai, bi), hash, iv)?;
        Ok(Self::one(s))
    }
}

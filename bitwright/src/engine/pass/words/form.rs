//! Integer forms: `c + Σ kᵢ·aᵢ` over the integers, the atoms being values of the context,
//! `floor(F / 2^k)` of a form, the AND of two forms modulo `2^p`, the XOR of any number of
//! forms (values that are not negative, as integers), and a choice between two forms. Every
//! function here is an identity of the integers; see the module above for what they are
//! used for.
//!
//! An [`Algebra`] makes one of three kinds of forms, which differ in what an XOR is (see
//! [`Algebra::plain`] and [`Algebra::values`]): an atom over the words truncations are of, an
//! atom over the values as they are, or the sum `x + y − 2·(x & y)`.

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
/// The most terms of a form; and of a plain one (see `Algebra::plain`): a form with more
/// has the root asked with the plain forms too.
const MAX_TERMS: usize = 256;
const PLAIN_TERMS: usize = 40;
/// The most atoms and forms of a call.
const MAX_ATOMS: usize = 1 << 17;
/// How deep the functions below call one another.
const MAX_DEPTH: u32 = 48;
/// How deep the search for bounds goes, and how many ways it tries at each level.
const BOUND_DEPTH: u8 = 3;
/// The most operands of an XOR.
const MAX_XOR: usize = 256;
/// How many times a form is moved along the relations of its atoms (see `settle`).
const MAX_SETTLE: u32 = 16;

/// The places of the kinds of atoms in the order of terms.
const LEAF: u8 = 0;
const SEL: u8 = 1;
const XOR: u8 = 2;
const AND: u8 = 3;
const FLOOR: u8 = 4;

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
    /// The XOR, as integers, of the operands of a list (see [`Algebra::xor_list`]: values
    /// that are not negative) and of the list's constant; a value of `p` bits. No operand is
    /// such an XOR (its operands are in the list instead), a constant, or there twice.
    Xor(u8, u32),
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
    /// Whether the atom is an AND with a relation to an XOR (see `link`).
    linked: Vec<bool>,
    /// Whether the atom is an XOR, or has one under it.
    xor: Vec<bool>,
    bounds: Vec<Iv>,
    ids: IdMap<Atom, AtomId>,
    forms: Vec<Form>,
    hashes: Vec<u64>,
    form_ids: IdMap<Form, FormId>,
    /// Bounds of forms found, with the depth of the search they were found at.
    found: IdMap<Form, (Iv, u8)>,
    /// Bounds of forms given (see `bound`).
    given: IdMap<Form, Iv>,
    depth: u32,
    /// XORs are sums without twice the AND, as arithmetic on them is read: no XOR atoms, and
    /// no relations (see the module).
    pub(super) plain: bool,
    /// The operands of XORs and of ANDs' relations are the values as they are, not the
    /// words truncations are of (see `rep`): what bitwise code on truncations is read by,
    /// as the words are what arithmetic on them is read by.
    pub(super) values: bool,
    /// Whether the plain forms may read the nodes better: arithmetic was done on an XOR, or
    /// a form was moved along a relation (see `mark` and `settle`).
    forked: bool,
    /// Whether an operand was taken as a word that is not the value (see `values`).
    wordy: bool,
    linking: u32,
    /// Terms handled, for the meter.
    pub(super) work: u64,
    /// The operands of the XOR atoms (in their order: by structure) and their constants.
    lists: Vec<(Vec<FormId>, i128)>,
    list_ids: IdMap<(Vec<FormId>, i128), u32>,
    /// Per AND atom of two bits or more, the values it was first asked of (see `band`): it
    /// is their AND as they are.
    whole: IdMap<AtomId, (Form, Form)>,
    /// Per AND atom, the form `d` with `2·AND = d` and the XOR atom in it, where there are
    /// (see `link` and `settle`).
    rel: IdMap<AtomId, Option<(Form, Option<AtomId>)>>,
    /// Per XOR atom and another atom that begins a part of it (see `split`): the AND atoms
    /// of each such part and the rest of the XOR.
    split: IdMap<(AtomId, AtomId), Vec<AtomId>>,
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

    /// Whether the root is to be asked with the plain forms too (see `plain`).
    pub(super) fn forked(&self) -> bool {
        self.forked
    }

    /// Whether the root is to be asked with the operands as values too (see `values`).
    pub(super) fn wordy(&self) -> bool {
        self.wordy
    }

    /// The forms are other than the plain ones would be (see `forked`).
    pub(super) fn fork(&mut self) {
        self.forked = true;
    }

    /// Where `f` is in an order of forms by structure (and by index where two hashes meet).
    pub(super) fn place(&mut self, f: &Form) -> R<(u64, FormId)> {
        let i = self.intern(f)?;
        Ok((self.hashes[i as usize], i))
    }

    /// Arithmetic was done on `f`: where an XOR is in it, the plain forms may read it better.
    pub(super) fn mark(&mut self, f: &Form) {
        self.forked |= self.xored(f);
    }

    /// Whether an XOR atom is in `f`, or under an atom of it.
    fn xored(&self, f: &Form) -> bool {
        f.t.iter().any(|x| self.xor[x.0 as usize])
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
        let under = |s: &Self, i: FormId| s.xored(&s.forms[i as usize]);
        let (rank, xor) = match a {
            Atom::Leaf(_) => (LEAF, false),
            Atom::Sel(c, x, y) => (SEL, under(self, c) || under(self, x) || under(self, y)),
            Atom::Xor(..) => (XOR, true),
            Atom::And(_, x, y) => (AND, under(self, x) || under(self, y)),
            Atom::Floor(e, _) => (FLOOR, under(self, e)),
        };
        let i = self.atoms.len() as AtomId;
        self.atoms.push(a);
        self.key.push((rank, hash));
        self.linked.push(false);
        self.xor.push(xor);
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
        let f = self.sum(x, y, m)?;
        self.settle(f)
    }

    /// `x + m·y`, as the terms come: for what takes a form apart term by term (the sum is
    /// the same value, and need not be the form [`add`](Self::add) gives).
    pub(super) fn sum(&mut self, x: &Form, y: &Form, m: i128) -> R<Form> {
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
        if t.len() > PLAIN_TERMS {
            if self.plain || t.len() > MAX_TERMS {
                return Err(Over);
            }
            self.forked |= self.linking == 0;
        }
        Ok(Form {
            c: plus(x.c, mul(y.c, m)?)?,
            t,
        })
    }

    pub(super) fn scale(&mut self, x: &Form, m: i128) -> R<Form> {
        let f = self.scaled(x, m)?;
        self.settle(f)
    }

    /// `m·x`, as the terms come.
    fn scaled(&mut self, x: &Form, m: i128) -> R<Form> {
        if m == 0 {
            return Ok(Form::default());
        }
        let mut t = Vec::with_capacity(x.t.len());
        for &(a, c) in &x.t {
            t.push((a, mul(c, m)?));
        }
        Ok(Form { c: mul(x.c, m)?, t })
    }

    // ----- the relation of an AND and an XOR ----------------------------------------------

    /// For the AND atom `a`, the AND of the values `x` and `y`: the form `d` with `2·a = d`,
    /// which is `x + y − (x ^ y)`, and the XOR's atom where it is one. None for single bits
    /// (which stay sums of ANDs), and where the pass's bounds are left.
    fn link(&mut self, a: AtomId) -> Option<(Form, Option<AtomId>)> {
        if self.plain {
            return None;
        }
        if let Some(l) = self.rel.get(&a) {
            return l.clone();
        }
        // (None while it is being made.)
        self.rel.insert(a, None);
        self.linking += 1;
        let l = self.link_of(a);
        self.linking -= 1;
        self.rel.insert(a, l.clone());
        l
    }

    fn link_of(&mut self, a: AtomId) -> Option<(Form, Option<AtomId>)> {
        let (x, y) = self.whole.get(&a)?.clone();
        let xor = self.xor_values(&x, &y).ok()?;
        let s = self.add(&x, &y, 1).ok()?;
        let d = self.add(&s, &xor, -1).ok().filter(|d| d.coeff(a) == 0)?;
        let b = xor
            .single()
            .filter(|&b| matches!(self.atom(b), Atom::Xor(..)));
        Some((d, b))
    }

    fn relation(&mut self, a: AtomId) -> Option<Form> {
        self.link(a).map(|l| l.0)
    }

    /// The values the AND atom `a` (of two bits or more) is the AND of, as they are.
    pub(super) fn whole(&self, a: AtomId) -> Option<&(Form, Form)> {
        self.whole.get(&a)
    }

    /// The XOR of two values that are not negative, as they are.
    fn xor_values(&mut self, x: &Form, y: &Form) -> R<Form> {
        let bits = self.range(x).bits().zip(self.range(y).bits());
        let p = bits.map(|(a, b)| a.max(b)).ok_or(Over)?;
        self.bxor(p, &[x.clone(), y.clone()])
    }

    /// Bounds of the value of `f` as an operand: those found, and those given for it.
    fn range(&mut self, f: &Form) -> Iv {
        let iv = self.interval(f);
        match self.given.get(f) {
            Some(&g) => {
                let met = iv.meet(g);
                // (Bounds that cross are of a value that does not occur.)
                if matches!((met.lo, met.hi), (Some(l), Some(h)) if l > h) {
                    g
                } else {
                    met
                }
            }
            None => iv,
        }
    }

    /// `f` where its value is known to lie in `[0, 2^p)`.
    fn exact(&mut self, f: &Form, p: u32) -> Option<Form> {
        let top = (1i128 << p) - 1;
        if f.is_const() {
            return Some(Form::konst(f.c & top));
        }
        self.range(f).within(0, top).then(|| f.clone())
    }

    /// The value of `f` modulo `2^p`, as a form of a value in `[0, 2^p)`: `f` where it is
    /// one.
    fn modulo(&mut self, f: &Form, p: u32) -> R<Form> {
        if let Some(e) = self.exact(f, p) {
            return Ok(e);
        }
        // (For the relation of an AND alone, nothing is made that was not there.)
        if self.linking > 0 {
            return Err(Over);
        }
        let w = self.wrap(f, p, None)?;
        if self.interval(&w).within(0, (1i128 << p) - 1) {
            Ok(w)
        } else {
            Err(Over)
        }
    }

    /// For the XOR atom `x` and another atom `u` of a form: where `u` is a part of the XOR
    /// (the XOR of some of its operands), or the first term of an operand, the AND atom of
    /// that part and the rest of the XOR.
    fn split(&mut self, x: AtomId, u: AtomId) -> Vec<AtomId> {
        if let Some(s) = self.split.get(&(x, u)) {
            return s.clone();
        }
        self.split.insert((x, u), Vec::new());
        let s = self.split_of(x, u).unwrap_or_default();
        self.split.insert((x, u), s.clone());
        s
    }

    fn split_of(&mut self, x: AtomId, u: AtomId) -> R<Vec<AtomId>> {
        let Atom::Xor(q, li) = self.atom(x) else {
            return Ok(Vec::new());
        };
        let (ops, k) = self.lists[li as usize].clone();
        // The parts `u` begins, each with its constant.
        let mut parts: Vec<(Vec<FormId>, i128)> = Vec::new();
        if let Atom::Xor(_, l2) = self.atom(u) {
            let (inner, k2) = self.lists[l2 as usize].clone();
            if !inner.is_empty() && inner.iter().all(|i| ops.contains(i)) {
                parts.push((inner, k2));
            }
        }
        for &i in &ops {
            if self.form(i).t.first().is_some_and(|t| t.0 == u) {
                parts.push((vec![i], 0));
            }
        }
        let mut out = Vec::new();
        for (part, kp) in parts {
            let (mut pf, mut rest): (Vec<Form>, Vec<Form>) = (Vec::new(), Vec::new());
            for &i in &ops {
                let f = self.form(i).clone();
                if part.contains(&i) {
                    pf.push(f);
                } else {
                    rest.push(f);
                }
            }
            if rest.is_empty() && k == kp {
                continue;
            }
            pf.push(Form::konst(kp));
            rest.push(Form::konst(k ^ kp));
            let p = u32::from(q);
            let (g, h) = (self.bxor(p, &pf)?, self.bxor(p, &rest)?);
            if g.is_const() || h.is_const() && h.c == 0 {
                continue;
            }
            let and = self.band(p, &g, &h)?;
            if let Some(a) = and.single()
                && matches!(self.atom(a), Atom::And(..))
                && !out.contains(&a)
            {
                out.push(a);
            }
        }
        Ok(out)
    }

    /// The form moved along the relations of its atoms to the one of fewest terms.
    ///
    /// An AND `A` of `x` and `y` has `2·A = x + y − (x ^ y)`, so a form and the form with any
    /// multiple of `2·A − x − y + (x ^ y)` added are one value. Of those in which one of the
    /// relation's terms is gone, the one of fewest terms stays, an AND counted as two:
    /// `x + y − 2·(x & y)` is `x ^ y`, `(x ^ y) + 2·(x & y)` is `x + y`, `x + y − (x & y)` is
    /// `(x ^ y) + (x & y)`, and `2·(x & y)` is itself. Where two have as few, the one without
    /// the XOR stays, then the one whose AND has the smaller coefficient. The relations are
    /// those of the ANDs in the form, and of the XORs in it one part of which and the rest
    /// are terms of it (`(x ^ y) − x − y` is `−2·(x & y)`).
    fn settle(&mut self, f: Form) -> R<Form> {
        let related = |s: &Self, f: &Form| {
            f.t.iter()
                .any(|x| s.key[x.0 as usize].0 == XOR || s.linked[x.0 as usize])
        };
        if !related(self, &f) {
            return Ok(f);
        }
        let mut f = f;
        for _ in 0..MAX_SETTLE {
            let mut ands: Vec<AtomId> = Vec::new();
            for i in 0..f.t.len() {
                let a = f.t[i].0;
                match self.key[a as usize].0 {
                    AND if self.linked[a as usize] => ands.push(a),
                    XOR => {
                        for j in 0..f.t.len() {
                            let u = f.t[j].0;
                            if u == a {
                                continue;
                            }
                            for and in self.split(a, u) {
                                if f.coeff(and) == 0 && !ands.contains(&and) {
                                    ands.push(and);
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
            self.work += f.t.len() as u64 + 1;
            let mut moved = None;
            for a in ands {
                let Some(d) = self.relation(a) else {
                    continue;
                };
                if let Some(m) = self.best_move(&f, a, &d)
                    && m != 0
                {
                    moved = Some((a, d, m));
                    break;
                }
            }
            let Some((a, d, m)) = moved else {
                return Ok(f);
            };
            // f − m·(2·a − d)
            let g = self.sum(&f, &Self::one(a), mul(-2, m)?)?;
            f = self.sum(&g, &d, m)?;
            // (Not for the relation of an AND alone.)
            self.forked |= self.linking == 0;
        }
        Ok(f)
    }

    /// Of the forms `f − m·(2·a − d)` in which a term of the relation is gone, the best (see
    /// [`settle`](Self::settle)): its `m`. None when there is none.
    fn best_move(&self, f: &Form, a: AtomId, d: &Form) -> Option<i128> {
        let g = f.coeff(a);
        let cs: Vec<(i128, i128, u8)> =
            d.t.iter()
                .map(|&(t, dt)| (f.coeff(t), dt, self.key[t as usize].0))
                .collect();
        let mut ms: Vec<i128> = Vec::with_capacity(cs.len() + 1);
        if g % 2 == 0 {
            ms.push(g / 2);
        }
        for &(c, dt, _) in &cs {
            if c % dt == 0 {
                ms.push(-(c / dt));
            }
        }
        let mut best: Option<((u32, u32, i128, bool), i128)> = None;
        for m in ms {
            let Some(ga) = m.checked_mul(2).and_then(|x| g.checked_sub(x)) else {
                continue;
            };
            let (mut terms, mut xors, mut over) = (2 * u32::from(ga != 0), 0u32, false);
            for &(c, dt, rank) in &cs {
                match m.checked_mul(dt).and_then(|x| c.checked_add(x)) {
                    Some(0) => {}
                    Some(v) if v > -BIG && v < BIG => {
                        terms += if rank == AND { 2 } else { 1 };
                        xors += u32::from(rank == XOR);
                    }
                    _ => over = true,
                }
            }
            if over || ga <= -BIG || ga >= BIG {
                continue;
            }
            let key = (terms, xors, ga.abs(), ga < 0);
            if best.is_none_or(|b| key < b.0) {
                best = Some((key, m));
            }
        }
        best.map(|b| b.1)
    }

    /// The XOR atom of the values the AND atom `a` is the AND of, where there is one.
    pub(super) fn xor_of(&mut self, a: AtomId) -> Option<AtomId> {
        self.link(a).and_then(|l| l.1)
    }

    /// The value of `f` where each node has the value `leaf` gives (for the tests).
    #[cfg(test)]
    pub(super) fn eval(&self, f: &Form, leaf: &dyn Fn(u32) -> i128) -> i128 {
        let of = |i: FormId| self.eval(self.form(i), leaf);
        let mut v = f.c;
        for &(a, c) in &f.t {
            v += c * match self.atom(a) {
                Atom::Leaf(n) => leaf(n),
                Atom::Floor(ri, k) => of(ri) >> k,
                Atom::And(p, xi, yi) => of(xi) & of(yi) & ((1i128 << p) - 1),
                Atom::Sel(ci, ai, bi) => {
                    if of(ci) != 0 {
                        of(ai)
                    } else {
                        of(bi)
                    }
                }
                // (As they are: an operand out of its bounds would show.)
                Atom::Xor(_, li) => {
                    let (ops, k) = self.xor_list(li);
                    ops.iter().fold(k, |x, &i| x ^ of(i))
                }
            };
        }
        v
    }

    // ----- xor --------------------------------------------------------------------------

    /// The operands and the constant of the XOR atoms' list `li`.
    pub(super) fn xor_list(&self, li: u32) -> (&[FormId], i128) {
        let (ops, k) = &self.lists[li as usize];
        (ops, *k)
    }

    /// The XOR of `ops`, each modulo `2^p`.
    pub(super) fn bxor(&mut self, p: u32, ops: &[Form]) -> R<Form> {
        self.enter()?;
        let r = self.bxor_in(p, ops);
        self.depth -= 1;
        r
    }

    fn bxor_in(&mut self, p: u32, ops: &[Form]) -> R<Form> {
        if p == 0 {
            return Ok(Form::default());
        }
        if p > MAX_SHIFT {
            return Err(Over);
        }
        if p == 1 {
            // (Single bits stay sums of ANDs: see the gates of `lift`.)
            let mut acc = Form::default();
            for o in ops {
                let o = self.wrap(o, 1, None)?;
                let and = self.band(1, &acc, &o)?;
                let sum = self.add(&acc, &o, 1)?;
                acc = self.add(&sum, &and, -2)?;
            }
            return Ok(acc);
        }
        if self.plain {
            // Each with the ones before: the sum without twice the AND.
            let mut acc: Option<Form> = None;
            for o in ops {
                acc = Some(match acc {
                    None => o.clone(),
                    Some(a) => {
                        let sum = self.add(&a, o, 1)?;
                        let and = self.band(p, &a, o)?;
                        self.add(&sum, &and, -2)?
                    }
                });
            }
            return Ok(acc.unwrap_or_default());
        }
        let top = (1i128 << p) - 1;
        // The operands as the values they have modulo `2^p`, the constants apart, and how
        // many bits the XOR has.
        let (mut k, mut neg) = (0i128, false);
        let mut exact: Vec<Form> = Vec::with_capacity(ops.len());
        let mut q = 1;
        for o in ops {
            let mut f = self.modulo(o, p)?;
            // `2^p − 1 − x` is the complement of `x`: the form whose first atom is positive
            // stays.
            if !f.is_const() && f.t[0].1 < 0 {
                let g = self.scaled(&f, -1)?;
                f = self.shift(&g, top)?;
                neg = !neg;
            }
            if f.is_const() {
                k ^= f.c;
                continue;
            }
            q = q.max(self.range(&f).bits().map_or(p, |b| b.min(p)));
            exact.push(f);
        }
        if k == top {
            neg = !neg;
            k = 0;
        }
        q = q.max(bit_len(k));
        let low = (1i128 << q) - 1;
        // An operand is taken without its multiples of `2^q` where that is not negative: the
        // word a truncation is of, as arithmetic takes it (the XOR of the words has the XOR
        // of the truncations in its low `q` bits). The operands of an XOR among them are
        // operands.
        let mut flat: Vec<FormId> = Vec::new();
        for e in exact {
            let r = self.rep(&e, q);
            if let Some(a) = r.single()
                && let Atom::Xor(_, li) = self.atom(a)
            {
                let (inner, ik) = self.lists[li as usize].clone();
                k ^= ik & low;
                flat.extend(inner);
            } else {
                flat.push(self.intern(&r)?);
            }
            if flat.len() > MAX_XOR {
                return Err(Over);
            }
        }
        self.work += flat.len() as u64 + 1;
        flat.sort_unstable_by_key(|&i| (self.hashes[i as usize], i));
        // Each operand once: two of one cancel.
        let mut list: Vec<FormId> = Vec::with_capacity(flat.len());
        for i in flat {
            if list.last() == Some(&i) {
                list.pop();
            } else {
                list.push(i);
            }
        }
        // A constant that is one run of ones is taken with slices, as `band` takes it.
        let mut run = 0i128;
        if k != 0 {
            let r = k >> k.trailing_zeros();
            if r & (r + 1) == 0 {
                run = k;
                k = 0;
            }
        }
        let core = if list.is_empty() {
            Form::konst(k)
        } else if list.len() == 1 && k == 0 {
            self.form(list[0]).clone()
        } else if let Some(h) = self.hoisted(q, &list, k)? {
            h
        } else {
            self.xor_atom(list, k)?
        };
        // (The value: what of it is below `2^q`.)
        let mut core = self.modulo(&core, q)?;
        if run != 0 {
            let and = self.band(q, &core, &Form::konst(run))?;
            let sum = self.shift(&core, run)?;
            core = self.add(&sum, &and, -2)?;
        }
        if neg {
            let m = self.scale(&core, -1)?;
            core = self.shift(&m, top)?;
        }
        Ok(core)
    }

    /// The operand an XOR or an AND takes for the value `e` (in `[0, 2^q)`): `e` without its
    /// multiples of `2^q` where that is not negative (the word a truncation is of), else
    /// `e`; and `e` always where the operands are the values (see `values`).
    fn rep(&mut self, e: &Form, q: u32) -> Form {
        let r = self.reduce(e, q);
        if r == *e || !self.interval(&r).within(0, (1i128 << MAX_SHIFT) - 1) {
            return e.clone();
        }
        self.wordy |= self.linking == 0;
        if self.values { e.clone() } else { r }
    }

    /// The XOR of operands that are all the same floor, or the same slice, of forms: that
    /// floor or slice of the XOR of the forms (with `k`, shifted to where they are).
    fn hoisted(&mut self, p: u32, list: &[FormId], k: i128) -> R<Option<Form>> {
        let mut common: Option<(u32, Option<u32>)> = None;
        let mut inner: Vec<Form> = Vec::with_capacity(list.len() + 1);
        for &i in list {
            let f = self.form(i).clone();
            let Some((Some(e), lo, len)) = self.shape(&f) else {
                return Ok(None);
            };
            // (Of what begins at bit 0 the XOR is no floor of another.)
            if lo == 0 {
                return Ok(None);
            }
            match common {
                None => common = Some((lo, len)),
                Some(c) if c == (lo, len) => {}
                _ => return Ok(None),
            }
            inner.push(e);
        }
        let Some((lo, len)) = common else {
            return Ok(None);
        };
        // (What of the constant is above the slice is beside it.)
        let width = len.unwrap_or(p).min(p);
        if lo + width > MAX_SHIFT {
            return Ok(None);
        }
        let low = (1i128 << width) - 1;
        inner.push(Form::konst((k & low) << lo));
        let x = self.bxor(lo + width, &inner)?;
        let out = match len {
            None => self.floor(&x, lo, None)?,
            Some(len) => self.slice(&x, lo, len, None)?,
        };
        let out = self.wrap(&out, p, None)?;
        Ok(Some(self.shift(&out, k & !low)?))
    }

    /// The atom of the XOR of the operands `list` (values that are not negative, in order,
    /// each once, two at least or one and a constant) and `k`: of them as integers.
    fn xor_atom(&mut self, list: Vec<FormId>, k: i128) -> R<Form> {
        let mut q = if k == 0 { 1 } else { bit_len(k) };
        for &i in &list {
            let f = self.form(i).clone();
            q = q.max(self.range(&f).bits().ok_or(Over)?);
        }
        if q > MAX_SHIFT {
            return Err(Over);
        }
        let mut hash = combine(combine(0x0078_6f72, u64::from(q)), k as u64);
        hash = combine(hash, (k >> 64) as u64);
        for &i in &list {
            hash = combine(hash, self.hashes[i as usize]);
        }
        let key = (list, k);
        let li = match self.list_ids.get(&key) {
            Some(&li) => li,
            None => {
                if self.lists.len() >= MAX_ATOMS {
                    return Err(Over);
                }
                let li = self.lists.len() as u32;
                self.lists.push(key.clone());
                self.list_ids.insert(key, li);
                li
            }
        };
        let a = self.make(Atom::Xor(q as u8, li), hash, Iv::new(0, (1i128 << q) - 1))?;
        Ok(Self::one(a))
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

    /// The value of `f` lies in `iv`: `f` is the form of a node, and these are the node's
    /// bounds. They are read where a form is an operand that has to be a value of so many
    /// bits (see `range`), and nowhere else: the forms themselves are as without them.
    pub(super) fn bound(&mut self, f: &Form, iv: Iv) {
        if f.t.is_empty() || self.plain {
            return;
        }
        let met = self.given.get(f).map_or(iv, |old| old.meet(iv));
        // (Bounds that cross are of a value that does not occur.)
        if matches!((met.lo, met.hi), (Some(l), Some(h)) if l > h) {
            return;
        }
        self.given.insert(f.clone(), met);
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
        // A bitwise combination: `α·x + β·y + γ·(x & y) + δ·(x ^ y)` takes, bit by bit, one
        // of the values 0, α + δ, β + δ and α + β + γ times the bit's weight.
        let mut tried = 0;
        for &(m, g) in &f.t {
            let Atom::And(p, xi, yi) = self.atom(m) else {
                continue;
            };
            // The XOR of the two, where it is an atom of the form: then the AND is that of
            // the values it was asked of, whole. Else an operand is read by its low `p`
            // bits: an atom that is wider, as those.
            let xor = self.xor_of(m).filter(|&a| f.coeff(a) != 0);
            let dl = xor.map_or(0, |a| f.coeff(a));
            let whole = xor.and_then(|_| self.whole.get(&m).cloned());
            let top = match whole {
                Some(_) => (1i128 << MAX_SHIFT) - 1,
                None => (1i128 << p) - 1,
            };
            let known = whole.is_some();
            let mut ops = match whole {
                Some((x, y)) => [x, y],
                None => [self.form(xi).clone(), self.form(yi).clone()],
            };
            let mut ivs = [Iv::point(0); 2];
            for (z, iz) in ops.iter_mut().zip(&mut ivs) {
                *iz = match known {
                    true => self.range(z),
                    false => self.interval_at(z, depth + 1),
                };
                if !known
                    && !iz.within(0, top)
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
                let Ok(rest) = self.sum(f, &x, -al).and_then(|r| self.sum(&r, &y, -be)) else {
                    continue;
                };
                let mut rest = rest.without(m);
                if let Some(a) = xor {
                    rest = rest.without(a);
                }
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
                                .and_then(|s| s.checked_add(g * (xb & yb)))
                                .and_then(|s| s.checked_add(dl * (xb ^ yb)));
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
            let Ok(rest) = self.sum(f, &r, -lam) else {
                continue;
            };
            // (Moved along the relations of its atoms: what the remainder leaves may be an
            // XOR against the sum it is of.)
            let rest = rest.without(a);
            let rest = self.settle(rest.clone()).unwrap_or(rest);
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
                let Ok(rest) = self.sum(f, &Self::one(lo), -lam) else {
                    continue;
                };
                let rest = rest.without(hi);
                let rest = self.settle(rest.clone()).unwrap_or(rest);
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

    /// One level deeper; the caller leaves it again. (Refused at the bound without counting:
    /// a refusal leaves the depth as it was.)
    fn enter(&mut self) -> R<()> {
        if self.depth >= MAX_DEPTH {
            return Err(Over);
        }
        self.depth += 1;
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
        // A choice against a constant, whole: its floor is the choice between the floors of
        // what it is where the condition holds and where it does not.
        if !self.plain
            && let Some((c, hi, lo)) = self.cases(&r)?
        {
            let (fh, fl) = (self.floor(&hi, k, None)?, self.floor(&lo, k, None)?);
            let s = self.sel(&c, &fh, &fl)?;
            self.forked |= self.linking == 0;
            return self.add(&out, &s, 1);
        }
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
        // The floor of an XOR of values: those below `2^k` are not in it.
        if let Some(a) = r.single()
            && let Atom::Xor(q, li) = self.atom(a)
        {
            let (ops, kk) = self.lists[li as usize].clone();
            let mut kept: Vec<Form> = Vec::with_capacity(ops.len() + 1);
            for &i in &ops {
                let g = self.form(i).clone();
                if self.interval(&g).bits().is_none_or(|b| b > k) {
                    kept.push(g);
                }
            }
            if kept.len() < ops.len() {
                kept.push(Form::konst(kk));
                let x = self.bxor(u32::from(q), &kept)?;
                let fl = self.floor(&x, k, None)?;
                return self.add(&out, &fl, 1);
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
        // An AND atom is of its operands modulo a power of two (the bits of the lesser);
        // the values it was asked of are kept, for its relation with their XOR.
        if !self.plain
            && let Ok(f) = &r
            && let Some(a) = f.single()
            && matches!(self.atom(a), Atom::And(q, ..) if q >= 2)
            && !self.whole.contains_key(&a)
            && let Some(w) = self.operands(p, x, y)
        {
            self.whole.insert(a, w);
            self.linked[a as usize] = self.link(a).is_some();
        }
        r
    }

    /// Two values that are not negative whose AND, as integers, is `(x mod 2^p) & (y mod
    /// 2^p)`: the two without their multiples of `2^p` where those are not negative and one
    /// is below `2^p` (the words truncations are of, as arithmetic takes them); else the
    /// two as they are modulo `2^p`, where they are known to be.
    fn operands(&mut self, p: u32, x: &Form, y: &Form) -> Option<(Form, Form)> {
        let top = (1i128 << p) - 1;
        let big = (1i128 << MAX_SHIFT) - 1;
        if !self.values {
            let (rx, ry) = (self.reduce(x, p), self.reduce(y, p));
            let (ix, iy) = (self.interval(&rx), self.interval(&ry));
            if ix.within(0, big) && iy.within(0, big) && (ix.within(0, top) || iy.within(0, top)) {
                self.wordy |= self.linking == 0 && (rx != *x || ry != *y);
                return Some((rx, ry));
            }
        }
        self.exact(x, p).zip(self.exact(y, p))
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
            return self.band_in(q, &x, &y);
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

    /// `(C, r₁, r₀)` when `r` is `q + μ·C + λ·(c ? A : B)`: a choice one arm of which is the
    /// form 0 (how one against a constant is read, see `sel`), a multiple `μ ≠ 0` of the form
    /// `C` of its condition, and a constant. What `r` is where the condition holds, `q + μ +
    /// λ·A`, and where it does not, `q + λ·B`.
    fn cases(&mut self, r: &Form) -> R<Option<(Form, Form, Form)>> {
        for &(s, lam) in &r.t {
            let Atom::Sel(ci, ai, bi) = self.atom(s) else {
                continue;
            };
            let (c, a, b) = (
                self.form(ci).clone(),
                self.form(ai).clone(),
                self.form(bi).clone(),
            );
            let none = |x: &Form| x.is_const() && x.c == 0;
            if none(&a) == none(&b) {
                continue;
            }
            let Some(&(a0, c0)) = c.t.first() else {
                continue;
            };
            let have = r.coeff(a0);
            if have == 0 || have % c0 != 0 {
                continue;
            }
            let mu = have / c0;
            let rest = self.sum(r, &c, -mu)?.without(s);
            if !rest.is_const() {
                continue;
            }
            let hi = self.scaled(&a, lam)?;
            let hi = self.shift(&hi, plus(rest.c, mu)?)?;
            let lo = self.scaled(&b, lam)?;
            let lo = self.shift(&lo, rest.c)?;
            return Ok(Some((c, hi, lo)));
        }
        Ok(None)
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
        // A constant arm is taken apart: `c ? K : b` is `K·c + (c ? 0 : b)`, and `c ? a : K`
        // is `K − K·c + (c ? a : 0)`. The floors and slices of the other arm are then those
        // of the choice (below), whatever digits of a constant each is chosen against: a
        // value chosen limb by limb between a register and a constant is the limbs of the
        // one choice.
        if !self.plain {
            let zero = Form::default();
            if a.is_const() && a.c != 0 {
                let s = self.sel(c, &zero, b)?;
                self.forked |= self.linking == 0;
                return self.add(&s, c, a.c);
            }
            if b.is_const() && b.c != 0 {
                let s = self.sel(c, a, &zero)?;
                self.forked |= self.linking == 0;
                let t = self.add(&s, c, -b.c)?;
                return self.shift(&t, b.c);
            }
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

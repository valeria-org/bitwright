//! Bit-level facts: known bits, unsigned and signed ranges, and tri-state proofs.
//!
//! Facts about an expression are sound over-approximations of the set of values it can take.
//! They are computed lazily, iteratively (no recursion), cached per node for the life of the
//! context, and bounded by a per-query work cap: when the cap is reached the answer is `top`
//! (always sound), the nodes whose transfer completed stay cached, and the next query
//! continues from there. Fact queries never create expression nodes.

mod backward;
mod constraint;
pub(crate) mod known;
mod range;
#[cfg(test)]
mod tests;
mod transfer;

use core::fmt;
use std::sync::Arc;

pub(crate) use constraint::Env;
pub use constraint::{Assumptions, ConstraintId, Reliance};
pub use known::KnownBits;
pub use range::{SRange, URange};

use crate::error::Error;
use crate::expr::{Context, Expr, OpCode};
use crate::hash::IdMap;
use crate::ops::{CmpOp, CmpOpExt, UnOp};
use crate::{BitVec, Width};
use range::{sle, slt, ule, ult};
pub(crate) use transfer::decide as decide_cmp;
use transfer::{TOp, decide, transfer};

/// What is known about the values of a `W`-bit expression: known bits, and an unsigned and a
/// signed interval. All three are kept consistent with each other (a reduced product).
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Facts {
    pub(crate) known: KnownBits,
    pub(crate) urange: URange,
    pub(crate) srange: SRange,
}

impl fmt::Debug for Facts {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Facts({:?}, u[{}, {}], s[{}, {}])",
            self.known,
            self.urange.lo(),
            self.urange.hi(),
            self.srange.lo(),
            self.srange.hi()
        )
    }
}

impl Facts {
    /// Nothing known.
    pub fn top(w: Width) -> Facts {
        Facts {
            known: KnownBits::unknown(w),
            urange: URange::full(w),
            srange: SRange::full(w),
        }
    }

    /// Exactly one value.
    pub fn constant(v: &BitVec) -> Facts {
        Facts {
            known: KnownBits::constant(v),
            urange: URange::constant(v),
            srange: SRange::constant(v),
        }
    }

    /// Facts from their three components, reduced against each other. `None` if the widths
    /// differ or no value satisfies all three.
    pub fn new(known: KnownBits, urange: URange, srange: SRange) -> Option<Facts> {
        if known.width() != urange.width() || known.width() != srange.width() {
            return None;
        }
        Facts::reduce(known, urange, srange)
    }

    /// Known bits.
    pub fn known(&self) -> KnownBits {
        self.known
    }

    /// The unsigned interval.
    pub fn urange(&self) -> URange {
        self.urange
    }

    /// The signed interval.
    pub fn srange(&self) -> SRange {
        self.srange
    }

    /// The facts implied by known bits alone.
    pub fn from_known(k: KnownBits) -> Facts {
        let w = k.width();
        Facts::reduce(k, URange::full(w), SRange::full(w)).unwrap_or_else(|| Facts::top(w))
    }

    /// The width.
    pub fn width(&self) -> Width {
        self.known.width()
    }

    /// The value, if the facts pin exactly one.
    pub fn as_constant(&self) -> Option<BitVec> {
        self.known.as_constant()
    }

    /// Whether `v` is consistent with every component.
    pub fn contains(&self, v: &BitVec) -> bool {
        self.known.contains(v) && self.urange.contains(v) && self.srange.contains(v)
    }

    /// Facts true of both (the intersection); `None` if contradictory or of different widths.
    pub fn meet(&self, o: &Facts) -> Option<Facts> {
        if self.width() != o.width() {
            return None;
        }
        // Facts are always reduced, so when one refines the other it is the meet.
        if self.refines(o) {
            return Some(*self);
        }
        if o.refines(self) {
            return Some(*o);
        }
        Facts::reduce(
            self.known.meet(&o.known)?,
            self.urange.meet(&o.urange)?,
            self.srange.meet(&o.srange)?,
        )
    }

    /// Whether every value `self` allows, `o` allows too, component by component.
    fn refines(&self, o: &Facts) -> bool {
        let (k, ok) = (&self.known, &o.known);
        let bits = |a: &BitVec, b: &BitVec| known::bv_and(a, &known::bv_not(b)).is_zero();
        bits(&ok.known_zero(), &k.known_zero())
            && bits(&ok.known_one(), &k.known_one())
            && ule(&o.urange.lo(), &self.urange.lo())
            && ule(&self.urange.hi(), &o.urange.hi())
            && sle(&o.srange.lo(), &self.srange.lo())
            && sle(&self.srange.hi(), &o.srange.hi())
    }

    /// Facts true of either (the hull); `None` if the widths differ.
    pub fn join(&self, o: &Facts) -> Option<Facts> {
        (self.width() == o.width()).then(|| self.hull(o))
    }

    /// `join` for operands known to have the same width.
    pub(crate) fn hull(&self, o: &Facts) -> Facts {
        let w = self.width();
        Facts::reduce(
            self.known.hull(&o.known),
            self.urange.hull(&o.urange),
            self.srange.hull(&o.srange),
        )
        .unwrap_or_else(|| Facts::top(w))
    }

    pub(crate) fn meet_known(&self, k: &KnownBits) -> Option<Facts> {
        Facts::reduce(self.known.meet(k)?, self.urange, self.srange)
    }

    pub(crate) fn meet_urange(&self, u: &URange) -> Option<Facts> {
        Facts::reduce(self.known, self.urange.meet(u)?, self.srange)
    }

    /// The reduced product: tightens each component with the others. `None` if the
    /// components are contradictory (no value satisfies all three).
    pub(crate) fn reduce(mut k: KnownBits, mut u: URange, mut s: SRange) -> Option<Facts> {
        let w = k.width();
        for round in 0..2 {
            let before = (k, u, s);
            // Known bits bound both ranges.
            u = u.meet(&URange::new(k.umin(), k.umax())?)?;
            s = s.meet(&SRange::new(k.smin(), k.smax())?)?;
            // An unsigned range fixes its bounds' common high bits.
            k = k.meet(&prefix_bits(&u.lo(), &u.hi()))?;
            // A signed range on one side of zero orders like an unsigned one.
            let zero = BitVec::zero(w);
            let non_negative = sle(&zero, &s.lo());
            let negative = slt(&s.hi(), &zero);
            if non_negative || negative {
                k = k.meet(&prefix_bits(&s.lo(), &s.hi()))?;
                u = u.meet(&URange::new(s.lo(), s.hi())?)?;
            }
            // An unsigned range on one side of the sign boundary is also a signed range.
            let smax = BitVec::smax(w);
            if ule(&u.hi(), &smax) || ult(&smax, &u.lo()) {
                s = s.meet(&SRange::new(u.lo(), u.hi())?)?;
            }
            // A round that changed nothing is a fixed point; the second round only helps when
            // the first tightened something.
            if round == 0 && before == (k, u, s) {
                break;
            }
        }
        Some(Facts {
            known: k,
            urange: u,
            srange: s,
        })
    }
}

/// Transfer functions over facts, for hosts composing their own (for example the known bits of
/// an extension operation): the facts of an operator's result for every operand value inside
/// the operands' facts. Sound; as precise as the context's own.
impl Facts {
    /// Facts of `op(a)`.
    pub fn apply_un(op: UnOp, a: &Facts) -> Result<Facts, crate::WidthError> {
        BitVec::apply_un(op, &BitVec::zero(a.width()))?;
        Ok(transfer(&TOp::Un(op), &[a]))
    }

    /// Facts of `op(a, b)`.
    pub fn apply_bin(op: crate::BinOp, a: &Facts, b: &Facts) -> Result<Facts, crate::WidthError> {
        same_width(a, b)?;
        Ok(transfer(&TOp::Bin(op), &[a, b]))
    }

    /// Facts of the 1-bit comparison `op(a, b)`.
    pub fn apply_cmp(
        op: impl Into<CmpOpExt>,
        a: &Facts,
        b: &Facts,
    ) -> Result<Facts, crate::WidthError> {
        same_width(a, b)?;
        let (op, swap) = op.into().canonical();
        let (a, b) = if swap { (b, a) } else { (a, b) };
        Ok(transfer(&TOp::Cmp(op), &[a, b]))
    }

    /// Facts of the zero extension to `to` bits (`to` at least the width).
    pub fn zext(&self, to: Width) -> Result<Facts, crate::WidthError> {
        if to == self.width() {
            return Ok(*self);
        }
        crate::BitVec::zero(self.width()).zext(to)?;
        Ok(transfer(&TOp::Zext(to), &[self]))
    }

    /// Facts of the sign extension to `to` bits (`to` at least the width).
    pub fn sext(&self, to: Width) -> Result<Facts, crate::WidthError> {
        if to == self.width() {
            return Ok(*self);
        }
        crate::BitVec::zero(self.width()).sext(to)?;
        Ok(transfer(&TOp::Sext(to), &[self]))
    }

    /// Facts of bits `[lo, lo + len)`.
    pub fn extract(&self, lo: u16, len: Width) -> Result<Facts, crate::WidthError> {
        crate::BitVec::zero(self.width()).extract(lo, len)?;
        Ok(transfer(&TOp::Extract { lo, width: len }, &[self]))
    }

    /// Facts of `hi · 2^L + lo`.
    pub fn concat(hi: &Facts, lo: &Facts) -> Result<Facts, crate::WidthError> {
        crate::BitVec::concat(&BitVec::zero(hi.width()), &BitVec::zero(lo.width()))?;
        Ok(transfer(&TOp::Concat, &[hi, lo]))
    }

    /// Facts of `c ? t : f` (`c` of 1 bit).
    pub fn select(c: &Facts, t: &Facts, f: &Facts) -> Result<Facts, crate::WidthError> {
        crate::BitVec::select(
            &BitVec::zero(c.width()),
            &BitVec::zero(t.width()),
            &BitVec::zero(f.width()),
        )?;
        Ok(transfer(&TOp::Select, &[c, t, f]))
    }
}

/// The same transfers on known bits alone (through [`Facts`]: the result may be sharper than
/// a bits-only transfer, never less sound).
impl KnownBits {
    /// Known bits of `op(a)`.
    pub fn apply_un(op: UnOp, a: &KnownBits) -> Result<KnownBits, crate::WidthError> {
        Ok(Facts::apply_un(op, &Facts::from_known(*a))?.known)
    }

    /// Known bits of `op(a, b)`.
    pub fn apply_bin(
        op: crate::BinOp,
        a: &KnownBits,
        b: &KnownBits,
    ) -> Result<KnownBits, crate::WidthError> {
        Ok(Facts::apply_bin(op, &Facts::from_known(*a), &Facts::from_known(*b))?.known)
    }
}

fn same_width(a: &Facts, b: &Facts) -> Result<(), crate::WidthError> {
    if a.width() == b.width() {
        Ok(())
    } else {
        Err(crate::WidthError::Mismatch {
            left: a.width().bits(),
            right: b.width().bits(),
        })
    }
}

/// Known bits shared by every value in `[lo, hi]` (unsigned): the common high bits.
fn prefix_bits(lo: &BitVec, hi: &BitVec) -> KnownBits {
    let w = lo.width();
    let diff = known::bv_xor(lo, hi);
    let p = known::leading_zeros(&diff);
    let mask = known::high_mask(w, p);
    KnownBits::from_masks(
        known::bv_and(&known::bv_not(lo), &mask),
        known::bv_and(lo, &mask),
    )
}

/// A three-valued answer. `Unknown` is always a correct answer.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Truth {
    /// Proved true.
    True,
    /// Proved false.
    False,
    /// Not decided.
    Unknown,
}

impl Truth {
    fn from_opt(b: Option<bool>) -> Truth {
        match b {
            Some(true) => Truth::True,
            Some(false) => Truth::False,
            None => Truth::Unknown,
        }
    }
}

impl core::ops::Not for Truth {
    type Output = Truth;
    /// The logical negation (`Unknown` stays `Unknown`).
    fn not(self) -> Truth {
        match self {
            Truth::True => Truth::False,
            Truth::False => Truth::True,
            Truth::Unknown => Truth::Unknown,
        }
    }
}

/// A question about expression values, answered by [`Context::prove`].
#[derive(Copy, Clone, Debug)]
#[non_exhaustive]
pub enum Query<'q> {
    /// The value is zero.
    IsZero(Expr),
    /// The value is not zero.
    IsNonZero(Expr),
    /// Bit `bit` has value `value`.
    Bit {
        /// The expression.
        e: Expr,
        /// The bit index.
        bit: u16,
        /// The value asked about.
        value: bool,
    },
    /// The two values are equal.
    Eq(Expr, Expr),
    /// The comparison holds.
    Cmp(CmpOpExt, Expr, Expr),
    /// The value is in `[lo, hi]` (unsigned).
    InURange {
        /// The expression.
        e: Expr,
        /// Lower bound.
        lo: &'q BitVec,
        /// Upper bound.
        hi: &'q BitVec,
    },
    /// The value is in `[lo, hi]` (signed).
    InSRange {
        /// The expression.
        e: Expr,
        /// Lower bound.
        lo: &'q BitVec,
        /// Upper bound.
        hi: &'q BitVec,
    },
    /// The value is a multiple of `2^log2`.
    Aligned {
        /// The expression.
        e: Expr,
        /// Alignment exponent.
        log2: u16,
    },
    /// `e & mask == e`.
    MaskRedundant {
        /// The expression.
        e: Expr,
        /// The mask.
        mask: &'q BitVec,
    },
    /// The unsigned value fits in `bits` bits.
    FitsUnsigned {
        /// The expression.
        e: Expr,
        /// Number of bits.
        bits: u16,
    },
    /// The signed value fits in `bits` bits.
    FitsSigned {
        /// The expression.
        e: Expr,
        /// Number of bits.
        bits: u16,
    },
    /// The facts pin the value to one constant.
    IsConstant(Expr),
    /// `e` is an injective function of its subexpression `of`: with every value that does not
    /// depend on `of` held fixed, distinct values put in place of `of` give distinct values of
    /// `e`. Proved through a chain of invertible layers from `of` up to `e` (operators
    /// injective in one operand with the others fixed, such as `x ^ k`, `x * k` for odd `k`,
    /// rotations, `zext`, declared extension operations, and triangular maps such as
    /// `h ^ ((h >>u 32) >>u (h >>u 60))`); `False` when `e` does not depend on `of` or is
    /// narrower than it.
    Injective {
        /// The expression.
        e: Expr,
        /// The subexpression it is read as a function of.
        of: Expr,
    },
    /// `e` is a bijective function of its subexpression `of`: injective (see
    /// [`Query::Injective`]), of the same width. `False` when `e` does not depend on `of` or
    /// their widths differ.
    Bijective {
        /// The expression.
        e: Expr,
        /// The subexpression it is read as a function of.
        of: Expr,
    },
}

/// An answer from [`Context::prove_under`]: the truth value, and the constraints it relies on
/// (none for `Unknown`).
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub struct Proof {
    /// The answer.
    pub truth: Truth,
    /// The constraints the answer relies on.
    pub relies_on: Reliance,
}

/// A capped base-fact computation in progress: the post-order of the uncached part below
/// `root`, and how far it got. A later query for the same root resumes here.
#[derive(Clone, Debug)]
struct Pending {
    root: u32,
    order: Vec<u32>,
    pos: usize,
}

/// Facts of width up to 64 as six words: the known zero and one bits and both ranges' bounds.
fn to_words(f: &Facts) -> [u64; 6] {
    let w = |v: BitVec| v.limbs()[0];
    [
        w(f.known.known_zero()),
        w(f.known.known_one()),
        w(f.urange.lo()),
        w(f.urange.hi()),
        w(f.srange.lo()),
        w(f.srange.hi()),
    ]
}

/// The facts of width `w` (at most 64) from their six words.
fn from_words(w: Width, x: &[u64; 6]) -> Facts {
    let v = |x: u64| BitVec::from_canonical_u64(w, x);
    Facts {
        known: KnownBits::from_masks(v(x[0]), v(x[1])),
        urange: URange::from_bounds(v(x[2]), v(x[3])),
        srange: SRange::from_bounds(v(x[4]), v(x[5])),
    }
}

/// Facts stored compactly: six words up to 64 bits, whole beyond.
#[derive(Clone, Debug)]
enum Packed {
    Narrow([u64; 6]),
    Wide(Box<Facts>),
}

impl Packed {
    fn new(f: &Facts) -> Packed {
        if f.width().bits() <= 64 {
            Packed::Narrow(to_words(f))
        } else {
            Packed::Wide(Box::new(*f))
        }
    }

    /// The facts, of width `w`.
    fn get(&self, w: Width) -> Facts {
        match self {
            Packed::Narrow(x) => from_words(w, x),
            Packed::Wide(f) => **f,
        }
    }
}

/// Facts and the constraints they rely on per node, packed: the overlays of facts under
/// assumptions.
#[derive(Clone, Debug, Default)]
pub(crate) struct FactMap(IdMap<u32, (Packed, Reliance)>);

impl FactMap {
    /// The entry of node `i`, of width `w`.
    pub(crate) fn get(&self, i: u32, w: Width) -> Option<(Facts, Reliance)> {
        self.0.get(&i).map(|(p, r)| (p.get(w), *r))
    }

    pub(crate) fn contains_key(&self, i: u32) -> bool {
        self.0.contains_key(&i)
    }

    pub(crate) fn insert(&mut self, i: u32, (f, r): (Facts, Reliance)) {
        self.0.insert(i, (Packed::new(&f), r));
    }

    pub(crate) fn clear(&mut self) {
        self.0.clear();
    }

    /// Drops the entries of nodes `n` and above.
    pub(crate) fn retain_below(&mut self, n: u32) {
        self.0.retain(|&k, _| k < n);
    }
}

/// Base facts per node, stored compactly: facts of width up to 64 bits as six words (the known
/// zero and one bits and both ranges' bounds) instead of six 512-bit values, wider ones whole.
/// Entries are appended in the order they are computed (bottom-up), and found through a slot per
/// node index, so a query walks both tables mostly in order.
#[derive(Clone, Debug, Default)]
struct BaseFacts {
    /// Per node index: 0 if not cached, else `1 + k` for entry `k` of `narrow` (nodes of width up
    /// to 64) or of `wide`.
    slot: Vec<u32>,
    narrow: Vec<[u64; 6]>,
    wide: Vec<Facts>,
}

impl BaseFacts {
    fn contains(&self, i: u32) -> bool {
        self.slot.get(i as usize).is_some_and(|&s| s != 0)
    }

    /// The facts of node `i`, of width `w`.
    fn get(&self, i: u32, w: Width) -> Option<Facts> {
        let k = (*self.slot.get(i as usize)?).checked_sub(1)? as usize;
        if w.bits() > 64 {
            return Some(self.wide[k]);
        }
        Some(from_words(w, &self.narrow[k]))
    }

    fn insert(&mut self, i: u32, f: Facts) {
        let i = i as usize;
        if i >= self.slot.len() {
            self.slot.resize(i + 1, 0);
        }
        let narrow = f.width().bits() <= 64;
        let at = self.slot[i].checked_sub(1).map(|k| k as usize);
        if !narrow {
            match at {
                Some(k) => self.wide[k] = f,
                None => {
                    self.wide.push(f);
                    self.slot[i] = self.wide.len() as u32;
                }
            }
            return;
        }
        let x = to_words(&f);
        match at {
            Some(k) => self.narrow[k] = x,
            None => {
                self.narrow.push(x);
                self.slot[i] = self.narrow.len() as u32;
            }
        }
    }

    /// Makes room for the nodes below `len` and `more` new entries, so a query grows the tables
    /// once instead of step by step.
    fn reserve(&mut self, len: usize, more: usize) {
        if self.slot.len() < len {
            self.slot.resize(len, 0);
        }
        self.narrow.reserve(more);
    }

    fn clear(&mut self) {
        self.slot.clear();
        self.narrow.clear();
        self.wide.clear();
    }
}

/// The per-context fact cache: base facts per node, one overlay for the most recent
/// assumption set (keyed by an exact copy of it), and the resumable capped computation.
#[derive(Clone, Debug, Default)]
pub(crate) struct FactCache {
    base: BaseFacts,
    overlay: FactMap,
    overlay_key: Option<Assumptions>,
    pending: Option<Pending>,
    /// Transfer functions run so far (never reset; the engine charges differences).
    pub(crate) work: u64,
    /// Queries answered imprecisely because a work cap was reached (never reset).
    pub(crate) capped: u64,
    /// Nodes the overlay walks visited (never reset; for tests of its cost).
    pub(crate) walked: u64,
}

impl FactCache {
    /// Stops keying the overlay by `a` (if it is), so `a` can change without a copy.
    pub(crate) fn forget(&mut self, a: &Assumptions) {
        if self
            .overlay_key
            .as_ref()
            .is_some_and(|k| Arc::ptr_eq(&k.store, &a.store))
        {
            self.overlay_key = None;
            self.overlay.clear();
        }
    }

    pub(crate) fn clear(&mut self) {
        self.base.clear();
        self.overlay.clear();
        self.overlay_key = None;
        self.pending = None;
    }
}

impl Context {
    pub(crate) fn top_of(&self, i: u32) -> TOp {
        let n = self.node(i);
        let w = self.width_of(i);
        match n.op {
            OpCode::Const => TOp::Const(self.const_val(i).unwrap_or(BitVec::zero(w))),
            OpCode::Sym => TOp::Top(w),
            OpCode::Zext => TOp::Zext(w),
            OpCode::Sext => TOp::Sext(w),
            OpCode::Extract => TOp::Extract {
                lo: n.b as u16,
                width: w,
            },
            OpCode::Concat => TOp::Concat,
            OpCode::Select => TOp::Select,
            op => {
                if let Some(u) = op.as_un() {
                    TOp::Un(u)
                } else if let Some(b) = op.as_bin() {
                    TOp::Bin(b)
                } else if let Some(c) = op.as_cmp() {
                    TOp::Cmp(c)
                } else {
                    TOp::Top(w)
                }
            }
        }
    }

    /// The facts of node `i` from the given operand facts alone: [`Self::transfer_at`] without
    /// the refinements that read other nodes' cached facts. For facts computed over a region
    /// whose operands stand for other values than their own (an unknown input, say).
    pub(crate) fn transfer_local(&self, i: u32, args: &[&Facts]) -> Facts {
        let op = self.top_of(i);
        if self.node(i).op == OpCode::Concat {
            return transfer(&op, args);
        }
        self.transfer_at(i, &op, args)
    }

    /// Runs the transfer function of node `i` over facts of its children taken from `get`.
    fn transfer_node(&self, i: u32, get: impl Fn(u32) -> Facts) -> Facts {
        let op = self.top_of(i);
        let n = self.node(i);
        let mut kids = [Facts::top(Width::W1); 3];
        let mut k = 0;
        for c in n.children() {
            kids[k] = get(c);
            k += 1;
        }
        let refs: [&Facts; 3] = [&kids[0], &kids[1], &kids[2]];
        self.transfer_at(i, &op, &refs[..k])
    }

    /// The facts of node `i` (whose operator is `op`) from its operands' facts: the transfer
    /// function, or for an extension node its operation's known bits (exact when every
    /// argument is).
    pub(crate) fn transfer_at(&self, i: u32, op: &TOp, args: &[&Facts]) -> Facts {
        let n = self.node(i);
        if n.op == OpCode::Select {
            let f = transfer(op, args);
            return self
                .min_max_bound(i, args)
                .and_then(|g| f.meet(&g))
                .unwrap_or(f);
        }
        if n.op == OpCode::Concat {
            let f = transfer(op, args);
            return self
                .wide_product_bound(i)
                .and_then(|g| f.meet(&g))
                .unwrap_or(f);
        }
        if n.op == OpCode::LShr {
            let f = transfer(op, args);
            return self
                .self_shift_bound(i, args)
                .and_then(|g| f.meet(&g))
                .unwrap_or(f);
        }
        let Some((_, k)) = n.op.as_ext() else {
            return transfer(op, args);
        };
        let w = self.width_of(i);
        let Some(o) = self.registry.as_deref().and_then(|r| r.op_at(n.aux)) else {
            return Facts::top(w);
        };
        // Exact when every argument is.
        let vals: Option<Vec<BitVec>> = args.iter().map(|f| f.as_constant()).collect();
        if let Some(vals) = vals {
            return match crate::ext::run_eval(o, &vals) {
                Ok(out) if out.get(k).is_some_and(|v| v.width() == w) => Facts::constant(&out[k]),
                _ => Facts::top(w),
            };
        }
        let widths: Vec<Width> = args.iter().map(|f| f.width()).collect();
        let Ok(sig) = o.signature(&widths) else {
            return Facts::top(w);
        };
        let kb: Vec<KnownBits> = args.iter().map(|f| f.known).collect();
        match crate::ext::run_known_bits(o, &sig, &kb) {
            Ok(out) => out
                .get(k)
                .filter(|kb| kb.width() == w)
                .map_or(Facts::top(w), |kb| Facts::from_known(*kb)),
            Err(_) => Facts::top(w),
        }
    }

    /// A select choosing between the two operands of its own ordered comparison is a minimum or
    /// maximum (`select(p <u q, p, q)` is `umin(p, q)`): the range of the choice is then bounded
    /// on both sides, which the join of the arms alone does not give.
    fn min_max_bound(&self, i: u32, args: &[&Facts]) -> Option<Facts> {
        let n = self.node(i);
        let c = self.node(n.a);
        let op = c.op.as_cmp()?;
        let min = if (n.b, n.c) == (c.a, c.b) {
            true
        } else if (n.b, n.c) == (c.b, c.a) {
            false
        } else {
            return None;
        };
        let (t, f) = (args[1], args[2]);
        let w = t.width();
        let pick = |x: BitVec, y: BitVec, less: fn(&BitVec, &BitVec) -> bool, low: bool| {
            if less(&x, &y) == low { x } else { y }
        };
        match op {
            CmpOp::Ult | CmpOp::Ule => {
                let (a, b) = (t.urange, f.urange);
                let lo = pick(a.lo(), b.lo(), ult, min);
                let hi = pick(a.hi(), b.hi(), ult, min);
                Facts::new(KnownBits::unknown(w), URange::new(lo, hi)?, SRange::full(w))
            }
            CmpOp::Slt | CmpOp::Sle => {
                let (a, b) = (t.srange, f.srange);
                let lo = pick(a.lo(), b.lo(), slt, min);
                let hi = pick(a.hi(), b.hi(), slt, min);
                Facts::new(KnownBits::unknown(w), URange::full(w), SRange::new(lo, hi)?)
            }
            _ => None,
        }
    }

    /// A right shift of a value by its own top bits, `a >>u (a >>u k)` (the count spelled
    /// `b >>u m` with `a = b >>u j`, `j <= m`, or `a = b`), as in xorshift-multiply mixers
    /// (`h ^ ((h >>u 32) >>u (h >>u 60))`). When the count is `t`, `a` lies in
    /// `[t << k, ((t + 1) << k) - 1]`, so the result is below `2^k` at every `t` (for
    /// `2^t >= t + 1`), where the count's range alone allows the whole of `a`'s.
    fn self_shift_bound(&self, i: u32, args: &[&Facts]) -> Option<Facts> {
        let n = self.node(i);
        let w = self.width_of(i);
        let wb = u64::from(w.bits());
        let s = self.node(n.b);
        if s.op != OpCode::LShr {
            return None;
        }
        let m = self.const_val(s.b)?.to_u64()?;
        let j = if n.a == s.a {
            0
        } else {
            let a = self.node(n.a);
            if a.op != OpCode::LShr || a.a != s.a {
                return None;
            }
            self.const_val(a.b)?.to_u64()?
        };
        if j > m || m >= wb {
            return None;
        }
        // The count is `a >>u k`.
        let k = u32::try_from(m - j).ok()?;
        let (fa, fs) = (args[0], args[1]);
        let (slo, shi) = (fs.urange.lo().to_u64()?, fs.urange.hi().to_u64()?);
        let shl = |v: &BitVec| known::bv_shl(v, k);
        let mut hull: Option<(BitVec, BitVec)> = None;
        let mut widen = |lo: BitVec, hi: BitVec| {
            hull = Some(match hull {
                None => (lo, hi),
                Some((l, h)) => (
                    if ult(&lo, &l) { lo } else { l },
                    if ult(&h, &hi) { hi } else { h },
                ),
            });
        };
        for t in slo..=shi.min(wb - 1) {
            let tv = BitVec::wrapping_from_u64(w, t);
            let first = shl(&tv);
            if known::bv_lshr(&first, k) != tv {
                // No value of `a` has these top bits.
                break;
            }
            let next = known::bv_add(&tv, &BitVec::one(w));
            let past = shl(&next);
            let last = if next.is_zero() || known::bv_lshr(&past, k) != next {
                BitVec::ones(w)
            } else {
                known::bv_add(&past, &BitVec::ones(w))
            };
            let lo = if ult(&first, &fa.urange.lo()) {
                fa.urange.lo()
            } else {
                first
            };
            let hi = if ult(&fa.urange.hi(), &last) {
                fa.urange.hi()
            } else {
                last
            };
            if ult(&hi, &lo) {
                continue;
            }
            let t = u32::try_from(t).ok()?;
            widen(known::bv_lshr(&lo, t), known::bv_lshr(&hi, t));
        }
        if shi >= wb {
            // A count of at least W shifts everything out.
            widen(BitVec::zero(w), BitVec::zero(w));
        }
        let (lo, hi) = hull?;
        Facts::new(KnownBits::unknown(w), URange::new(lo, hi)?, SRange::full(w))
    }

    /// `concat(umulhi(a, b), a * b)` is the full unsigned product of `a` and `b` (and with
    /// `smulhi`, the signed one): at twice the width it cannot overflow, so its range follows
    /// from the operands' ranges, which the two halves' facts alone lose.
    fn wide_product_bound(&self, i: u32) -> Option<Facts> {
        let n = self.node(i);
        let (hi, lo) = (self.node(n.a), self.node(n.b));
        if lo.op != OpCode::Mul || (hi.a, hi.b) != (lo.a, lo.b) {
            return None;
        }
        let signed = match hi.op {
            OpCode::UMulHi => false,
            OpCode::SMulHi => true,
            _ => return None,
        };
        let w2 = self.width_of(i);
        let fa = self.cached_facts(lo.a)?;
        let fb = self.cached_facts(lo.b)?;
        let mul = |x: &BitVec, y: &BitVec| BitVec::bin_unchecked(crate::BinOp::Mul, x, y);
        if signed {
            let ext = |v: BitVec| v.sext(w2).ok();
            let (a, b) = (fa.srange, fb.srange);
            let corners = [
                mul(&ext(a.lo())?, &ext(b.lo())?),
                mul(&ext(a.lo())?, &ext(b.hi())?),
                mul(&ext(a.hi())?, &ext(b.lo())?),
                mul(&ext(a.hi())?, &ext(b.hi())?),
            ];
            let lo = corners
                .iter()
                .copied()
                .reduce(|x, y| if slt(&y, &x) { y } else { x })?;
            let hi = corners
                .iter()
                .copied()
                .reduce(|x, y| if slt(&x, &y) { y } else { x })?;
            Facts::new(
                KnownBits::unknown(w2),
                URange::full(w2),
                SRange::new(lo, hi)?,
            )
        } else {
            let ext = |v: BitVec| v.zext(w2).ok();
            let (a, b) = (fa.urange, fb.urange);
            let lo = mul(&ext(a.lo())?, &ext(b.lo())?);
            let hi = mul(&ext(a.hi())?, &ext(b.hi())?);
            Facts::new(
                KnownBits::unknown(w2),
                URange::new(lo, hi)?,
                SRange::full(w2),
            )
        }
    }

    /// Post-order of the part of the DAG below `root` whose facts are not cached.
    fn uncached_order(&mut self, root: u32) -> Vec<u32> {
        self.marks.begin(self.len());
        let mut order = Vec::new();
        let mut stack: Vec<(u32, u8)> = vec![(root, 0)];
        self.marks.test_and_set(root);
        while let Some(top) = stack.last_mut() {
            let (i, k) = *top;
            let n = self.node(i);
            if (k as usize) < n.op.arity() {
                top.1 += 1;
                let c = [n.a, n.b, n.c][k as usize];
                if !self.facts.base.contains(c) && !self.marks.test_and_set(c) {
                    stack.push((c, 0));
                }
            } else {
                stack.pop();
                order.push(i);
            }
        }
        order
    }

    /// Computes base facts for `root` and every uncached node below it, running at most
    /// `fact_work` transfers. Returns `None` if the cap was reached first; the next call for
    /// the same root resumes where this one stopped, so total work stays linear.
    fn compute_facts(&mut self, root: u32) -> Option<Facts> {
        let cap = self.config().fact_work.max(1);
        self.compute_facts_cap(root, cap)
    }

    /// [`Self::compute_facts`] with at most `cap` transfers (and at most the context's cap).
    fn compute_facts_cap(&mut self, root: u32, cap: u32) -> Option<Facts> {
        if let Some(f) = self.cached_facts(root) {
            return Some(f);
        }
        let cap = cap.min(self.config().fact_work.max(1));
        if cap == 0 {
            self.facts.capped += 1;
            return None;
        }
        let cap = cap as usize;
        let mut pending = match self.facts.pending.take() {
            Some(p) if p.root == root => p,
            _ => Pending {
                root,
                order: self.uncached_order(root),
                pos: 0,
            },
        };
        let len = self.len();
        self.facts
            .base
            .reserve(len, pending.order.len() - pending.pos);
        let mut done = 0usize;
        while pending.pos < pending.order.len() {
            let i = pending.order[pending.pos];
            if !self.facts.base.contains(i) {
                if done >= cap {
                    self.facts.pending = Some(pending);
                    self.facts.capped += 1;
                    return None;
                }
                let f = self.transfer_node(i, |c| {
                    self.cached_facts(c)
                        .expect("operands' facts are computed first")
                });
                self.facts.base.insert(i, f);
                done += 1;
                self.facts.work += 1;
            }
            pending.pos += 1;
        }
        self.cached_facts(root)
    }

    /// The cached base facts of node `i`.
    fn cached_facts(&self, i: u32) -> Option<Facts> {
        self.facts.base.get(i, self.width_of(i))
    }

    /// Facts about `e`. If the per-query work cap (`ContextConfig::fact_work`) is reached,
    /// the answer is [`Facts::top`] (sound, just imprecise); see [`Context::try_facts`].
    pub fn facts(&mut self, e: Expr) -> Result<Facts, Error> {
        let i = self.id(e)?;
        Ok(self
            .compute_facts(i)
            .unwrap_or_else(|| Facts::top(self.width_of(i))))
    }

    /// Facts about `e`, or `None` if the per-query work cap was reached first. Progress is
    /// kept: repeating the call for the same expression continues where it stopped.
    pub fn try_facts(&mut self, e: Expr) -> Result<Option<Facts>, Error> {
        let i = self.id(e)?;
        Ok(self.compute_facts(i))
    }

    /// The value of `e` if its facts pin exactly one.
    pub fn exact(&mut self, e: Expr) -> Result<Option<BitVec>, Error> {
        if let Some(v) = self.as_const(e)? {
            return Ok(Some(v));
        }
        Ok(self.facts(e)?.as_constant())
    }

    /// The values `e`'s facts allow, if there are at most `limit` of them (and at most 2^20
    /// candidates to examine). Every value `e` can take is included; some included values may
    /// be impossible, since facts over-approximate.
    pub fn enumerate_values(&mut self, e: Expr, limit: u32) -> Result<Option<Vec<BitVec>>, Error> {
        let f = self.facts(e)?;
        let limit = u64::from(limit.min(1 << 20));
        // From the unsigned range when it is narrow.
        let span = BitVec::bin_unchecked(crate::BinOp::Sub, &f.urange.hi(), &f.urange.lo());
        if span.to_u64().is_some_and(|d| d < limit) {
            let mut out = Vec::new();
            let mut v = f.urange.lo();
            let one = BitVec::one(f.width());
            loop {
                if f.contains(&v) {
                    out.push(v);
                }
                if v == f.urange.hi() {
                    break;
                }
                v = BitVec::bin_unchecked(crate::BinOp::Add, &v, &one);
            }
            return Ok(Some(out));
        }
        // From the known bits otherwise.
        Ok(f.known
            .enumerate(20)
            .map(|vs| vs.into_iter().filter(|v| f.contains(v)).collect::<Vec<_>>())
            .filter(|vs| vs.len() as u64 <= limit))
    }

    /// Facts about `e` under `assumptions`, or `None` if the assumptions are infeasible for
    /// the part of the expression that `e` depends on. Never pollutes the base cache.
    pub fn facts_with(
        &mut self,
        e: Expr,
        assumptions: &Assumptions,
    ) -> Result<Option<Facts>, Error> {
        let cap = self.config().fact_work;
        self.facts_with_cap(e, assumptions, cap)
    }

    /// Base facts with at most `cap` transfers; `None` if the cap was reached first.
    pub(crate) fn try_facts_cap(&mut self, e: Expr, cap: u32) -> Result<Option<Facts>, Error> {
        let i = self.id(e)?;
        Ok(self.compute_facts_cap(i, cap))
    }

    /// Facts about `e` under `assumptions`, with the constraints they rely on; `None` if the
    /// assumptions are infeasible. Never pollutes the base cache.
    pub fn facts_under(
        &mut self,
        e: Expr,
        assumptions: &Assumptions,
    ) -> Result<Option<(Facts, Reliance)>, Error> {
        let cap = self.config().fact_work;
        Ok(self.facts_under_cap(e, assumptions, cap)?.ok())
    }

    /// [`Context::facts_with`] with at most `cap` transfers per query (and at most the
    /// context's cap); a capped query answers `top`, counted in `capped`.
    pub(crate) fn facts_with_cap(
        &mut self,
        e: Expr,
        assumptions: &Assumptions,
        cap: u32,
    ) -> Result<Option<Facts>, Error> {
        Ok(self
            .facts_under_cap(e, assumptions, cap)?
            .ok()
            .map(|(f, _)| f))
    }

    /// Facts about `e` under `assumptions` and the constraints they rely on, with at most `cap`
    /// transfers; `Err` with the conflicting constraints if the assumptions are infeasible.
    pub(crate) fn facts_under_cap(
        &mut self,
        e: Expr,
        assumptions: &Assumptions,
        cap: u32,
    ) -> Result<Result<(Facts, Reliance), Reliance>, Error> {
        let root = self.id(e)?;
        self.overlay_for(assumptions)?;
        let mut overlay = core::mem::take(&mut self.facts.overlay);
        let r = self.overlay_facts(&assumptions.store.env, &mut overlay, root, cap);
        self.facts.overlay = overlay;
        Ok(r)
    }

    /// Makes the overlay follow `assumptions` (dropping it if they changed).
    fn overlay_for(&mut self, assumptions: &Assumptions) -> Result<(), Error> {
        if self.facts.overlay_key.as_ref() != Some(assumptions) {
            assumptions.check_context(self)?;
            self.facts.overlay.clear();
            self.facts.overlay_key = Some(assumptions.clone());
        }
        Ok(())
    }

    /// Whether `op(x, y)` follows from (or is refuted by) an assumed ordering of the nodes `x`
    /// and `y`, and what it relies on.
    pub(crate) fn assumed_order(
        &self,
        assumptions: &Assumptions,
        op: CmpOp,
        x: u32,
        y: u32,
    ) -> Option<(bool, Reliance)> {
        let env = &assumptions.store.env;
        if env.infeasible.is_some() || x == y {
            return None;
        }
        let (m, r) = env.relation(x, y)?;
        constraint::worlds::decide(m, op).map(|v| (v, r))
    }

    /// Facts of node `root` under `env`, cached in `overlay`, with at most `cap` transfers (a
    /// capped query answers `top`, counted in `capped`). `Err` with the constraints involved if
    /// the assumptions are infeasible.
    pub(crate) fn overlay_facts(
        &mut self,
        env: &Env,
        overlay: &mut FactMap,
        root: u32,
        cap: u32,
    ) -> Result<(Facts, Reliance), Reliance> {
        if let Some(rel) = env.infeasible {
            return Err(rel);
        }
        let cap = cap.min(self.config().fact_work.max(1));
        if let Some(f) = overlay.get(root, self.width_of(root)) {
            return Ok(f);
        }
        // The overlay's transfers and the base facts they need share the one cap. A base query
        // the cap stops has counted itself in `capped`; the query then answers `top` and
        // caches nothing, so no later query reads a fact weakened by this one's cap.
        let work0 = self.facts.work;
        let left = move |cx: &Context| {
            cap.saturating_sub(u32::try_from(cx.facts.work - work0).unwrap_or(u32::MAX))
        };
        let base = move |cx: &mut Context, i: u32| {
            let l = left(cx);
            cx.compute_facts_cap(i, l).map(|f| (f, Reliance::NONE))
        };
        let top = move |cx: &Context| (Facts::top(cx.width_of(root)), Reliance::NONE);
        // Only nodes at or above the lowest assumed index can depend on an assumption
        // (children always have lower indices), so the walk stops below it.
        if env.is_empty() || root < env.min {
            return Ok(base(self, root).unwrap_or_else(|| top(self)));
        }
        let min = env.min;
        // Post-order of the part not in the overlay yet. Every node the walk finishes goes into
        // the overlay (those that depend on no assumption with their base facts and no
        // reliance), so a later query stops at it instead of walking below it again.
        self.marks.begin(self.len());
        let mut order = Vec::new();
        let mut stack: Vec<(u32, u8)> = vec![(root, 0)];
        self.marks.test_and_set(root);
        while let Some(top) = stack.last_mut() {
            let (i, k) = *top;
            let n = self.node(i);
            if (k as usize) < n.op.arity() {
                top.1 += 1;
                let c = [n.a, n.b, n.c][k as usize];
                if c >= min && !overlay.contains_key(c) && !self.marks.test_and_set(c) {
                    self.facts.walked += 1;
                    stack.push((c, 0));
                }
            } else {
                stack.pop();
                order.push(i);
            }
        }
        for &i in &order {
            let n = self.node(i);
            let ordering = n.op.as_cmp().and_then(|_| env.relation(n.a, n.b));
            let mut kids = [(Facts::top(Width::W1), Reliance::NONE); 3];
            for (k, c) in n.children().enumerate() {
                // Operands below `min` depend on no assumption: base facts.
                kids[k] = match overlay.get(c, self.width_of(c)) {
                    Some(f) => f,
                    None => match base(self, c) {
                        Some(f) => f,
                        None => return Ok(top(self)),
                    },
                };
            }
            let tainted = env.assumed.contains_key(&i)
                || ordering.is_some()
                || kids[..n.op.arity()].iter().any(|(_, r)| !r.is_none());
            if !tainted {
                let Some(f) = base(self, i) else {
                    return Ok(top(self));
                };
                overlay.insert(i, f);
                continue;
            }
            if left(self) == 0 {
                self.facts.capped += 1;
                return Ok(top(self));
            }
            self.facts.work += 1;
            let mut rel = Reliance::NONE;
            for (_, r) in &kids[..n.op.arity()] {
                rel |= *r;
            }
            let refs: [&Facts; 3] = [&kids[0].0, &kids[1].0, &kids[2].0];
            let mut f = self.transfer_at(i, &self.top_of(i), &refs[..n.op.arity()]);
            if let (Some(op), Some((m, r))) = (n.op.as_cmp(), ordering)
                && let Some(v) = constraint::worlds::decide(m, op)
            {
                let v = BitVec::from_bool(v);
                if !f.contains(&v) {
                    return Err(rel | r);
                }
                // The ordering alone decides it: what the operands' facts rely on is not needed.
                f = Facts::constant(&v);
                rel = r;
            }
            if let Some((a, r)) = env.assumed.get(&i) {
                rel |= *r;
                f = f.meet(a).ok_or(rel)?;
            }
            overlay.insert(i, (f, rel));
        }
        Ok(match overlay.get(root, self.width_of(root)) {
            Some(f) => f,
            None => base(self, root).unwrap_or_else(|| top(self)),
        })
    }

    /// Answers a question from facts. Every `True`/`False` is proved; `Unknown` otherwise.
    pub fn prove(&mut self, q: Query<'_>) -> Result<Truth, Error> {
        Ok(self.prove_inner(q, None)?.truth)
    }

    /// Answers a question from facts under assumptions. Infeasible assumptions prove
    /// anything: every well-formed question is answered `True`.
    pub fn prove_with(&mut self, q: Query<'_>, assumptions: &Assumptions) -> Result<Truth, Error> {
        Ok(self.prove_under(q, assumptions)?.truth)
    }

    /// [`Context::prove_with`], also reporting the constraints the answer relies on.
    pub fn prove_under(&mut self, q: Query<'_>, assumptions: &Assumptions) -> Result<Proof, Error> {
        self.prove_inner(q, Some(assumptions))
    }

    /// Checks a query's arguments (handles, widths, bit indices) before anything else.
    fn validate_query(&self, q: &Query<'_>) -> Result<Vec<Expr>, Error> {
        let same = |a: Width, b: Width| -> Result<(), Error> {
            if a != b {
                return Err(crate::WidthError::Mismatch {
                    left: a.bits(),
                    right: b.bits(),
                }
                .into());
            }
            Ok(())
        };
        Ok(match *q {
            Query::IsZero(e) | Query::IsNonZero(e) | Query::IsConstant(e) => {
                self.width(e)?;
                vec![e]
            }
            Query::Aligned { e, .. }
            | Query::FitsUnsigned { e, .. }
            | Query::FitsSigned { e, .. } => {
                self.width(e)?;
                vec![e]
            }
            Query::Bit { e, bit, .. } => {
                let w = self.width(e)?;
                if bit >= w.bits() {
                    return Err(crate::WidthError::ExtractRange {
                        width: w.bits(),
                        lo: bit,
                        len: 1,
                    }
                    .into());
                }
                vec![e]
            }
            Query::Eq(x, y) | Query::Cmp(_, x, y) => {
                same(self.width(x)?, self.width(y)?)?;
                vec![x, y]
            }
            Query::InURange { e, lo, hi } | Query::InSRange { e, lo, hi } => {
                let w = self.width(e)?;
                same(w, lo.width())?;
                same(w, hi.width())?;
                vec![e]
            }
            Query::MaskRedundant { e, mask } => {
                same(self.width(e)?, mask.width())?;
                vec![e]
            }
            Query::Injective { e, of } | Query::Bijective { e, of } => {
                self.width(e)?;
                self.width(of)?;
                vec![e, of]
            }
        })
    }

    fn prove_inner(&mut self, q: Query<'_>, a: Option<&Assumptions>) -> Result<Proof, Error> {
        let exprs = self.validate_query(&q)?;
        if let Query::Injective { e, of } | Query::Bijective { e, of } = q {
            let onto = matches!(q, Query::Bijective { .. });
            return crate::invert::prove(self, e, of, onto, a);
        }
        let proof = |truth: Truth, relies_on: Reliance| Proof {
            truth,
            relies_on: if truth == Truth::Unknown {
                Reliance::NONE
            } else {
                relies_on
            },
        };
        // An assumed ordering decides a comparison of two expressions directly.
        if let Some(a) = a
            && let Query::Eq(x, y) | Query::Cmp(_, x, y) = q
            && x != y
        {
            let (op, swap) = match q {
                Query::Cmp(op, ..) => op.canonical(),
                _ => (CmpOp::Eq, false),
            };
            let (x, y) = if swap { (y, x) } else { (x, y) };
            a.check_context(self)?;
            let (x, y) = (self.id(x)?, self.id(y)?);
            if let Some((v, r)) = self.assumed_order(a, op, x, y) {
                return Ok(proof(Truth::from_opt(Some(v)), r));
            }
        }
        // Facts of every involved expression (under the assumptions, if any).
        let mut fs = Vec::with_capacity(2);
        let mut rel = Reliance::NONE;
        for e in exprs {
            let f = match a {
                None => self.facts(e)?,
                Some(a) => {
                    let cap = self.config().fact_work;
                    match self.facts_under_cap(e, a, cap)? {
                        Ok((f, r)) => {
                            rel |= r;
                            f
                        }
                        // Infeasible: anything holds.
                        Err(r) => return Ok(proof(Truth::True, r)),
                    }
                }
            };
            fs.push(f);
        }
        let f = fs[0];
        let w = f.width();
        let truth = match q {
            Query::IsZero(_) => {
                Truth::from_opt(decide(CmpOp::Eq, &f, &Facts::constant(&BitVec::zero(w))))
            }
            Query::IsNonZero(_) => {
                !Truth::from_opt(decide(CmpOp::Eq, &f, &Facts::constant(&BitVec::zero(w))))
            }
            Query::IsConstant(_) => {
                if f.as_constant().is_some() {
                    Truth::True
                } else {
                    Truth::Unknown
                }
            }
            Query::Bit { bit, value, .. } => Truth::from_opt(f.known.bit(bit).map(|b| b == value)),
            Query::Eq(x, y) => {
                if x == y {
                    Truth::True
                } else {
                    Truth::from_opt(decide(CmpOp::Eq, &fs[0], &fs[1]))
                }
            }
            Query::Cmp(op, x, y) => {
                let (op, swap) = op.canonical();
                if x == y {
                    Truth::from_opt(Some(matches!(op, CmpOp::Eq | CmpOp::Ule | CmpOp::Sle)))
                } else {
                    let (fx, fy) = if swap {
                        (&fs[1], &fs[0])
                    } else {
                        (&fs[0], &fs[1])
                    };
                    Truth::from_opt(decide(op, fx, fy))
                }
            }
            Query::InURange { lo, hi, .. } => {
                if ule(lo, &f.urange.lo()) && ule(&f.urange.hi(), hi) {
                    Truth::True
                } else if ult(hi, &f.urange.lo()) || ult(&f.urange.hi(), lo) {
                    Truth::False
                } else {
                    Truth::Unknown
                }
            }
            Query::InSRange { lo, hi, .. } => {
                if sle(lo, &f.srange.lo()) && sle(&f.srange.hi(), hi) {
                    Truth::True
                } else if slt(hi, &f.srange.lo()) || slt(&f.srange.hi(), lo) {
                    Truth::False
                } else {
                    Truth::Unknown
                }
            }
            Query::Aligned { log2, .. } => {
                let low = known::low_mask(w, u32::from(log2));
                if known::bv_and(&f.known.maybe_one(), &low).is_zero() {
                    Truth::True
                } else if !known::bv_and(&f.known.known_one(), &low).is_zero() {
                    Truth::False
                } else {
                    Truth::Unknown
                }
            }
            Query::MaskRedundant { mask, .. } => {
                let outside = known::bv_not(mask);
                if known::bv_and(&f.known.maybe_one(), &outside).is_zero() {
                    Truth::True
                } else if !known::bv_and(&f.known.known_one(), &outside).is_zero() {
                    Truth::False
                } else {
                    Truth::Unknown
                }
            }
            Query::FitsUnsigned { bits, .. } => {
                if u32::from(bits) >= u32::from(w.bits()) {
                    Truth::True
                } else {
                    let limit = known::low_mask(w, u32::from(bits));
                    if ule(&f.urange.hi(), &limit) {
                        Truth::True
                    } else if ult(&limit, &f.urange.lo()) {
                        Truth::False
                    } else {
                        Truth::Unknown
                    }
                }
            }
            // Answered above.
            Query::Injective { .. } | Query::Bijective { .. } => Truth::Unknown,
            Query::FitsSigned { bits, .. } => {
                if bits == 0 {
                    Truth::False
                } else if u32::from(bits) >= u32::from(w.bits()) {
                    Truth::True
                } else {
                    // [-(2^(bits-1)), 2^(bits-1) - 1] at width W.
                    let hi = known::low_mask(w, u32::from(bits) - 1);
                    let lo = known::bv_not(&hi);
                    if sle(&lo, &f.srange.lo()) && sle(&f.srange.hi(), &hi) {
                        Truth::True
                    } else if slt(&f.srange.hi(), &lo) || slt(&hi, &f.srange.lo()) {
                        Truth::False
                    } else {
                        Truth::Unknown
                    }
                }
            }
        };
        Ok(proof(truth, rel))
    }
}

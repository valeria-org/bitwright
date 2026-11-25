//! Reasoning about an invertible 64-bit mixer (`H(x, C)` for odd 64-bit `C`):
//!
//! ```text
//! t = C * (x ^ C)          (mod 2^64)
//! H(x, C) = C * (t ^ ((t >> 32) >> (t >> 60)))
//! ```
//!
//! Each round with an odd constant `C` is a bijection on 64-bit words with a closed-form inverse
//! ([`invert_round`]). Guards in obfuscated code often test systems of XORs of rounds sharing one
//! input expression:
//!
//! ```text
//! H(e, C_1) ^ H(e, C_2) == K_1   &&   H(e, C_1) ^ H(e, C_3) == K_2   && ...
//! ```
//!
//! This module provides three deterministic, fail-closed capabilities:
//!
//! 1. **Complete bounded-domain solving** ([`solve_bounded`], [`solve_derived`]): given a
//!    [`System`] of mixer equations over one 64-bit input and an explicit or [`Facts`]-derived
//!    [`Domain`] (narrow zero/sign extensions, bitmasks, unsigned/signed ranges, or injective
//!    wrappers around them), enumerates every solution in canonical order across worker threads
//!    within a deterministic input-evaluation budget (`Unknown` when the domain exceeds the fuel
//!    bound).
//! 2. **Best-effort `u64` witness search** ([`propose_witness`], [`propose_expr_witness`]):
//!    deterministically probes algebraic reductions (GF(2) row elimination and single-round
//!    inversion) followed by structured small/boundary 32-bit and 64-bit spans (and forward images
//!    of small inner-symbol values through bijective input wrappers such as `counter * odd_C`),
//!    returning a verified witness without claiming completeness.
//! 3. **A mixer theory** ([`RoundOp`], [`UnroundOp`], [`registry`], [`simplify_predicate`]):
//!    keeps `H` as a known bijection instead of an unconstrained free symbol so single-round
//!    inversions (`H(x, C) == K <=> x == invert_round(K, C)`), same-key cancellations
//!    (`H(x, C) == H(y, C) <=> x == y`), congruence under `x == y`, GF(2) linear dependencies
//!    across XORed round equations, and small-domain reductions are decided directly.

use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

use crate::expr::OpCode;
use crate::ext::{ExtInverse, ExtOp, ExtSig, InverseArg, Invertible, Registry};
use crate::hash::IdMap;
use crate::{
    Assumptions, BinOp, BitVec, CmpOp, Context, Error, Expr, Facts, KnownBits, UnOp, Width,
};

/// Extension operation name for a forward 64-bit mixer round `@mixer.round(x, key)`.
pub const ROUND_OP_NAME: &str = "mixer.round";

/// Extension operation name for the inverse 64-bit mixer round `@mixer.unround(y, key)`.
pub const UNROUND_OP_NAME: &str = "mixer.unround";

/// Multiplicative inverse of an odd 64-bit integer modulo `2^64`, or `None` if `c` is even.
#[inline(always)]
#[must_use]
pub const fn invert_odd_u64(c: u64) -> Option<u64> {
    if c & 1 == 0 {
        return None;
    }
    let mut inv = c;
    inv = inv.wrapping_mul(2u64.wrapping_sub(c.wrapping_mul(inv)));
    inv = inv.wrapping_mul(2u64.wrapping_sub(c.wrapping_mul(inv)));
    inv = inv.wrapping_mul(2u64.wrapping_sub(c.wrapping_mul(inv)));
    inv = inv.wrapping_mul(2u64.wrapping_sub(c.wrapping_mul(inv)));
    inv = inv.wrapping_mul(2u64.wrapping_sub(c.wrapping_mul(inv)));
    Some(inv)
}

/// Evaluates one 64-bit mixer round `H(x, key) = key * (t ^ ((t >> 32) >> (t >> 60)))`
/// where `t = key * (x ^ key)` (wrapping modulo `2^64`).
#[inline(always)]
#[must_use]
pub const fn eval_round(x: u64, key: u64) -> u64 {
    let t = key.wrapping_mul(x ^ key);
    key.wrapping_mul(t ^ ((t >> 32) >> (t >> 60)))
}

/// Closed-form inverse of [`eval_round`] for an odd 64-bit `key`: returns the unique `x`
/// with `eval_round(x, key) == y`, or `None` when `key` is even.
#[inline(always)]
#[must_use]
pub const fn invert_round(y: u64, key: u64) -> Option<u64> {
    let Some(inv) = invert_odd_u64(key) else {
        return None;
    };
    let u = y.wrapping_mul(inv);
    let r = (u >> 32) >> (u >> 60);
    let t = u ^ r;
    Some(t.wrapping_mul(inv) ^ key)
}

// ---------------------------------------------------------------------------
// Extension operations (`@mixer.round`, `@mixer.unround`)
// ---------------------------------------------------------------------------

/// Host extension operator `@mixer.round(x, key)` representing [`eval_round`].
///
/// When `key` is proved odd (`key & 1 == 1`), the operator declares [`Invertible::Bijective`]
/// in `x` with [`invert_round`] as its exact preimage. By default (`expand == false`), bit-blasting
/// leaves unreduced rounds unsupported rather than expanding two 64-bit multipliers per round;
/// [`RoundOp::expanded`] enables arithmetic expansion when bit-level circuits are desired.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct RoundOp {
    expand: bool,
}

impl RoundOp {
    /// Atomic mixer round operator (no bit-blast expansion).
    #[must_use]
    pub const fn new() -> Self {
        Self { expand: false }
    }

    /// Mixer round operator that expands to primitive 64-bit arithmetic during bit-blasting.
    #[must_use]
    pub const fn expanded() -> Self {
        Self { expand: true }
    }
}

impl ExtOp for RoundOp {
    fn name(&self) -> &str {
        ROUND_OP_NAME
    }

    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [x, k] if x.bits() == 64 && k.bits() == 64 => Ok(ExtSig::new(&[("h", Width::W64)])),
            _ => Err("expected (x: i64, key: i64)".into()),
        }
    }

    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let x = args[0].to_u64().unwrap_or(0);
        let key = args[1].to_u64().unwrap_or(0);
        out[0] = BitVec::wrapping_from_u64(Width::W64, eval_round(x, key));
    }

    fn known_bits(&self, args: &[KnownBits], out: &mut [KnownBits]) {
        if let (Some(x), Some(key)) = (args[0].as_constant(), args[1].as_constant())
            && let (Some(xv), Some(kv)) = (x.to_u64(), key.to_u64())
        {
            out[0] = KnownBits::constant(&BitVec::wrapping_from_u64(
                Width::W64,
                eval_round(xv, kv),
            ));
        } else if args[1].as_constant().is_some_and(|v| v.is_zero()) {
            out[0] = KnownBits::constant(&BitVec::zero(Width::W64));
        }
    }

    fn expand(&self, cx: &mut Context, args: &[Expr]) -> Option<Result<Vec<Expr>, Error>> {
        if !self.expand {
            return None;
        }
        Some((|| {
            let (x, key) = (args[0], args[1]);
            let xk = cx.xor(x, key)?;
            let t = cx.mul(xk, key)?;
            let c32 = cx.constant_u64(Width::W64, 32)?;
            let c60 = cx.constant_u64(Width::W64, 60)?;
            let hi = cx.bin(BinOp::LShr, t, c32)?;
            let top = cx.bin(BinOp::LShr, t, c60)?;
            let sh = cx.bin(BinOp::LShr, hi, top)?;
            let s = cx.xor(t, sh)?;
            let h = cx.mul(s, key)?;
            Ok(vec![h])
        })())
    }

    fn invertible(&self, output: u8, arg: u8, args: &[KnownBits]) -> Invertible {
        if output == 0 && arg == 0 && args.get(1).and_then(|k| k.bit(0)) == Some(true) {
            Invertible::Bijective
        } else {
            Invertible::No
        }
    }

    fn invert(&self, output: u8, arg: u8, args: &[BitVec], value: &BitVec) -> Option<BitVec> {
        if output != 0 || arg != 0 {
            return None;
        }
        let key = args.get(1)?.to_u64()?;
        let y = value.to_u64()?;
        invert_round(y, key).map(|x| BitVec::wrapping_from_u64(Width::W64, x))
    }
}

/// Host extension operator `@mixer.unround(y, key)` representing [`invert_round`] for odd `key`
/// (and returning `0` when `key` is even so the operation is total).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct UnroundOp;

impl UnroundOp {
    /// Inverse mixer round operator.
    #[must_use]
    pub const fn new() -> Self {
        Self
    }
}

impl ExtOp for UnroundOp {
    fn name(&self) -> &str {
        UNROUND_OP_NAME
    }

    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [y, k] if y.bits() == 64 && k.bits() == 64 => Ok(ExtSig::new(&[("x", Width::W64)])),
            _ => Err("expected (y: i64, key: i64)".into()),
        }
    }

    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let y = args[0].to_u64().unwrap_or(0);
        let key = args[1].to_u64().unwrap_or(0);
        out[0] = BitVec::wrapping_from_u64(Width::W64, invert_round(y, key).unwrap_or(0));
    }

    fn invertible(&self, output: u8, arg: u8, args: &[KnownBits]) -> Invertible {
        if output == 0 && arg == 0 && args.get(1).and_then(|k| k.bit(0)) == Some(true) {
            Invertible::Bijective
        } else {
            Invertible::No
        }
    }

    fn invert(&self, output: u8, arg: u8, args: &[BitVec], value: &BitVec) -> Option<BitVec> {
        if output != 0 || arg != 0 {
            return None;
        }
        let key = args.get(1)?.to_u64()?;
        if key & 1 == 0 {
            return None;
        }
        let x = value.to_u64()?;
        Some(BitVec::wrapping_from_u64(Width::W64, eval_round(x, key)))
    }

    fn inverse(&self, _output: u8, _arg: u8) -> Option<ExtInverse> {
        let _ = (ExtInverse::new, InverseArg::Output);
        None
    }
}

/// Builds a [`Registry`] containing [`RoundOp::new`] (`@mixer.round`) and [`UnroundOp::new`]
/// (`@mixer.unround`).
#[must_use]
pub fn registry() -> Registry {
    Registry::builder()
        .register_unchecked(RoundOp::new())
        .expect("valid RoundOp")
        .register_unchecked(UnroundOp::new())
        .expect("valid UnroundOp")
        .build()
}

/// Builds a [`Registry`] containing [`RoundOp::expanded`] (`@mixer.round`) and [`UnroundOp::new`]
/// (`@mixer.unround`).
#[must_use]
pub fn registry_expanded() -> Registry {
    Registry::builder()
        .register_unchecked(RoundOp::expanded())
        .expect("valid RoundOp")
        .register_unchecked(UnroundOp::new())
        .expect("valid UnroundOp")
        .build()
}

/// Builds a mixer round `H(x, key)` in `cx`: uses `@mixer.round(x, key)` if registered in `cx`,
/// otherwise constructs the primitive 64-bit arithmetic round.
pub fn mk_round(cx: &mut Context, x: Expr, key: u64) -> Result<Expr, Error> {
    let key_expr = cx.constant_u64(Width::W64, key)?;
    if let Some(id) = cx.registry.as_deref().and_then(|r| r.id(ROUND_OP_NAME)) {
        return Ok(cx.ext(id, &[x, key_expr])?[0]);
    }
    let xk = cx.xor(x, key_expr)?;
    let t = cx.mul(xk, key_expr)?;
    let c32 = cx.constant_u64(Width::W64, 32)?;
    let c60 = cx.constant_u64(Width::W64, 60)?;
    let hi = cx.bin(BinOp::LShr, t, c32)?;
    let top = cx.bin(BinOp::LShr, t, c60)?;
    let sh = cx.bin(BinOp::LShr, hi, top)?;
    let s = cx.xor(t, sh)?;
    cx.mul(s, key_expr)
}

// ---------------------------------------------------------------------------
// Structural round & equation recognition
// ---------------------------------------------------------------------------

#[inline]
fn const_u64(cx: &Context, id: u32) -> Option<u64> {
    (cx.wid(id) == 64)
        .then(|| cx.const_val(id)?.to_u64())
        .flatten()
}

#[inline]
fn const_side_64(cx: &Context, a: u32, b: u32) -> Option<(u32, u64)> {
    const_u64(cx, a)
        .map(|k| (b, k))
        .or_else(|| const_u64(cx, b).map(|k| (a, k)))
}

fn is_shift_count_of(cx: &Context, mut id: u32, t: u32) -> bool {
    let n = cx.node(id);
    if n.op == OpCode::Zext {
        id = n.a;
    }
    let n = cx.node(id);
    if n.op == OpCode::And
        && let Some((inner, m)) = cx
            .const_val(n.b)
            .and_then(|v| v.to_u64())
            .map(|m| (n.a, m))
            .or_else(|| {
                cx.const_val(n.a)
                    .and_then(|v| v.to_u64())
                    .map(|m| (n.b, m))
            })
    {
        if (m & 15) != 15 {
            return false;
        }
        id = inner;
    }
    let n = cx.node(id);
    if n.op == OpCode::Extract && n.a == t && n.b == 60 && n.width >= 4 {
        return true;
    }
    n.op == OpCode::LShr
        && n.a == t
        && cx.const_val(n.b).and_then(|v| v.to_u64()) == Some(60)
}

fn is_shifted_term_of(cx: &Context, mut shifted: u32, t: u32) -> bool {
    let sn = cx.node(shifted);
    if sn.op == OpCode::Zext && cx.wid(sn.a) == 32 {
        let inner = cx.node(sn.a);
        if inner.op == OpCode::LShr {
            let ext = cx.node(inner.a);
            if ext.op == OpCode::Extract && ext.a == t && ext.b == 32 && ext.width == 32 {
                return is_shift_count_of(cx, inner.b, t);
            }
        }
        shifted = sn.a;
    }
    let shift = cx.node(shifted);
    if shift.op != OpCode::LShr {
        return false;
    }
    let nested = cx.node(shift.a);
    if nested.op == OpCode::LShr && nested.a == t && const_u64(cx, nested.b) == Some(32) {
        return is_shift_count_of(cx, shift.b, t);
    }
    if shift.a == t && matches!(cx.node(shift.b).op, OpCode::Add | OpCode::Or) {
        let add = cx.node(shift.b);
        return const_side_64(cx, add.a, add.b)
            .is_some_and(|(cnt, off)| off == 32 && is_shift_count_of(cx, cnt, t));
    }
    false
}

/// Matches a 64-bit node `id` as `H(input, key)` (either `@mixer.round(input, key)` or any
/// written-out 64-bit arithmetic spelling), returning `(input_id, key)`.
pub(crate) fn match_round_id(cx: &Context, id: u32) -> Option<(u32, u64)> {
    let outer = cx.node(id);
    if outer.width != 64 {
        return None;
    }
    if let Some((_, out_idx)) = outer.op.as_ext() {
        if out_idx != 0 {
            return None;
        }
        let op = cx.registry.as_deref()?.op_at(outer.aux)?;
        if op.name() != ROUND_OP_NAME {
            return None;
        }
        let mut kids = outer.children();
        let x = kids.next()?;
        let k = kids.next()?;
        return Some((x, const_u64(cx, k)?));
    }
    if outer.op != OpCode::Mul {
        return None;
    }
    let (scrambled, key) = const_side_64(cx, outer.a, outer.b)?;
    let xor = cx.node(scrambled);
    if xor.op != OpCode::Xor {
        return None;
    }
    for (t, shifted) in [(xor.a, xor.b), (xor.b, xor.a)] {
        if !is_shifted_term_of(cx, shifted, t) {
            continue;
        }
        let inner = cx.node(t);
        if inner.op != OpCode::Mul {
            continue;
        }
        let Some((masked, inner_key)) = const_side_64(cx, inner.a, inner.b) else {
            continue;
        };
        if inner_key != key {
            continue;
        }
        let inp = cx.node(masked);
        if inp.op != OpCode::Xor {
            continue;
        }
        let Some((source, input_key)) = const_side_64(cx, inp.a, inp.b) else {
            continue;
        };
        if input_key == key {
            return Some((source, key));
        }
    }
    None
}

/// Recognizes `expr` as a 64-bit mixer round `H(input, key)`, returning `(input, key)`.
#[must_use]
pub fn match_round(cx: &Context, expr: Expr) -> Option<(Expr, u64)> {
    let id = cx.id(expr).ok()?;
    let (src, key) = match_round_id(cx, id)?;
    Some((cx.handle(src), key))
}

#[inline]
const fn op_bit(op: OpCode) -> u128 {
    1u128 << (op as u8)
}

/// Rewrites written-out 64-bit mixer rounds below `root` into `@mixer.round(input, key)` calls
/// (requires [`RoundOp`] to be registered in `cx`'s [`Registry`]).
pub fn fold_rounds(cx: &mut Context, root: Expr) -> Result<Expr, Error> {
    let Some(ext_id) = cx.registry.as_deref().and_then(|r| r.id(ROUND_OP_NAME)) else {
        return Ok(root);
    };
    let root_id = cx.id(root)?;
    let order = cx.post_order_ids(&[root_id]);
    let mut map: IdMap<u32, u32> = IdMap::default();
    for id in order {
        let n = cx.node(id);
        let mut kids = [n.a, n.b, n.c];
        let mut changed = false;
        for (slot, c) in n.children().enumerate() {
            if let Some(&nc) = map.get(&c) {
                kids[slot] = nc;
                changed |= nc != c;
            }
        }
        let cur = if changed { cx.rebuild(id, kids)? } else { id };
        let next = if let Some((src, key)) = match_round_id(cx, cur) {
            let k_expr = cx.constant_u64(Width::W64, key)?;
            let call = cx.ext(ext_id, &[cx.handle(src), k_expr])?[0];
            cx.id(call)?
        } else {
            cur
        };
        map.insert(id, next);
    }
    Ok(cx.handle(map[&root_id]))
}

/// Expands `@mixer.round(input, key)` calls below `root` into primitive 64-bit arithmetic.
pub fn expand_rounds(cx: &mut Context, root: Expr) -> Result<Expr, Error> {
    let root_id = cx.id(root)?;
    let order = cx.post_order_ids(&[root_id]);
    let mut map: IdMap<u32, u32> = IdMap::default();
    for id in order {
        let n = cx.node(id);
        let mut kids = [n.a, n.b, n.c];
        let mut changed = false;
        for (slot, c) in n.children().enumerate() {
            if let Some(&nc) = map.get(&c) {
                kids[slot] = nc;
                changed |= nc != c;
            }
        }
        let cur = if changed { cx.rebuild(id, kids)? } else { id };
        let cn = cx.node(cur);
        let is_ext_round = cn.op.as_ext().is_some_and(|(_, o)| o == 0)
            && cx
                .registry
                .as_deref()
                .and_then(|r| r.op_at(cn.aux))
                .is_some_and(|op| op.name() == ROUND_OP_NAME);
        let next = if is_ext_round {
            let mut ch = cn.children();
            let x = cx.handle(ch.next().unwrap());
            let key = cx.handle(ch.next().unwrap());
            let xk = cx.xor(x, key)?;
            let t = cx.mul(xk, key)?;
            let c32 = cx.constant_u64(Width::W64, 32)?;
            let c60 = cx.constant_u64(Width::W64, 60)?;
            let hi = cx.bin(BinOp::LShr, t, c32)?;
            let top = cx.bin(BinOp::LShr, t, c60)?;
            let sh = cx.bin(BinOp::LShr, hi, top)?;
            let s = cx.xor(t, sh)?;
            let h = cx.mul(s, key)?;
            cx.id(h)?
        } else {
            cur
        };
        map.insert(id, next);
    }
    Ok(cx.handle(map[&root_id]))
}

// ---------------------------------------------------------------------------
// Equations, Systems, and GF(2) reduction
// ---------------------------------------------------------------------------

/// One mixer XOR equation `(H(x, k_1) ^ ... ^ H(x, k_m)) & mask == rhs & mask` over a 64-bit `x`.
///
/// Keys are stored sorted with duplicate keys cancelled in pairs (`H(x, k) ^ H(x, k) == 0`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Equation {
    keys: Vec<u64>,
    rhs: u64,
    mask: u64,
}

impl Equation {
    /// Full-width equation `H(x, k_1) ^ ... ^ H(x, k_m) == rhs`.
    #[must_use]
    pub fn new(keys: impl Into<Vec<u64>>, rhs: u64) -> Self {
        Self::masked(keys, rhs, u64::MAX)
    }

    /// Masked equation `(H(x, k_1) ^ ... ^ H(x, k_m)) & mask == rhs & mask`.
    #[must_use]
    pub fn masked(keys: impl Into<Vec<u64>>, rhs: u64, mask: u64) -> Self {
        let mut raw = keys.into();
        raw.sort_unstable();
        let mut dedup = Vec::with_capacity(raw.len());
        for k in raw {
            if dedup.last() == Some(&k) {
                dedup.pop();
            } else {
                dedup.push(k);
            }
        }
        Self {
            keys: dedup,
            rhs: rhs & mask,
            mask,
        }
    }

    /// Canonical sorted keys after pair cancellation.
    #[must_use]
    pub fn keys(&self) -> &[u64] {
        &self.keys
    }

    /// Target right-hand side (`rhs & mask`).
    #[must_use]
    pub const fn rhs(&self) -> u64 {
        self.rhs
    }

    /// Observed bitmask (`u64::MAX` for an unmasked 64-bit equality).
    #[must_use]
    pub const fn mask(&self) -> u64 {
        self.mask
    }

    /// Whether 64-bit input `x` satisfies this equation.
    #[inline]
    #[must_use]
    pub fn holds(&self, x: u64) -> bool {
        let mut acc = 0u64;
        for &k in &self.keys {
            acc ^= eval_round(x, k);
        }
        (acc ^ self.rhs) & self.mask == 0
    }
}

/// Result of exact GF(2) Gaussian elimination and single-round inversion on a [`System`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReducedSystem {
    /// Every 64-bit value satisfies the system (no active constraints remain).
    Tautology,
    /// Provably unsatisfiable over all `2^64` 64-bit values (e.g. a GF(2) XOR contradiction
    /// `0 == K` with `K != 0`, or an odd-key single-round preimage rejected by another equation).
    Unsatisfiable,
    /// Uniquely solved over all `2^64` 64-bit values via an odd-key single-round pivot.
    Unique(u64),
    /// Reduced to linearly independent equations (each remaining equation has `>= 2` keys or an
    /// even single key / partial mask).
    Open(Vec<Equation>),
}

/// Conjunction of [`Equation`]s over one shared 64-bit input expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct System {
    input: Option<Expr>,
    equations: Vec<Equation>,
}

impl System {
    /// System of equations over an unnamed 64-bit input.
    #[must_use]
    pub fn new(equations: impl Into<Vec<Equation>>) -> Self {
        Self {
            input: None,
            equations: equations.into(),
        }
    }

    /// System of equations over the 64-bit expression `input`.
    #[must_use]
    pub fn for_input(input: Expr, equations: impl Into<Vec<Equation>>) -> Self {
        Self {
            input: Some(input),
            equations: equations.into(),
        }
    }

    /// The shared 64-bit input expression, if attached to a [`Context`].
    #[must_use]
    pub const fn input(&self) -> Option<Expr> {
        self.input
    }

    /// Equations in this system.
    #[must_use]
    pub fn equations(&self) -> &[Equation] {
        &self.equations
    }

    /// Whether `x` satisfies every equation in the system.
    #[inline]
    #[must_use]
    pub fn holds(&self, x: u64) -> bool {
        self.equations.iter().all(|eq| eq.holds(x))
    }

    /// Performs exact GF(2) row reduction over the full-width (`mask == u64::MAX`) equations
    /// and applies closed-form [`invert_round`] whenever a 1-key row with an odd key is exposed.
    #[must_use]
    pub fn reduce_gf2(&self) -> ReducedSystem {
        let mut full_rows: Vec<(u128, u64)> = Vec::new();
        let mut all_keys: Vec<u64> = Vec::new();
        let mut partial: Vec<Equation> = Vec::new();

        for eq in &self.equations {
            if eq.mask == 0 {
                continue;
            }
            if eq.keys.is_empty() {
                if eq.rhs & eq.mask != 0 {
                    return ReducedSystem::Unsatisfiable;
                }
                continue;
            }
            if eq.mask == u64::MAX && all_keys.len() + eq.keys.len() <= 128 {
                for &k in &eq.keys {
                    if !all_keys.contains(&k) {
                        all_keys.push(k);
                    }
                }
            } else {
                partial.push(eq.clone());
            }
        }
        all_keys.sort_unstable();
        if all_keys.len() > 128 {
            return ReducedSystem::Open(self.equations.clone());
        }
        for eq in &self.equations {
            if eq.mask != u64::MAX || eq.keys.is_empty() {
                continue;
            }
            let mut row_mask = 0u128;
            for &k in &eq.keys {
                let idx = all_keys.binary_search(&k).unwrap();
                row_mask |= 1u128 << idx;
            }
            full_rows.push((row_mask, eq.rhs));
        }

        // Reduced row-echelon form over GF(2) so 1-key pivots (e.g. from `(a ^ b) + (b ^ c) + a`)
        // are always exposed when in the span.
        let mut rank = 0usize;
        for col in 0..all_keys.len() {
            let bit = 1u128 << col;
            let Some(piv) = (rank..full_rows.len()).find(|&r| full_rows[r].0 & bit != 0) else {
                continue;
            };
            full_rows.swap(rank, piv);
            let (piv_mask, piv_rhs) = full_rows[rank];
            for (r, row) in full_rows.iter_mut().enumerate() {
                if r != rank && row.0 & bit != 0 {
                    row.0 ^= piv_mask;
                    row.1 ^= piv_rhs;
                }
            }
            rank += 1;
        }

        for &(m, rhs) in &full_rows[rank..] {
            if m == 0 && rhs != 0 {
                return ReducedSystem::Unsatisfiable;
            }
        }

        // Check if any row has weight 1 with an odd key: that uniquely determines `x` in O(1)!
        for &(m, rhs) in &full_rows[..rank] {
            if m.count_ones() == 1 {
                let idx = m.trailing_zeros() as usize;
                let key = all_keys[idx];
                if let Some(x0) = invert_round(rhs, key) {
                    if self.holds(x0) {
                        return ReducedSystem::Unique(x0);
                    } else {
                        return ReducedSystem::Unsatisfiable;
                    }
                }
            }
        }

        let mut out = Vec::with_capacity(rank + partial.len());
        for &(mut m, rhs) in &full_rows[..rank] {
            if m == 0 {
                if rhs != 0 {
                    return ReducedSystem::Unsatisfiable;
                }
                continue;
            }
            let mut keys = Vec::with_capacity(m.count_ones() as usize);
            while m != 0 {
                let idx = m.trailing_zeros() as usize;
                keys.push(all_keys[idx]);
                m &= m - 1;
            }
            out.push(Equation {
                keys,
                rhs,
                mask: u64::MAX,
            });
        }
        for eq in partial {
            if !out.contains(&eq) {
                out.push(eq);
            }
        }
        if out.is_empty() {
            ReducedSystem::Tautology
        } else {
            ReducedSystem::Open(out)
        }
    }

    /// Returns the exact 64-bit value of `⊕_{k ∈ keys} H(input, k)` whenever that XOR lies in the
    /// GF(2) row span of this system's full-width equations (`None` if independent of the span).
    #[must_use]
    pub fn implied_rhs(&self, keys: &[u64]) -> Option<u64> {
        let probe = Equation::new(keys.to_vec(), 0);
        if probe.keys.is_empty() {
            return Some(0);
        }
        match self.reduce_gf2() {
            ReducedSystem::Unsatisfiable => None,
            ReducedSystem::Tautology => None,
            ReducedSystem::Unique(x0) => {
                let mut acc = 0u64;
                for &k in &probe.keys {
                    acc ^= eval_round(x0, k);
                }
                Some(acc)
            }
            ReducedSystem::Open(rref) => implied_rhs_from_rref(&rref, &probe.keys),
        }
    }
}

fn implied_rhs_from_rref(rref: &[Equation], target_keys: &[u64]) -> Option<u64> {
    let mut cur = target_keys.to_vec();
    let mut acc_rhs = 0u64;
    for row in rref {
        if row.mask != u64::MAX || row.keys.is_empty() {
            continue;
        }
        let piv = row.keys[0];
        if cur.binary_search(&piv).is_ok() {
            acc_rhs ^= row.rhs;
            let mut merged = Vec::with_capacity(cur.len() + row.keys.len());
            let (mut i, mut j) = (0usize, 0usize);
            while i < cur.len() && j < row.keys.len() {
                match cur[i].cmp(&row.keys[j]) {
                    std::cmp::Ordering::Less => {
                        merged.push(cur[i]);
                        i += 1;
                    }
                    std::cmp::Ordering::Greater => {
                        merged.push(row.keys[j]);
                        j += 1;
                    }
                    std::cmp::Ordering::Equal => {
                        i += 1;
                        j += 1;
                    }
                }
            }
            merged.extend_from_slice(&cur[i..]);
            merged.extend_from_slice(&row.keys[j..]);
            cur = merged;
        }
    }
    cur.is_empty().then_some(acc_rhs)
}

/// Parses a single 64-bit zero-equality term `term & mask == target & mask` into `(input_id, Equation)`.
/// Handles `H(x,a) ^ H(x,b) ^ K`, `(H(x,a) ^ H(x,b)) + K`, `K - (H(x,a) ^ H(x,b))`, and `H(x,a) == K`.
fn parse_xor_term(cx: &Context, mut term: u32, mut target: u64, mask: u64) -> Option<(u32, Equation)> {
    if cx.wid(term) != 64 || mask == 0 {
        return None;
    }
    // Peel outer `+ K` or `- K` when `mask` is a low-bit mask `2^b - 1` (ring homomorphism mod 2^b,
    // including full 64-bit `u64::MAX`).
    let is_low_mask = mask == u64::MAX || (mask & (mask.wrapping_add(1))) == 0;
    if is_low_mask {
        for _ in 0..4 {
            let n = cx.node(term);
            match n.op {
                OpCode::Add => {
                    if let Some((inner, k)) = const_side_64(cx, n.a, n.b) {
                        target = target.wrapping_sub(k) & mask;
                        term = inner;
                    } else {
                        break;
                    }
                }
                OpCode::Sub => {
                    if let Some(k) = const_u64(cx, n.b) {
                        target = target.wrapping_add(k) & mask;
                        term = n.a;
                    } else if let Some(k) = const_u64(cx, n.a) {
                        target = k.wrapping_sub(target) & mask;
                        term = n.b;
                    } else {
                        break;
                    }
                }
                OpCode::Neg => {
                    target = target.wrapping_neg() & mask;
                    term = n.a;
                }
                _ => break,
            }
        }
    }

    let mut stack = vec![term];
    let mut salt = 0u64;
    let mut keys = Vec::new();
    let mut source: Option<u32> = None;
    let mut steps = 0usize;
    while let Some(cur) = stack.pop() {
        steps += 1;
        if steps > 64 {
            return None;
        }
        if let Some(c) = const_u64(cx, cur) {
            salt ^= c;
            continue;
        }
        if let Some((src, key)) = match_round_id(cx, cur) {
            if let Some(prev) = source {
                if prev != src {
                    return None;
                }
            } else {
                source = Some(src);
            }
            keys.push(key);
            continue;
        }
        let n = cx.node(cur);
        match n.op {
            OpCode::Xor => {
                stack.push(n.a);
                stack.push(n.b);
            }
            OpCode::Not => {
                salt ^= u64::MAX;
                stack.push(n.a);
            }
            _ => return None,
        }
    }
    let src = source?;
    let eq = Equation::masked(keys, (target ^ salt) & mask, mask);
    if eq.keys.is_empty() {
        return None;
    }
    Some((src, eq))
}

/// Extracts `(input_id, Equation)` atoms implied when `id` evaluates to `want` (`true` or `false`).
fn collect_implied_equations(
    cx: &Context,
    root: u32,
    want: bool,
    out: &mut Vec<(u32, Equation)>,
) {
    let mut stack = vec![(root, want)];
    let mut seen: IdMap<(u32, bool), ()> = IdMap::default();
    while let Some((id, w)) = stack.pop() {
        if seen.len() > 2048 || seen.insert((id, w), ()).is_some() {
            continue;
        }
        let n = cx.node(id);
        match n.op {
            OpCode::Not if n.width == 1 => stack.push((n.a, !w)),
            OpCode::And if w => {
                stack.push((n.a, true));
                stack.push((n.b, true));
            }
            OpCode::Or if !w => {
                stack.push((n.a, false));
                stack.push((n.b, false));
            }
            OpCode::Zext | OpCode::Sext if w => stack.push((n.a, true)),
            OpCode::Extract if n.b == 0 && cx.wid(n.a) == 1 => stack.push((n.a, w)),
            OpCode::Eq | OpCode::Ne => {
                let is_eq = (n.op == OpCode::Eq) == w;
                if !is_eq {
                    // `x != 0` on a zero-extended 1-bit or masked boolean guard `(zext(g) != 0)`
                    if cx.const_val(n.b).is_some_and(|v| v.is_zero()) {
                        stack.push((n.a, true));
                    } else if cx.const_val(n.a).is_some_and(|v| v.is_zero()) {
                        stack.push((n.b, true));
                    }
                    continue;
                }
                if cx.wid(n.a) == 1 {
                    if let Some(b) = cx.const_val(n.b) {
                        stack.push((n.a, !b.is_zero()));
                        continue;
                    }
                    if let Some(a) = cx.const_val(n.a) {
                        stack.push((n.b, !a.is_zero()));
                        continue;
                    }
                }
                if cx.wid(n.a) != 64 {
                    if let Some(c) = cx.const_val(n.b) {
                        if c.is_zero() && matches!(cx.node(n.a).op, OpCode::Zext | OpCode::Or) {
                            if cx.node(n.a).op == OpCode::Zext {
                                stack.push((cx.node(n.a).a, false));
                            } else {
                                stack.push((cx.node(n.a).a, false));
                                stack.push((cx.node(n.a).b, false));
                            }
                        } else if c.to_u64() == Some(1) && cx.node(n.a).op == OpCode::Zext {
                            stack.push((cx.node(n.a).a, true));
                        }
                    }
                    continue;
                }
                if let Some((subject, target)) = const_side_64(cx, n.a, n.b) {
                    if target == 0 && cx.node(subject).op == OpCode::Zext {
                        stack.push((cx.node(subject).a, false));
                        continue;
                    }
                    if target == 1 && cx.node(subject).op == OpCode::Zext && cx.wid(cx.node(subject).a) == 1 {
                        stack.push((cx.node(subject).a, true));
                        continue;
                    }
                    // Disjunction packed into `|`: `(t1 | t2 | ...) == target` requires every
                    // leaf to vanish on `!target` (in particular, `== 0` requires every leaf `== 0`).
                    if cx.node(subject).op == OpCode::Or {
                        let clear_mask = !target;
                        if clear_mask != 0 {
                            let mut or_stack = vec![subject];
                            while let Some(leaf) = or_stack.pop() {
                                let ln = cx.node(leaf);
                                if ln.op == OpCode::Or {
                                    or_stack.push(ln.a);
                                    or_stack.push(ln.b);
                                } else {
                                    let (term, obs) = if ln.op == OpCode::And {
                                        const_side_64(cx, ln.a, ln.b).unwrap_or((leaf, u64::MAX))
                                    } else {
                                        (leaf, u64::MAX)
                                    };
                                    if let Some(item) = parse_xor_term(cx, term, 0, obs & clear_mask)
                                    {
                                        out.push(item);
                                    }
                                }
                            }
                        }
                    } else {
                        let (term, obs) = if cx.node(subject).op == OpCode::And {
                            let an = cx.node(subject);
                            const_side_64(cx, an.a, an.b).unwrap_or((subject, u64::MAX))
                        } else {
                            (subject, u64::MAX)
                        };
                        if target & !obs == 0
                            && let Some(item) = parse_xor_term(cx, term, target, obs)
                        {
                            out.push(item);
                        }
                    }
                } else {
                    // Two non-constant 64-bit sides `lhs == rhs` <-> `(lhs ^ rhs) == 0`
                    let mut keys = Vec::new();
                    let mut salt = 0u64;
                    let mut source: Option<u32> = None;
                    let mut ok = true;
                    let mut xor_stack = vec![n.a, n.b];
                    let mut steps = 0usize;
                    while let Some(cur) = xor_stack.pop() {
                        steps += 1;
                        if steps > 64 {
                            ok = false;
                            break;
                        }
                        if let Some(c) = const_u64(cx, cur) {
                            salt ^= c;
                            continue;
                        }
                        if let Some((src, key)) = match_round_id(cx, cur) {
                            if let Some(prev) = source {
                                if prev != src {
                                    ok = false;
                                    break;
                                }
                            } else {
                                source = Some(src);
                            }
                            keys.push(key);
                            continue;
                        }
                        let cn = cx.node(cur);
                        if cn.op == OpCode::Xor {
                            xor_stack.push(cn.a);
                            xor_stack.push(cn.b);
                        } else {
                            ok = false;
                            break;
                        }
                    }
                    if ok
                        && let Some(src) = source
                    {
                        let eq = Equation::new(keys, salt);
                        if !eq.keys.is_empty() {
                            out.push((src, eq));
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

fn group_by_input(cx: &Context, raw: Vec<(u32, Equation)>) -> Vec<System> {
    let mut order: Vec<u32> = Vec::new();
    let mut by_src: IdMap<u32, Vec<Equation>> = IdMap::default();
    for (src, eq) in raw {
        let entry = by_src.entry(src).or_insert_with(|| {
            order.push(src);
            Vec::new()
        });
        if !entry.contains(&eq) {
            entry.push(eq);
        }
    }
    order.sort_unstable();
    order
        .into_iter()
        .filter_map(|src| {
            let eqs = by_src.remove(&src)?;
            (!eqs.is_empty()).then(|| System::for_input(cx.handle(src), eqs))
        })
        .collect()
}

/// Extracts all mixer equation [`System`]s implied by `predicate == true` (together with any
/// `assumptions`), grouped by shared 64-bit `input` expression in deterministic ID order.
pub fn extract_systems(
    cx: &Context,
    predicate: Expr,
    assumptions: Option<&Assumptions>,
) -> Result<Vec<System>, Error> {
    let root = cx.id(predicate)?;
    let mut raw = Vec::new();
    collect_implied_equations(cx, root, true, &mut raw);
    if let Some(a) = assumptions {
        a.check_context(cx)?;
        for (_, e, facts) in a.constraints() {
            let id = cx.id(e)?;
            if let Some(c) = facts.as_constant() {
                if cx.wid(id) == 1 {
                    collect_implied_equations(cx, id, !c.is_zero(), &mut raw);
                } else if cx.wid(id) == 64
                    && let Some(target) = c.to_u64()
                    && let Some(item) = parse_xor_term(cx, id, target, u64::MAX)
                {
                    raw.push(item);
                }
            }
        }
    }
    Ok(group_by_input(cx, raw))
}

fn post_order_readonly(cx: &Context, root_id: u32) -> Vec<u32> {
    let mut visited: IdMap<u32, bool> = IdMap::default();
    let mut stack = vec![(root_id, false)];
    let mut order = Vec::new();
    while let Some((id, exited)) = stack.pop() {
        if exited {
            order.push(id);
            continue;
        }
        if visited.insert(id, true).is_some() {
            continue;
        }
        stack.push((id, true));
        let mut kids: [u32; 3] = [0; 3];
        let mut n_kids = 0usize;
        for c in cx.node(id).children() {
            kids[n_kids] = c;
            n_kids += 1;
        }
        for &c in kids[..n_kids].iter().rev() {
            if !visited.contains_key(&c) {
                stack.push((c, false));
            }
        }
    }
    order
}

/// Scans an arbitrary expression DAG (such as a 64-bit jump-target expression containing guarded
/// branches) and returns every mixer [`System`] tested by comparisons in `root`, in deterministic
/// topological order.
pub fn extract_all_systems(cx: &Context, root: Expr) -> Result<Vec<System>, Error> {
    let root_id = cx.id(root)?;
    let order = post_order_readonly(cx, root_id);
    // Collect maximal boolean/casted guard cones (`And`, `Zext`, `Eq`, `Ne`) so conjoined equations
    // on the same input stay grouped together.
    let mut raw = Vec::new();
    for &id in &order {
        let n = cx.node(id);
        if matches!(n.op, OpCode::Eq | OpCode::Ne) {
            collect_implied_equations(cx, id, true, &mut raw);
        }
    }
    Ok(group_by_input(cx, raw))
}

// ---------------------------------------------------------------------------
// Domains & Automatic Facts Derivation
// ---------------------------------------------------------------------------

/// Forward deterministic operation mapping an inner narrow/bounded domain into a 64-bit mixer input.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ForwardOp {
    /// Zero-extension from `bits` (`1..64`) to `to_bits`.
    Zext { from: u16, to: u16 },
    /// Sign-extension from `bits` (`1..64`) to `to_bits`.
    Sext { from: u16, to: u16 },
    /// Bitwise NOT at `bits`.
    Not { bits: u16 },
    /// Two's-complement negation at `bits`.
    Neg { bits: u16 },
    /// Byte-swap at `bits`.
    Bswap { bits: u16 },
    /// Bit-reversal at `bits`.
    BitRev { bits: u16 },
    /// Wrapping addition `(v + k) mod 2^bits`.
    Add { bits: u16, k: u64 },
    /// Wrapping subtraction `(v - k) mod 2^bits`.
    Sub { bits: u16, k: u64 },
    /// Wrapping subtraction `(k - v) mod 2^bits`.
    SubFrom { bits: u16, k: u64 },
    /// Bitwise XOR `(v ^ k)`.
    Xor { bits: u16, k: u64 },
    /// Bitwise AND `(v & k)`.
    And { bits: u16, k: u64 },
    /// Bitwise OR `(v | k)`.
    Or { bits: u16, k: u64 },
    /// Wrapping multiplication `(v * k) mod 2^bits`.
    Mul { bits: u16, k: u64 },
    /// Logical left shift `(v << k) mod 2^bits`.
    Shl { bits: u16, k: u32 },
    /// Logical right shift `v >> k` at `bits`.
    LShr { bits: u16, k: u32 },
    /// Rotate-left by `k` at `bits`.
    RotL { bits: u16, k: u32 },
    /// Rotate-right by `k` at `bits`.
    RotR { bits: u16, k: u32 },
}

impl ForwardOp {
    #[inline(always)]
    fn apply(self, v: u64) -> u64 {
        let mask_of = |b: u16| if b >= 64 { u64::MAX } else { (1u64 << b) - 1 };
        match self {
            Self::Zext { from, to } => (v & mask_of(from)) & mask_of(to),
            Self::Sext { from, to } => {
                let m = mask_of(from);
                let x = v & m;
                let sign = 1u64 << (from - 1);
                let ext = if x & sign != 0 { x | !m } else { x };
                ext & mask_of(to)
            }
            Self::Not { bits } => (!v) & mask_of(bits),
            Self::Neg { bits } => v.wrapping_neg() & mask_of(bits),
            Self::Bswap { bits } => v.swap_bytes() >> (64 - bits),
            Self::BitRev { bits } => v.reverse_bits() >> (64 - bits),
            Self::Add { bits, k } => v.wrapping_add(k) & mask_of(bits),
            Self::Sub { bits, k } => v.wrapping_sub(k) & mask_of(bits),
            Self::SubFrom { bits, k } => k.wrapping_sub(v) & mask_of(bits),
            Self::Xor { bits, k } => (v ^ k) & mask_of(bits),
            Self::And { bits, k } => (v & k) & mask_of(bits),
            Self::Or { bits, k } => (v | k) & mask_of(bits),
            Self::Mul { bits, k } => v.wrapping_mul(k) & mask_of(bits),
            Self::Shl { bits, k } => {
                if k >= u32::from(bits) {
                    0
                } else {
                    (v << k) & mask_of(bits)
                }
            }
            Self::LShr { bits, k } => {
                if k >= u32::from(bits) {
                    0
                } else {
                    (v & mask_of(bits)) >> k
                }
            }
            Self::RotL { bits, k } => {
                let w = u32::from(bits);
                let n = k % w;
                let x = v & mask_of(bits);
                if n == 0 {
                    x
                } else {
                    ((x << n) | (x >> (w - n))) & mask_of(bits)
                }
            }
            Self::RotR { bits, k } => {
                let w = u32::from(bits);
                let n = k % w;
                let x = v & mask_of(bits);
                if n == 0 {
                    x
                } else {
                    ((x >> n) | (x << (w - n))) & mask_of(bits)
                }
            }
        }
    }
}

/// Exact domain of 64-bit candidate inputs for complete mixer solving.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Domain {
    /// Empty domain (0 elements).
    Empty,
    /// Unsigned strided interval `lo, lo + stride, ..., hi` (`stride >= 1`, `lo <= hi`,
    /// `(hi - lo) % stride == 0`).
    Range { lo: u64, hi: u64, stride: u64 },
    /// Contiguous signed 64-bit interval `[lo, hi]` (`lo <= hi`), wrapping from `-1` (`u64::MAX`)
    /// to `0` when `lo < 0 <= hi` (e.g. sign-extended `i32`).
    SignedRange { lo: i64, hi: i64 },
    /// Bitmask domain `{ fixed_ones | deposit(idx, free_mask) : 0 <= idx < 2^popcnt(free_mask) }`.
    Masked { free_mask: u64, fixed_ones: u64 },
    /// Explicit sorted, deduplicated candidate values.
    Values(Vec<u64>),
    /// Exact forward image of an inner domain under a sequence of deterministic [`ForwardOp`]s.
    Mapped {
        base: Box<Domain>,
        ops: Vec<ForwardOp>,
    },
}

#[inline(always)]
fn pdep_u64(mut val: u64, mut mask: u64) -> u64 {
    let mut res = 0u64;
    while mask != 0 {
        let low = mask.isolate_lowest_one();
        if val & 1 != 0 {
            res |= low;
        }
        val >>= 1;
        mask &= mask - 1;
    }
    res
}

impl Domain {
    /// Empty domain.
    #[must_use]
    pub const fn empty() -> Self {
        Self::Empty
    }

    /// Full 64-bit domain (`2^64` elements).
    #[must_use]
    pub const fn full() -> Self {
        Self::Range {
            lo: 0,
            hi: u64::MAX,
            stride: 1,
        }
    }

    /// Unsigned low-bit domain `0 .. 2^bits` (`0 <= bits <= 64`, e.g. `low_bits(32)` for `zext(u32)`).
    #[must_use]
    pub const fn low_bits(bits: u8) -> Self {
        if bits == 0 {
            Self::Range {
                lo: 0,
                hi: 0,
                stride: 1,
            }
        } else if bits >= 64 {
            Self::full()
        } else {
            Self::Range {
                lo: 0,
                hi: (1u64 << bits) - 1,
                stride: 1,
            }
        }
    }

    /// Sign-extended `bits`-bit domain `[-2^(bits-1), 2^(bits-1) - 1]` (`1 <= bits <= 64`,
    /// e.g. `signed_bits(32)` for `sext<64>(i32)`).
    #[must_use]
    pub const fn signed_bits(bits: u8) -> Self {
        if bits == 0 {
            Self::Empty
        } else if bits >= 64 {
            Self::full()
        } else {
            let half = 1i64 << (bits - 1);
            Self::SignedRange {
                lo: -half,
                hi: half - 1,
            }
        }
    }

    /// Inclusive unsigned interval `[lo, hi]`.
    #[must_use]
    pub const fn unsigned_range(lo: u64, hi: u64) -> Self {
        if lo > hi {
            Self::Empty
        } else {
            Self::Range { lo, hi, stride: 1 }
        }
    }

    /// Unsigned strided interval `lo, lo + stride, ..., <= hi` (`stride >= 1`).
    #[must_use]
    pub const fn strided_range(lo: u64, hi: u64, stride: u64) -> Self {
        if lo > hi {
            return Self::Empty;
        }
        if stride <= 1 {
            return Self::Range { lo, hi, stride: 1 };
        }
        let steps = (hi - lo) / stride;
        Self::Range {
            lo,
            hi: lo + steps * stride,
            stride,
        }
    }

    /// Inclusive signed 64-bit interval `[lo, hi]`.
    #[must_use]
    pub const fn signed_range(lo: i64, hi: i64) -> Self {
        if lo > hi {
            Self::Empty
        } else if lo >= 0 || hi < 0 {
            Self::Range {
                lo: lo as u64,
                hi: hi as u64,
                stride: 1,
            }
        } else {
            Self::SignedRange { lo, hi }
        }
    }

    /// Bitmask domain `{ fixed_ones | (x & free_mask) }`. Returns [`Domain::Empty`] if `fixed_ones`
    /// overlaps `free_mask` inconsistently? (`fixed_ones` bits inside `free_mask` are cleared into
    /// `free_mask`).
    #[must_use]
    pub const fn bitmask(free_mask: u64, fixed_ones: u64) -> Self {
        let fixed = fixed_ones & !free_mask;
        if free_mask == 0 {
            Self::Range {
                lo: fixed,
                hi: fixed,
                stride: 1,
            }
        } else if (free_mask & (free_mask.wrapping_add(1))) == 0 && fixed == 0 {
            Self::Range {
                lo: 0,
                hi: free_mask,
                stride: 1,
            }
        } else {
            Self::Masked {
                free_mask,
                fixed_ones: fixed,
            }
        }
    }

    /// Domain of an explicit set of candidate 64-bit values (sorted and deduplicated).
    #[must_use]
    pub fn values(iter: impl IntoIterator<Item = u64>) -> Self {
        let mut v: Vec<u64> = iter.into_iter().collect();
        if v.is_empty() {
            return Self::Empty;
        }
        v.sort_unstable();
        v.dedup();
        Self::Values(v)
    }

    /// Exact cardinality (`0 ..= 2^64`).
    #[must_use]
    pub fn len(&self) -> u128 {
        match self {
            Self::Empty => 0,
            Self::Range { lo, hi, stride } => u128::from((hi - lo) / (*stride).max(1)) + 1,
            Self::SignedRange { lo, hi } => (i128::from(*hi) - i128::from(*lo) + 1) as u128,
            Self::Masked { free_mask, .. } => 1u128 << free_mask.count_ones(),
            Self::Values(v) => v.len() as u128,
            Self::Mapped { base, .. } => base.len(),
        }
    }

    /// Whether the domain has zero elements.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the `idx`-th element (`0 <= idx < self.len()`) in deterministic domain order.
    #[inline]
    #[must_use]
    pub fn nth(&self, idx: u64) -> u64 {
        match self {
            Self::Empty => 0,
            Self::Range { lo, stride, .. } => lo.wrapping_add(idx.wrapping_mul(*stride)),
            Self::SignedRange { lo, .. } => (*lo as u64).wrapping_add(idx),
            Self::Masked {
                free_mask,
                fixed_ones,
            } => *fixed_ones | pdep_u64(idx, *free_mask),
            Self::Values(v) => v[idx as usize],
            Self::Mapped { base, ops } => {
                let mut val = base.nth(idx);
                for &op in ops {
                    val = op.apply(val);
                }
                val
            }
        }
    }

    /// Derives the tightest enclosing [`Domain`] from `Facts` on a `<= 64`-bit expression
    /// (zero-extended into 64 bits when narrower than 64 bits).
    #[must_use]
    pub fn from_facts(facts: &Facts) -> Self {
        let w = facts.width().bits();
        if w == 0 || w > 64 {
            return Self::full();
        }
        let full = u64::MAX >> (64 - w);
        let kb = facts.known();
        let known_mask = (kb.known().limbs()[0] & full) | !full;
        let fixed_ones = kb.known_one().limbs()[0] & full;
        let free_mask = !known_mask;
        let d_mask = Self::bitmask(free_mask, fixed_ones);

        let ur = facts.urange();
        let ulo = ur.lo().limbs()[0] & full;
        let uhi = ur.hi().limbs()[0] & full;
        let stride = ur.stride().max(1);
        let d_urange = Self::strided_range(ulo, uhi, stride);

        let mut best = if d_urange.len() <= d_mask.len() {
            d_urange
        } else {
            d_mask
        };

        if w == 64 {
            let sr = facts.srange();
            if let (Some(slo), Some(shi)) = (sr.lo().to_i128(), sr.hi().to_i128())
                && let (Ok(slo64), Ok(shi64)) = (i64::try_from(slo), i64::try_from(shi))
            {
                let d_srange = Self::signed_range(slo64, shi64);
                if d_srange.len() < best.len() {
                    best = d_srange;
                }
            }
        } else {
            // Narrow signed range at width `w < 64` (zero-extended in `Facts`): if `srange`
            // crosses sign bit `w - 1`, `Mapped` over `Sext`/`Zext` can be smaller than `URange`.
            let sr = facts.srange();
            if let (Some(slo), Some(shi)) = (sr.lo().to_i128(), sr.hi().to_i128()) {
                let s_cnt = (shi - slo + 1).max(0) as u128;
                if s_cnt < best.len() {
                    let lo_mod = (slo as u64) & full;
                    best = Self::Mapped {
                        base: Box::new(Self::Range {
                            lo: 0,
                            hi: (s_cnt - 1) as u64,
                            stride: 1,
                        }),
                        ops: vec![ForwardOp::Add { bits: w, k: lo_mod }],
                    };
                }
            }
        }
        best
    }

    /// Derives the tightest sound [`Domain`] for 64-bit `input` in `cx` under `assumptions`,
    /// also peeling deterministic unary/constant-parameter chains (`counter * odd_C`, `sext(x)`,
    /// `zext(x)`, `(y & M) + K`, etc.) whenever an inner subterm has a strictly smaller domain.
    pub fn derive(
        cx: &mut Context,
        input: Expr,
        assumptions: Option<&Assumptions>,
    ) -> Result<Self, Error> {
        let id = cx.id(input)?;
        if cx.wid(id) > 64 {
            return Ok(Self::full());
        }
        let refreshed = assumptions.map(|a| a.refreshed(cx)).transpose()?;
        let a = refreshed.as_deref();
        let facts_of = |cx: &mut Context, node_id: u32| -> Result<Option<Facts>, Error> {
            let e = cx.handle(node_id);
            match a {
                None => Ok(Some(cx.facts(e)?)),
                Some(assump) => {
                    let cap = cx.config().fact_work;
                    match cx.facts_under_cap(e, assump, cap)? {
                        Ok((f, _)) => Ok(Some(f)),
                        Err(_) => Ok(None), // Infeasible assumptions -> empty domain!
                    }
                }
            }
        };

        let Some(top_facts) = facts_of(cx, id)? else {
            return Ok(Self::Empty);
        };
        let mut best = Self::from_facts(&top_facts);

        // Peel up to 16 single-operand deterministic steps (`input = f_0(f_1(...(cur)))`).
        let mut cur = id;
        let mut rev_ops: Vec<ForwardOp> = Vec::new();
        for _ in 0..16 {
            if best.len() <= 1 {
                break;
            }
            let Some((inner, op)) = peel_forward_step(cx, cur) else {
                break;
            };
            rev_ops.push(op);
            cur = inner;
            let Some(inner_facts) = facts_of(cx, cur)? else {
                return Ok(Self::Empty);
            };
            let d_inner = Self::from_facts(&inner_facts);
            if d_inner.len() < best.len() {
                let mut ops = rev_ops.clone();
                ops.reverse();
                best = Self::Mapped {
                    base: Box::new(d_inner),
                    ops,
                };
            }
        }
        Ok(best)
    }
}

fn peel_forward_step(cx: &Context, id: u32) -> Option<(u32, ForwardOp)> {
    let n = cx.node(id);
    let bits = n.width;
    if bits == 0 || bits > 64 {
        return None;
    }
    let const_child = |a: u32, b: u32| -> Option<(u32, u64, bool)> {
        if let Some(c) = cx.const_val(b).and_then(|v| v.to_u64()) {
            Some((a, c, true))
        } else {
            cx.const_val(a)
                .and_then(|v| v.to_u64())
                .map(|c| (b, c, false))
        }
    };
    match n.op {
        OpCode::Zext => Some((
            n.a,
            ForwardOp::Zext {
                from: cx.wid(n.a),
                to: bits,
            },
        )),
        OpCode::Sext => Some((
            n.a,
            ForwardOp::Sext {
                from: cx.wid(n.a),
                to: bits,
            },
        )),
        OpCode::Not => Some((n.a, ForwardOp::Not { bits })),
        OpCode::Neg => Some((n.a, ForwardOp::Neg { bits })),
        OpCode::Bswap => Some((n.a, ForwardOp::Bswap { bits })),
        OpCode::BitRev => Some((n.a, ForwardOp::BitRev { bits })),
        OpCode::Add => {
            let (x, k, _) = const_child(n.a, n.b)?;
            Some((x, ForwardOp::Add { bits, k }))
        }
        OpCode::Sub => {
            let (x, k, x_lhs) = const_child(n.a, n.b)?;
            Some((
                x,
                if x_lhs {
                    ForwardOp::Sub { bits, k }
                } else {
                    ForwardOp::SubFrom { bits, k }
                },
            ))
        }
        OpCode::Xor => {
            let (x, k, _) = const_child(n.a, n.b)?;
            Some((x, ForwardOp::Xor { bits, k }))
        }
        OpCode::And => {
            let (x, k, _) = const_child(n.a, n.b)?;
            Some((x, ForwardOp::And { bits, k }))
        }
        OpCode::Or => {
            let (x, k, _) = const_child(n.a, n.b)?;
            Some((x, ForwardOp::Or { bits, k }))
        }
        OpCode::Mul => {
            let (x, k, _) = const_child(n.a, n.b)?;
            Some((x, ForwardOp::Mul { bits, k }))
        }
        OpCode::Shl => {
            let k = cx.const_val(n.b)?.to_u64()?;
            Some((
                n.a,
                ForwardOp::Shl {
                    bits,
                    k: k.min(64) as u32,
                },
            ))
        }
        OpCode::LShr => {
            let k = cx.const_val(n.b)?.to_u64()?;
            Some((
                n.a,
                ForwardOp::LShr {
                    bits,
                    k: k.min(64) as u32,
                },
            ))
        }
        OpCode::RotL => {
            let k = cx.const_val(n.b)?.to_u64()?;
            Some((
                n.a,
                ForwardOp::RotL {
                    bits,
                    k: (k % u64::from(bits)) as u32,
                },
            ))
        }
        OpCode::RotR => {
            let k = cx.const_val(n.b)?.to_u64()?;
            Some((
                n.a,
                ForwardOp::RotR {
                    bits,
                    k: (k % u64::from(bits)) as u32,
                },
            ))
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Complete Bounded-Domain Solver (Item 1)
// ---------------------------------------------------------------------------

/// Fuel and parallelism configuration for [`solve_bounded`] and [`solve_derived`].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Limits {
    /// Maximum domain elements to evaluate (`1 << 32` covers a full 32-bit `zext`/`sext` scan).
    pub max_inputs: u64,
    /// Maximum satisfying values retained before returning [`Incomplete::TooManySolutions`].
    pub max_solutions: usize,
    /// Worker threads to use (`0`: [`std::thread::available_parallelism`], `1`: single-threaded).
    /// Affects wall-clock speed only; results and completeness are strictly independent of it.
    pub threads: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_inputs: 1 << 24,
            max_solutions: 256,
            threads: 0,
        }
    }
}

setters!(Limits {
    with_max_inputs: max_inputs: u64,
    with_max_solutions: max_solutions: usize,
    with_threads: threads: usize,
});

/// Why a bounded-domain mixer query could not return a complete solution set.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Incomplete {
    /// The domain size (`required`) exceeds [`Limits::max_inputs`] (`budget`).
    FuelExhausted { required: u128, budget: u64 },
    /// More than [`Limits::max_solutions`] solutions exist in the domain.
    TooManySolutions { limit: usize },
}

/// Result of [`solve_bounded`] / [`solve_derived`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolveOutcome {
    /// Every satisfying 64-bit input value in the domain (sorted, deduplicated), together with
    /// the deterministic count of domain inputs evaluated.
    Complete { solutions: Vec<u64>, evaluated: u64 },
    /// Undecided within the deterministic limits (fail-closed: never claims completeness).
    Unknown(Incomplete),
}

impl SolveOutcome {
    /// Whether the solution set is provably complete over the domain.
    #[must_use]
    pub const fn is_complete(&self) -> bool {
        matches!(self, Self::Complete { .. })
    }

    /// Returns the complete slice of solutions if decided, or `None` if `Unknown`.
    #[must_use]
    pub fn solutions(&self) -> Option<&[u64]> {
        match self {
            Self::Complete { solutions, .. } => Some(solutions),
            Self::Unknown(_) => None,
        }
    }
}

/// Compiled fast-path filter for a reduced [`System`].
struct FastEvaluator<'a> {
    /// Most selective pair equation `(k0, k1, rhs, mask)` evaluated first with 2 `eval_round`s.
    pair_first: Option<(u64, u64, u64, u64)>,
    /// Optional second pair sharing `k0` (`(k2, rhs2, mask2)`), needing only 1 extra `eval_round`!
    shared_second: Option<(u64, u64, u64)>,
    rest: &'a [Equation],
    skip_idx: [usize; 2],
}

impl<'a> FastEvaluator<'a> {
    fn new(eqs: &'a [Equation]) -> Self {
        let mut pair_idx = None;
        for (i, eq) in eqs.iter().enumerate() {
            if eq.keys.len() == 2 && eq.mask.count_ones() >= 32 {
                pair_idx = Some(i);
                break;
            }
        }
        let Some(i0) = pair_idx else {
            return Self {
                pair_first: None,
                shared_second: None,
                rest: eqs,
                skip_idx: [usize::MAX, usize::MAX],
            };
        };
        let eq0 = &eqs[i0];
        let (mut k0, mut k1) = (eq0.keys[0], eq0.keys[1]);
        let mut second = None;
        let mut i1_skip = usize::MAX;
        for (j, eq) in eqs.iter().enumerate() {
            if j == i0 || eq.keys.len() != 2 {
                continue;
            }
            if eq.keys[0] == k0 {
                second = Some((eq.keys[1], eq.rhs, eq.mask));
                i1_skip = j;
                break;
            } else if eq.keys[1] == k0 {
                second = Some((eq.keys[0], eq.rhs, eq.mask));
                i1_skip = j;
                break;
            } else if eq.keys[0] == k1 {
                core::mem::swap(&mut k0, &mut k1);
                second = Some((eq.keys[1], eq.rhs, eq.mask));
                i1_skip = j;
                break;
            } else if eq.keys[1] == k1 {
                core::mem::swap(&mut k0, &mut k1);
                second = Some((eq.keys[0], eq.rhs, eq.mask));
                i1_skip = j;
                break;
            }
        }
        Self {
            pair_first: Some((k0, k1, eq0.rhs, eq0.mask)),
            shared_second: second,
            rest: eqs,
            skip_idx: [i0, i1_skip],
        }
    }

    #[inline(always)]
    fn holds(&self, x: u64) -> bool {
        if let Some((k0, k1, rhs0, mask0)) = self.pair_first {
            let h0 = eval_round(x, k0);
            let h1 = eval_round(x, k1);
            if (h0 ^ h1 ^ rhs0) & mask0 != 0 {
                return false;
            }
            if let Some((k2, rhs1, mask1)) = self.shared_second {
                let h2 = eval_round(x, k2);
                if (h0 ^ h2 ^ rhs1) & mask1 != 0 {
                    return false;
                }
            }
            for (idx, eq) in self.rest.iter().enumerate() {
                if idx == self.skip_idx[0] || idx == self.skip_idx[1] {
                    continue;
                }
                if !eq.holds(x) {
                    return false;
                }
            }
            true
        } else {
            self.rest.iter().all(|eq| eq.holds(x))
        }
    }
}

fn run_stripes(total: u64, stripe: u64, threads: usize, work: impl Fn(usize, u64, u64) + Sync) {
    if total == 0 {
        return;
    }
    let num_stripes = total.div_ceil(stripe);
    let avail = match threads {
        0 => std::thread::available_parallelism().map_or(1, |n| n.get()),
        n => n.max(1),
    };
    let n_threads = avail.min(usize::try_from(num_stripes).unwrap_or(usize::MAX));
    if n_threads <= 1 {
        let mut s = 0u64;
        let mut base = 0u64;
        while base < total {
            let end = (base + stripe).min(total);
            work(s as usize, base, end);
            base = end;
            s += 1;
        }
        return;
    }
    let next = AtomicU64::new(0);
    let worker = || {
        loop {
            let s = next.fetch_add(1, Ordering::Relaxed);
            if s >= num_stripes {
                break;
            }
            let base = s * stripe;
            let end = (base + stripe).min(total);
            work(s as usize, base, end);
        }
    };
    std::thread::scope(|scope| {
        for _ in 1..n_threads {
            if crate::threads::builder()
                .spawn_scoped(scope, worker)
                .is_err()
            {
                break;
            }
        }
        worker();
    });
}

fn domain_contains_exact(domain: &Domain, target: u64) -> Option<bool> {
    match domain {
        Domain::Empty => Some(false),
        Domain::Range { lo, hi, stride } => {
            if target < *lo || target > *hi {
                Some(false)
            } else {
                Some((target - *lo).is_multiple_of((*stride).max(1)))
            }
        }
        Domain::SignedRange { lo, hi } => {
            let t = target as i64;
            Some(*lo <= t && t <= *hi)
        }
        Domain::Masked {
            free_mask,
            fixed_ones,
        } => Some((target & !*free_mask) == *fixed_ones),
        Domain::Values(v) => Some(v.binary_search(&target).is_ok()),
        Domain::Mapped { .. } => None,
    }
}

/// Solves `system` completely over `domain` within deterministic `limits`.
///
/// First applies exact GF(2) reduction and closed-form single-round inversion (which can prove
/// unsatisfiability or find a unique solution in `O(1)` even on wide domains when `domain`
/// membership is O(1)), then enumerates `domain` across `limits.threads` worker threads in
/// deterministic stripe order.
#[must_use]
pub fn solve_bounded(system: &System, domain: &Domain, limits: &Limits) -> SolveOutcome {
    let total_128 = domain.len();
    if total_128 == 0 {
        return SolveOutcome::Complete {
            solutions: Vec::new(),
            evaluated: 0,
        };
    }

    match system.reduce_gf2() {
        ReducedSystem::Unsatisfiable => {
            return SolveOutcome::Complete {
                solutions: Vec::new(),
                evaluated: 0,
            };
        }
        ReducedSystem::Unique(x0) => {
            if let Some(in_dom) = domain_contains_exact(domain, x0) {
                let solutions = if in_dom { vec![x0] } else { Vec::new() };
                if solutions.len() > limits.max_solutions {
                    return SolveOutcome::Unknown(Incomplete::TooManySolutions {
                        limit: limits.max_solutions,
                    });
                }
                return SolveOutcome::Complete {
                    solutions,
                    evaluated: 1,
                };
            }
        }
        ReducedSystem::Tautology => {
            if total_128 > u128::from(limits.max_inputs) {
                return SolveOutcome::Unknown(Incomplete::FuelExhausted {
                    required: total_128,
                    budget: limits.max_inputs,
                });
            }
            let total = total_128 as u64;
            let mut sols = Vec::with_capacity((total as usize).min(limits.max_solutions + 1));
            for i in 0..total {
                sols.push(domain.nth(i));
            }
            sols.sort_unstable();
            sols.dedup();
            if sols.len() > limits.max_solutions {
                return SolveOutcome::Unknown(Incomplete::TooManySolutions {
                    limit: limits.max_solutions,
                });
            }
            return SolveOutcome::Complete {
                solutions: sols,
                evaluated: total,
            };
        }
        ReducedSystem::Open(_) => {}
    }

    if total_128 > u128::from(limits.max_inputs) {
        return SolveOutcome::Unknown(Incomplete::FuelExhausted {
            required: total_128,
            budget: limits.max_inputs,
        });
    }
    let total = total_128 as u64;
    let reduced_eqs = match system.reduce_gf2() {
        ReducedSystem::Open(eqs) => eqs,
        ReducedSystem::Unique(x0) => vec![Equation::new(
            vec![1],
            eval_round(x0, 1),
        )],
        _ => unreachable!(),
    };
    let fast = FastEvaluator::new(&reduced_eqs);

    const STRIPE: u64 = 1 << 16;
    let num_stripes = total.div_ceil(STRIPE) as usize;
    let stripe_hits: Vec<Mutex<Vec<u64>>> = (0..num_stripes)
        .map(|_| Mutex::new(Vec::new()))
        .collect();
    let overflow = AtomicBool::new(false);
    let cap = limits.max_solutions;

    run_stripes(total, STRIPE, limits.threads, |s_idx, start, end| {
        if overflow.load(Ordering::Relaxed) {
            return;
        }
        let mut local = Vec::new();
        match domain {
            Domain::Range { lo, stride: 1, .. } => {
                let mut x = lo.wrapping_add(start);
                for _ in start..end {
                    if fast.holds(x) {
                        local.push(x);
                        if local.len() > cap {
                            overflow.store(true, Ordering::Relaxed);
                            break;
                        }
                    }
                    x = x.wrapping_add(1);
                }
            }
            Domain::SignedRange { lo, .. } => {
                let mut x = (*lo as u64).wrapping_add(start);
                for _ in start..end {
                    if fast.holds(x) {
                        local.push(x);
                        if local.len() > cap {
                            overflow.store(true, Ordering::Relaxed);
                            break;
                        }
                    }
                    x = x.wrapping_add(1);
                }
            }
            _ => {
                for idx in start..end {
                    let x = domain.nth(idx);
                    if fast.holds(x) {
                        local.push(x);
                        if local.len() > cap {
                            overflow.store(true, Ordering::Relaxed);
                            break;
                        }
                    }
                }
            }
        }
        if !local.is_empty() {
            *stripe_hits[s_idx].lock().unwrap_or_else(|e| e.into_inner()) = local;
        }
    });

    // Deterministic merge in canonical stripe order, then sort & deduplicate.
    // Note: if `overflow` triggered in an early stripe, re-checking after merging or only
    // triggering `overflow` when a single stripe alone already has `> cap` unique values:
    // for injective `Range`/`SignedRange`/`Masked`/`Values`, all elements in a stripe are distinct,
    // so `local.len() > cap` guarantees total unique solutions `> cap`! For `Mapped`, `ops` might
    // not be injective, so deduplicate `local` before setting `overflow`? Even simpler: deduplicate
    // all collected hits if `!overflow`, and in `Mapped` deduplicate `local` before checking `> cap`!
    let mut solutions = Vec::new();
    for slot in stripe_hits {
        let v = slot.into_inner().unwrap_or_else(|e| e.into_inner());
        solutions.extend(v);
    }
    solutions.sort_unstable();
    solutions.dedup();
    if overflow.load(Ordering::Relaxed) || solutions.len() > limits.max_solutions {
        // For non-injective `Mapped`, verify if `overflow` was a duplicate mirage (only when `Mapped`).
        if matches!(domain, Domain::Mapped { .. }) && solutions.len() <= limits.max_solutions {
            let mut exact_sols = Vec::new();
            for idx in 0..total {
                let x = domain.nth(idx);
                if fast.holds(x) && !exact_sols.contains(&x) {
                    exact_sols.push(x);
                    if exact_sols.len() > limits.max_solutions {
                        return SolveOutcome::Unknown(Incomplete::TooManySolutions {
                            limit: limits.max_solutions,
                        });
                    }
                }
            }
            exact_sols.sort_unstable();
            return SolveOutcome::Complete {
                solutions: exact_sols,
                evaluated: total,
            };
        }
        return SolveOutcome::Unknown(Incomplete::TooManySolutions {
            limit: limits.max_solutions,
        });
    }
    SolveOutcome::Complete {
        solutions,
        evaluated: total,
    }
}

/// Derives [`Domain`] automatically from `cx` [`Facts`] (and `assumptions`) on `system.input()`
/// and runs [`solve_bounded`].
pub fn solve_derived(
    cx: &mut Context,
    system: &System,
    assumptions: Option<&Assumptions>,
    limits: &Limits,
) -> Result<(Domain, SolveOutcome), Error> {
    let domain = match system.input {
        Some(inp) => Domain::derive(cx, inp, assumptions)?,
        None => Domain::full(),
    };
    let outcome = solve_bounded(system, &domain, limits);
    Ok((domain, outcome))
}

/// Peels injective layers (`counter * odd_C == v`, `zext(x) == v`, `sext(x) == v`, `x ^ k == v`,
/// `x + k == v`, `rotl(x, k) == v`, `@mixer.round(x, odd_C) == v`, etc.) on `input == value`
/// down to the deepest inner expression `(inner_expr, inner_val)` using Bitwright's invertibility
/// engine.
///
/// Returns `Ok(None)` when `value` has **no** preimage under `input`'s outer injective layers
/// (for instance `zext<64>(x:32) == 1 << 40`).
pub fn invert_input(
    cx: &mut Context,
    input: Expr,
    value: u64,
    assumptions: Option<&Assumptions>,
) -> Result<Option<(Expr, BitVec)>, Error> {
    let id = cx.id(input)?;
    let w = cx.width_of(id);
    let target = BitVec::wrapping_from_u64(w, value);
    let refreshed = assumptions.map(|a| a.refreshed(cx)).transpose()?;
    struct FactOracle<'a> {
        a: Option<&'a Assumptions>,
    }
    impl crate::invert::Oracle for FactOracle<'_> {
        type Err = Error;
        fn facts(&mut self, cx: &mut Context, i: u32) -> Result<Option<Facts>, Error> {
            let e = cx.handle(i);
            match self.a {
                None => Ok(Some(cx.facts(e)?)),
                Some(assump) => {
                    let cap = cx.config().fact_work;
                    Ok(cx.facts_under_cap(e, assump, cap)?.ok().map(|(f, _)| f))
                }
            }
        }
        fn charge(&mut self, _units: u64) -> Result<(), Error> {
            Ok(())
        }
    }
    let mut oracle = FactOracle {
        a: refreshed.as_deref(),
    };
    match crate::invert::solve_eq(cx, &mut oracle, id, &target)? {
        Some(crate::invert::Solved::Const(false)) => Ok(None),
        Some(crate::invert::Solved::Const(true)) | None => Ok(Some((input, target))),
        Some(crate::invert::Solved::Eq(inner_id, inner_val)) => {
            Ok(Some((cx.handle(inner_id), inner_val)))
        }
    }
}

// ---------------------------------------------------------------------------
// Best-Effort `u64` Witness Search (Item 2)
// ---------------------------------------------------------------------------

/// Fuel configuration for best-effort witness proposals ([`propose_witness`], [`propose_expr_witness`]).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct WitnessLimits {
    /// Maximum candidate values evaluated (`196_608` = `3 * 65_536` by default, covering
    /// `0..2^16` plus the top `2^16` of the 32-bit and 64-bit unsigned ranges).
    pub max_inputs: u64,
}

impl Default for WitnessLimits {
    fn default() -> Self {
        Self {
            max_inputs: 3 * (1 << 16) + 1024,
        }
    }
}

setters!(WitnessLimits {
    with_max_inputs: max_inputs: u64,
});

/// Result of [`propose_witness`]: a verified witness `value`, an algebraic proof of global
/// unsatisfiability, or `Unknown` (no completeness claim is ever made for `Found` or `Unknown`).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum WitnessOutcome {
    /// Verified 64-bit input `value` satisfying every equation in the system.
    Found { value: u64, checked: u64 },
    /// Algebraically proved unsatisfiable over all `2^64` inputs (via GF(2) contradiction or
    /// single-round closed-form inversion).
    Unsatisfiable { checked: u64 },
    /// No witness found within `checked` deterministic probes.
    Unknown { checked: u64 },
}

impl WitnessOutcome {
    /// Returns the satisfying 64-bit value if found.
    #[must_use]
    pub const fn value(&self) -> Option<u64> {
        match *self {
            Self::Found { value, .. } => Some(value),
            _ => None,
        }
    }
}

/// Expression-level witness returned by [`propose_expr_witness`], carrying both the 64-bit value
/// at `system.input()` and its inverted assignment `(inner_expr, inner_value)` when `input` wraps
/// a deeper expression via injective layers (such as `counter * odd_C`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprWitness {
    /// Verified witness: `input == input_value`, inverted down to `inner == inner_value`.
    Found {
        input_value: u64,
        inner: Expr,
        inner_value: BitVec,
        checked: u64,
    },
    /// Provably unsatisfiable (either algebraically over `u64` or because the derived domain is empty).
    Unsatisfiable { checked: u64 },
    /// No witness found within deterministic fuel.
    Unknown { checked: u64 },
}

/// Deterministically searches for a 64-bit witness satisfying `system` within `limits.max_inputs`
/// evaluations, without claiming completeness on `Found` or `Unknown`.
#[must_use]
pub fn propose_witness(system: &System, limits: &WitnessLimits) -> WitnessOutcome {
    thread_local! {
        static MEMO: std::cell::RefCell<std::collections::HashMap<(Vec<Equation>, u64), WitnessOutcome>> =
            std::cell::RefCell::new(std::collections::HashMap::new());
    }
    let key = (system.equations.clone(), limits.max_inputs);
    if let Some(hit) = MEMO.with(|m| m.borrow().get(&key).copied()) {
        return hit;
    }
    let out = propose_witness_filtered(system, limits, |_| true);
    MEMO.with(|m| {
        let mut map = m.borrow_mut();
        if map.len() >= 256 {
            map.clear();
        }
        map.insert(key, out);
    });
    out
}

fn propose_witness_filtered(
    system: &System,
    limits: &WitnessLimits,
    mut accept: impl FnMut(u64) -> bool,
) -> WitnessOutcome {
    match system.reduce_gf2() {
        ReducedSystem::Unsatisfiable => return WitnessOutcome::Unsatisfiable { checked: 0 },
        ReducedSystem::Unique(x0) => {
            return if accept(x0) {
                WitnessOutcome::Found {
                    value: x0,
                    checked: 1,
                }
            } else {
                WitnessOutcome::Unsatisfiable { checked: 1 }
            };
        }
        ReducedSystem::Tautology => {
            if accept(0) {
                return WitnessOutcome::Found {
                    value: 0,
                    checked: 1,
                };
            }
        }
        ReducedSystem::Open(_) => {}
    }

    let budget = limits.max_inputs;
    if budget == 0 {
        return WitnessOutcome::Unknown { checked: 0 };
    }
    let reduced_eqs = match system.reduce_gf2() {
        ReducedSystem::Open(eqs) => eqs,
        ReducedSystem::Tautology => Vec::new(),
        _ => unreachable!(),
    };
    let fast = FastEvaluator::new(&reduced_eqs);
    let mut checked = 0u64;

    macro_rules! probe {
        ($cand:expr) => {{
            if checked >= budget {
                return WitnessOutcome::Unknown { checked };
            }
            let x: u64 = $cand;
            checked += 1;
            if fast.holds(x) && accept(x) {
                return WitnessOutcome::Found { value: x, checked };
            }
        }};
    }

    // Tier 0: extremal constants, powers of two, bitmasks, and common status boundaries.
    for &c in &[
        0u64,
        1,
        2,
        u32::MAX as u64,
        u64::MAX,
        0x8000_0000,
        0x7fff_ffff,
        0xffff_ffff_8000_0000,
        0x7fff_ffff_ffff_ffff,
        0x8000_0000_0000_0000,
        0xc000_0000,
        0xffff_ffff_c000_0000,
    ] {
        probe!(c);
    }
    for b in 2..64u32 {
        probe!(1u64 << b);
        probe!((1u64 << b) - 1);
    }

    // Tier 1: small unsigned `0..2^16`, top `2^16` of `u32`, and top `2^16` of `u64`.
    const SPAN: u64 = 1 << 16;
    for x in 3..SPAN {
        probe!(x);
    }
    for x in ((1u64 << 32) - SPAN)..((1u64 << 32) - 1) {
        probe!(x);
    }
    for x in (u64::MAX - (SPAN - 1))..u64::MAX {
        probe!(x);
    }

    // Tier 2: common NTSTATUS codes (`0xc000_0001 .. 0xc000_0400`) and continued upward scan.
    for x in 0xc000_0001u64..0xc000_0401 {
        probe!(x);
    }
    let mut next = SPAN;
    while checked < budget {
        probe!(next);
        next += 1;
    }
    WitnessOutcome::Unknown { checked }
}

/// Proposes a verified witness for `system` in `cx` under `assumptions`: checks both direct
/// candidate values of `system.input()` (inverting injective wrappers such as `counter * odd_C`
/// via [`invert_input`]) and forward images of small values of the inner expression when `input`
/// wraps a subterm via [`ForwardOp`]s.
pub fn propose_expr_witness(
    cx: &mut Context,
    system: &System,
    assumptions: Option<&Assumptions>,
    limits: &WitnessLimits,
) -> Result<ExprWitness, Error> {
    let Some(input) = system.input else {
        return Ok(match propose_witness(system, limits) {
            WitnessOutcome::Found { .. } | WitnessOutcome::Unknown { .. } => {
                ExprWitness::Unknown { checked: 0 }
            }
            WitnessOutcome::Unsatisfiable { checked } => ExprWitness::Unsatisfiable { checked },
        });
    };
    let domain = Domain::derive(cx, input, assumptions)?;
    if domain.is_empty() {
        return Ok(ExprWitness::Unsatisfiable { checked: 0 });
    }

    // If the derived domain itself is tiny (`<= limits.max_inputs`), check it completely!
    if domain.len() <= u128::from(limits.max_inputs) {
        let solved = solve_bounded(
            system,
            &domain,
            &Limits::default()
                .with_max_inputs(limits.max_inputs)
                .with_max_solutions(16)
                .with_threads(1),
        );
        if let SolveOutcome::Complete {
            solutions,
            evaluated,
        } = solved
        {
            for v in solutions {
                if let Some((inner, inner_value)) = invert_input(cx, input, v, assumptions)? {
                    return Ok(ExprWitness::Found {
                        input_value: v,
                        inner,
                        inner_value,
                        checked: evaluated,
                    });
                }
            }
            return Ok(ExprWitness::Unsatisfiable { checked: evaluated });
        }
    }

    // Check if `input` is a deterministic chain over a deeper expression `base` (e.g. `counter * odd_C`)
    // so we can share budget between small values of `input` and small values of `base`.
    let id = cx.id(input)?;
    let mut cur = id;
    let mut rev_ops = Vec::new();
    for _ in 0..8 {
        if let Some((inner, op)) = peel_forward_step(cx, cur) {
            rev_ops.push(op);
            cur = inner;
        } else {
            break;
        }
    }
    let has_wrapper = !rev_ops.is_empty();
    let direct_budget = if has_wrapper {
        (limits.max_inputs * 3 / 4).max(1)
    } else {
        limits.max_inputs
    };

    let refreshed = assumptions.map(|a| a.refreshed(cx)).transpose()?;
    let top_facts = match refreshed.as_deref() {
        None => cx.facts(input)?,
        Some(a) => match cx.facts_under_cap(input, a, cx.config().fact_work)? {
            Ok((f, _)) => f,
            Err(_) => return Ok(ExprWitness::Unsatisfiable { checked: 0 }),
        },
    };

    let mut resolved: Option<(Expr, BitVec)> = None;
    let direct = if !has_wrapper
        && cx.node(id).op == OpCode::Sym
        && top_facts == Facts::top(Width::W64)
    {
        let w = propose_witness(
            system,
            &WitnessLimits {
                max_inputs: direct_budget,
            },
        );
        if let WitnessOutcome::Found { value, .. } = w {
            resolved = Some((input, BitVec::wrapping_from_u64(Width::W64, value)));
        }
        w
    } else {
        propose_witness_filtered(
            system,
            &WitnessLimits {
                max_inputs: direct_budget,
            },
            |v| {
                let bv = BitVec::wrapping_from_u64(Width::W64, v);
                if !top_facts.contains(&bv) {
                    return false;
                }
                if let Ok(Some(pair)) = invert_input(cx, input, v, assumptions) {
                    resolved = Some(pair);
                    true
                } else {
                    false
                }
            },
        )
    };
    match direct {
        WitnessOutcome::Found { value, checked } => {
            let (inner, inner_value) = resolved
                .unwrap_or_else(|| (input, BitVec::wrapping_from_u64(Width::W64, value)));
            Ok(ExprWitness::Found {
                input_value: value,
                inner,
                inner_value,
                checked,
            })
        }
        WitnessOutcome::Unsatisfiable { checked } => Ok(ExprWitness::Unsatisfiable { checked }),
        WitnessOutcome::Unknown { mut checked } => {
            if has_wrapper && checked < limits.max_inputs {
                rev_ops.reverse();
                let base_expr = cx.handle(cur);
                let base_w = cx.width_of(cur);
                let base_facts = match refreshed.as_deref() {
                    None => cx.facts(base_expr)?,
                    Some(a) => match cx.facts_under_cap(base_expr, a, cx.config().fact_work)? {
                        Ok((f, _)) => f,
                        Err(_) => return Ok(ExprWitness::Unsatisfiable { checked }),
                    },
                };
                let forward = |mut u: u64| -> u64 {
                    for &op in &rev_ops {
                        u = op.apply(u);
                    }
                    u
                };
                let rem = limits.max_inputs - checked;
                let span = (rem / 3).clamp(1, 1 << 16);
                let wb = base_w.bits();
                let full_base = if wb >= 64 { u64::MAX } else { (1u64 << wb) - 1 };
                for raw_u in (0..span).chain((full_base.saturating_sub(span - 1))..=full_base) {
                    if checked >= limits.max_inputs {
                        break;
                    }
                    let u = raw_u & full_base;
                    let ubv = BitVec::wrapping_from_u64(base_w, u);
                    if !base_facts.contains(&ubv) {
                        continue;
                    }
                    checked += 1;
                    let v = forward(u);
                    if system.holds(v) {
                        return Ok(ExprWitness::Found {
                            input_value: v,
                            inner: base_expr,
                            inner_value: ubv,
                            checked,
                        });
                    }
                }
            }
            Ok(ExprWitness::Unknown { checked })
        }
    }
}

// ---------------------------------------------------------------------------
// Mixer Theory Predicate Simplification & Prover Witness Proposals (Item 3)
// ---------------------------------------------------------------------------

/// Quick O(1) subtree bitmask test: returns `false` immediately when `expr` cannot contain any
/// mixer round (`@mixer.round` or `(x ^ C) * C ^ ... >>u ...`), guaranteeing zero overhead on
/// ordinary non-mixer expressions.
#[inline]
pub(crate) fn may_contain_mixer(cx: &Context, id: u32) -> bool {
    let ops = cx.meta[id as usize].ops;
    let ext = op_bit(OpCode::Ext2o0);
    let written = op_bit(OpCode::Mul) | op_bit(OpCode::LShr) | op_bit(OpCode::Xor);
    (ops & ext) != 0 || (ops & written) == written
}

/// Applies the mixer theory to a 1-bit predicate `goal` (under optional `assumptions` and
/// deterministic `fuel` for bounded-domain reductions):
///
/// 1. Round-trip cancellation `@mixer.unround(@mixer.round(x, C), C) -> x` (and vice versa) when `C` is odd.
/// 2. Same-key bijection cancellation `H(x, C) == H(y, C) -> x == y` (for odd `C`).
/// 3. Single-round closed-form inversion `H(x, C) == K -> x == invert_round(K, C)` (for odd `C`).
/// 4. Equality congruence: when `assumptions` or an implication guard asserts `a == b`, substitutes
///    `a -> b` across mixer inputs so `H(a, C_1) ^ H(a, C_2) == H(b, C_1) ^ H(b, C_2)` folds!
/// 5. Exact GF(2) elimination across conjoined mixer equations (in `assumptions` or negated-goal
///    conjunctions `!(c_1 & c_2 & ...)`): refutes inconsistent XOR combinations (`Proved` for
///    `!bad`), folds implied XOR equations, and solves exposed 1-key pivots via [`invert_round`].
/// 6. Complete bounded-domain reduction on mixer systems whose derived [`Domain`] has size
///    `<= domain_fuel`, replacing the mixer conjunction with exact `input == s_1 | ...` equalities.
pub fn simplify_predicate(
    cx: &mut Context,
    predicate: Expr,
    assumptions: Option<&Assumptions>,
    domain_fuel: u64,
) -> Result<Expr, Error> {
    let root = cx.id(predicate)?;
    if cx.wid(root) != 1 {
        return Ok(predicate);
    }
    let assump_has_mixer = assumptions.is_some_and(|a| {
        a.constraints()
            .any(|(_, e, _)| cx.id(e).is_ok_and(|id| may_contain_mixer(cx, id)))
    });
    if !may_contain_mixer(cx, root) && !assump_has_mixer {
        return Ok(predicate);
    }

    // Step 1: bottom-up local rewrites (round-trips, `H(x, C) == H(y, C)`, `H(x, C) == K`).
    let order = cx.post_order_ids(&[root]);
    let mut map: IdMap<u32, u32> = IdMap::default();
    for id in order {
        let n = cx.node(id);
        let mut kids = [n.a, n.b, n.c];
        let mut changed = false;
        for (slot, c) in n.children().enumerate() {
            if let Some(&nc) = map.get(&c) {
                kids[slot] = nc;
                changed |= nc != c;
            }
        }
        let cur = if changed { cx.rebuild(id, kids)? } else { id };
        let next = rewrite_local_mixer(cx, cur)?.unwrap_or(cur);
        map.insert(id, next);
    }
    let mut cur_root = map[&root];

    // Step 2: collect equality equivalences `u == v` and mixer equations implied by the
    // counterexample conjunction `bad = !cur_root & assumptions`.
    let mut bad = cx.c_un(UnOp::Not, cur_root)?;
    let mut assump_ids = Vec::new();
    if let Some(a) = assumptions {
        a.check_context(cx)?;
        for pred in a.predicates(cx)? {
            let pid = cx.id(pred)?;
            assump_ids.push(pid);
            bad = cx.c_bin(BinOp::And, bad, pid)?;
        }
    }

    // Congruence closure over direct word equalities `u == v` in `bad`: by the exact Boolean
    // identity `B(u, v) <=> (u == v) & B(v, v)` whenever `B(u, v) => (u == v)`, we substitute
    // `other -> rep` in `bad` and conjoin `other == rep`, never mutating `cur_root` unless `bad`
    // is refuted (`cur_root == true`) or replaced by an equivalent negation!
    let mut eq_pairs = Vec::new();
    collect_word_equalities(cx, bad, true, &mut eq_pairs);
    if !eq_pairs.is_empty() {
        let mut uf: IdMap<u32, u32> = IdMap::default();
        fn find_rep(uf: &mut IdMap<u32, u32>, x: u32) -> u32 {
            let p = uf.get(&x).copied().unwrap_or(x);
            if p == x {
                x
            } else {
                let r = find_rep(uf, p);
                uf.insert(x, r);
                r
            }
        }
        for &(a, b) in &eq_pairs {
            let ra = find_rep(&mut uf, a);
            let rb = find_rep(&mut uf, b);
            if ra != rb {
                let (ca, cb) = (cx.const_val(ra).is_some(), cx.const_val(rb).is_some());
                if ca && cb {
                    return cx.constant_u64(Width::W1, 1);
                }
                let (rep, other) = if ca {
                    (ra, rb)
                } else if cb {
                    (rb, ra)
                } else if ra < rb {
                    (ra, rb)
                } else {
                    (rb, ra)
                };
                uf.insert(other, rep);
            }
        }
        let mut subst = IdMap::default();
        let mut keys: Vec<u32> = uf.keys().copied().collect();
        keys.sort_unstable();
        for k in keys {
            let r = find_rep(&mut uf, k);
            if r != k {
                // If `r` is a constant and `k == r` has no preimage (e.g. `zext<64>(u32) == 0x1_0000_1234`),
                // then `bad` is immediately unsatisfiable!
                if let Some(cv) = const_u64(cx, r)
                    && invert_input(cx, cx.handle(k), cv, assumptions)?.is_none()
                {
                    return cx.constant_u64(Width::W1, 1);
                }
                subst.insert(k, r);
            }
        }
        if !subst.is_empty() {
            let mut sub_bad = eval_mixer_subst(cx, bad, &subst)?;
            if cx.const_val(sub_bad).is_some_and(|bv| bv.is_zero()) {
                return cx.constant_u64(Width::W1, 1);
            }
            let mut sorted_pairs: Vec<(u32, u32)> = subst.iter().map(|(&k, &r)| (k, r)).collect();
            sorted_pairs.sort_unstable();
            for (k, r) in sorted_pairs {
                let eq_kr = cx.c_cmp(CmpOp::Eq, k, r)?;
                sub_bad = cx.c_bin(BinOp::And, eq_kr, sub_bad)?;
            }
            bad = sub_bad;
        }
    }

    // Step 3: extract mixer systems on `bad` (`!cur_root & assumptions`).
    // - If ANY system on `bad` is unsatisfiable (by GF(2) elimination, single-round pivot, or
    //   complete bounded-domain enumeration within `domain_fuel`), then `bad == false`, which
    //   proves `cur_root == true`!
    // - If a system on `bad` reduces to a unique solution `input == x0` (or `k <= 8` solutions in
    //   a bounded domain), specialize/conjoin that exact fact or rewrite matching mixer comparisons
    //   inside `cur_root`!
    let mut raw = Vec::new();
    collect_implied_equations(cx, bad, true, &mut raw);
    let mut neg_raw = Vec::new();
    collect_implied_inequalities(cx, bad, true, &mut neg_raw);
    let systems = group_by_input(cx, raw);
    let mut fuel_left = domain_fuel;
    let mut pin_facts: Vec<(u32, Vec<u64>)> = Vec::new();

    for sys in &systems {
        match sys.reduce_gf2() {
            ReducedSystem::Unsatisfiable => {
                return cx.constant_u64(Width::W1, 1);
            }
            ReducedSystem::Unique(x0) => {
                if let Some(inp) = sys.input {
                    if invert_input(cx, inp, x0, assumptions)?.is_none() {
                        return cx.constant_u64(Width::W1, 1);
                    }
                    let inp_id = cx.id(inp)?;
                    for &(neg_src, ref neg_eq) in &neg_raw {
                        if neg_src == inp_id && neg_eq.holds(x0) {
                            return cx.constant_u64(Width::W1, 1);
                        }
                    }
                    pin_facts.push((inp_id, vec![x0]));
                }
            }
            ReducedSystem::Open(ref rref) => {
                if let Some(inp) = sys.input {
                    let inp_id = cx.id(inp)?;
                    for &(neg_src, ref neg_eq) in &neg_raw {
                        if neg_src == inp_id
                            && let Some(implied) = implied_rhs_from_rref(rref, &neg_eq.keys)
                            && (implied & neg_eq.mask) == (neg_eq.rhs & neg_eq.mask)
                        {
                            return cx.constant_u64(Width::W1, 1);
                        }
                    }
                    if fuel_left > 0 {
                        let dom = Domain::derive(cx, inp, assumptions)?;
                        if dom.len() <= u128::from(fuel_left) {
                            let solved = solve_bounded(
                                sys,
                                &dom,
                                &Limits::default()
                                    .with_max_inputs(fuel_left)
                                    .with_max_solutions(16),
                            );
                            if let SolveOutcome::Complete {
                                solutions,
                                evaluated,
                            } = solved
                            {
                                fuel_left = fuel_left.saturating_sub(evaluated);
                                if solutions.is_empty() {
                                    return cx.constant_u64(Width::W1, 1);
                                }
                                pin_facts.push((inp_id, solutions));
                            }
                        }
                    }
                }
            }
            ReducedSystem::Tautology => {}
        }
    }

    // If `bad` pinned `input` to a small complete set of values `{v_1, ..., v_k}`, check whether
    // substituting each `v_i` for `input` in `bad` evaluates all mixer rounds on `input` to constants
    // and collapses `bad` to `false` (or shrinks `cur_root` when `cur_root` itself is a mixer guard)!
    if !pin_facts.is_empty() {
        let mut any_satisfiable = false;
        let mut disj_guards: Option<u32> = None;
        if let &[(inp_id, ref vals)] = pin_facts.as_slice()
            && vals.len() <= 8
        {
            for &v in vals {
                let v_const = cx.mk_const_u64(64, v)?;
                let mut sub = IdMap::default();
                sub.insert(inp_id, v_const);
                let spec_bad = eval_mixer_subst(cx, bad, &sub)?;
                if cx.const_val(spec_bad).is_some_and(|bv| bv.is_zero()) {
                    continue;
                }
                any_satisfiable = true;
                let eq_node = build_input_eq(cx, inp_id, v, assumptions)?;
                let conj = cx.c_bin(BinOp::And, eq_node, spec_bad)?;
                disj_guards = Some(match disj_guards {
                    None => conj,
                    Some(prev) => cx.c_bin(BinOp::Or, prev, conj)?,
                });
            }
            if !any_satisfiable {
                return cx.constant_u64(Width::W1, 1);
            }
            if assump_ids.is_empty()
                && let Some(new_bad) = disj_guards
            {
                cur_root = cx.c_un(UnOp::Not, new_bad)?;
            }
        }
    }

    // Step 4: Also rewrite standalone bounded-domain mixer comparisons anywhere inside `cur_root`
    // (e.g. positive equality `(H(zext(x:8), a) ^ H(zext(x:8), b)) == K` -> `x == cand` or `false`!).
    if fuel_left > 0 {
        cur_root = reduce_bounded_subguards(cx, cur_root, assumptions, &mut fuel_left)?;
    }

    Ok(cx.handle(cur_root))
}

fn rewrite_local_mixer(cx: &mut Context, id: u32) -> Result<Option<u32>, Error> {
    let n = cx.node(id);
    // Round-trip cancellation on `@mixer.unround(@mixer.round(x, C), C)` and `@mixer.round(@mixer.unround(y, C), C)`
    if let Some((_, 0)) = n.op.as_ext()
        && let Some(op) = cx.registry.as_deref().and_then(|r| r.op_at(n.aux))
    {
        let name = op.name();
        if name == UNROUND_OP_NAME || name == ROUND_OP_NAME {
            let mut ch = n.children();
            let arg0 = ch.next().unwrap();
            let key_id = ch.next().unwrap();
            let key_odd = const_u64(cx, key_id).is_some_and(|k| k & 1 == 1);
            if key_odd {
                if name == UNROUND_OP_NAME
                    && let Some((src, k2)) = match_round_id(cx, arg0)
                    && Some(k2) == const_u64(cx, key_id)
                {
                    return Ok(Some(src));
                }
                if name == ROUND_OP_NAME {
                    let an = cx.node(arg0);
                    if an.op.as_ext().is_some_and(|(_, o)| o == 0)
                        && cx
                            .registry
                            .as_deref()
                            .and_then(|r| r.op_at(an.aux))
                            .is_some_and(|iop| iop.name() == UNROUND_OP_NAME)
                    {
                        let mut ach = an.children();
                        let inner_y = ach.next().unwrap();
                        let inner_k = ach.next().unwrap();
                        if inner_k == key_id {
                            return Ok(Some(inner_y));
                        }
                    }
                }
            }
        }
    }

    // Equality / inequality of two rounds with the same odd key (`H(x, C) == H(y, C) -> x == y`)
    // or a single round against a constant (`H(x, C) == K -> x == invert_round(K, C)`).
    if matches!(n.op, OpCode::Eq | OpCode::Ne) && cx.wid(n.a) == 64 {
        let cmp = if n.op == OpCode::Eq {
            CmpOp::Eq
        } else {
            CmpOp::Ne
        };
        if let (Some((x, ka)), Some((y, kb))) = (match_round_id(cx, n.a), match_round_id(cx, n.b))
            && ka == kb
            && ka & 1 == 1
        {
            return cx.c_cmp(cmp, x, y).map(Some);
        }
        if let Some((subject, target)) = const_side_64(cx, n.a, n.b)
            && let Some((src, eq)) = parse_xor_term(cx, subject, target, u64::MAX)
            && eq.keys.len() == 1
            && let Some(x0) = invert_round(eq.rhs, eq.keys[0])
        {
            let k_id = cx.mk_const_u64(64, x0)?;
            return cx.c_cmp(cmp, src, k_id).map(Some);
        }
    }
    Ok(None)
}

fn collect_implied_inequalities(
    cx: &Context,
    root: u32,
    want: bool,
    out: &mut Vec<(u32, Equation)>,
) {
    let mut stack = vec![(root, want)];
    let mut seen: IdMap<(u32, bool), ()> = IdMap::default();
    while let Some((id, w)) = stack.pop() {
        if seen.len() > 512 || seen.insert((id, w), ()).is_some() {
            continue;
        }
        let n = cx.node(id);
        match n.op {
            OpCode::Not if n.width == 1 => stack.push((n.a, !w)),
            OpCode::And if w => {
                stack.push((n.a, true));
                stack.push((n.b, true));
            }
            OpCode::Or if !w => {
                stack.push((n.a, false));
                stack.push((n.b, false));
            }
            OpCode::Eq | OpCode::Ne if (n.op == OpCode::Ne) == w && cx.wid(n.a) == 64 => {
                if let Some((subject, target)) = const_side_64(cx, n.a, n.b) {
                    let (term, obs) = if cx.node(subject).op == OpCode::And {
                        let an = cx.node(subject);
                        const_side_64(cx, an.a, an.b).unwrap_or((subject, u64::MAX))
                    } else {
                        (subject, u64::MAX)
                    };
                    if let Some(item) = parse_xor_term(cx, term, target, obs) {
                        out.push(item);
                    }
                } else {
                    // Also handle `H_1 ^ ... == H_k ^ ... ^ K` written with rounds on both sides!
                    let mut xor_stack = vec![n.a, n.b];
                    let mut salt = 0u64;
                    let mut keys = Vec::new();
                    let mut source: Option<u32> = None;
                    let mut ok = true;
                    let mut steps = 0usize;
                    while let Some(cur) = xor_stack.pop() {
                        steps += 1;
                        if steps > 64 {
                            ok = false;
                            break;
                        }
                        if let Some(c) = const_u64(cx, cur) {
                            salt ^= c;
                            continue;
                        }
                        if let Some((src, key)) = match_round_id(cx, cur) {
                            if let Some(prev) = source {
                                if prev != src {
                                    ok = false;
                                    break;
                                }
                            } else {
                                source = Some(src);
                            }
                            keys.push(key);
                            continue;
                        }
                        let cn = cx.node(cur);
                        if cn.op == OpCode::Xor {
                            xor_stack.push(cn.a);
                            xor_stack.push(cn.b);
                        } else {
                            ok = false;
                            break;
                        }
                    }
                    if ok
                        && let Some(src) = source
                    {
                        let eq = Equation::new(keys, salt);
                        if !eq.keys.is_empty() {
                            out.push((src, eq));
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

fn collect_word_equalities(cx: &Context, root: u32, want: bool, out: &mut Vec<(u32, u32)>) {
    let mut stack = vec![(root, want)];
    let mut seen: IdMap<(u32, bool), ()> = IdMap::default();
    while let Some((id, w)) = stack.pop() {
        if seen.len() > 512 || seen.insert((id, w), ()).is_some() {
            continue;
        }
        let n = cx.node(id);
        match n.op {
            OpCode::Not if n.width == 1 => stack.push((n.a, !w)),
            OpCode::And if w => {
                stack.push((n.a, true));
                stack.push((n.b, true));
            }
            OpCode::Or if !w => {
                stack.push((n.a, false));
                stack.push((n.b, false));
            }
            OpCode::Eq | OpCode::Ne
                if (n.op == OpCode::Eq) == w
                    && cx.wid(n.a) > 1
                    && n.a != n.b
                    && !may_contain_mixer(cx, n.a)
                    && !may_contain_mixer(cx, n.b) =>
            {
                out.push((n.a, n.b));
            }
            _ => {}
        }
    }
}

fn eval_mixer_subst(cx: &mut Context, root: u32, subst: &IdMap<u32, u32>) -> Result<u32, Error> {
    let order = cx.post_order_ids(&[root]);
    let mut map: IdMap<u32, u32> = IdMap::default();
    for id in order {
        if let Some(&to) = subst.get(&id) {
            map.insert(id, to);
            continue;
        }
        let n = cx.node(id);
        let mut kids = [n.a, n.b, n.c];
        let mut changed = false;
        for (slot, c) in n.children().enumerate() {
            if let Some(&nc) = map.get(&c) {
                kids[slot] = nc;
                changed |= nc != c;
            }
        }
        let cur = if changed { cx.rebuild(id, kids)? } else { id };
        let next = rewrite_local_mixer(cx, cur)?.unwrap_or(cur);
        map.insert(id, next);
    }
    Ok(map[&root])
}

fn build_input_eq(
    cx: &mut Context,
    inp_id: u32,
    val: u64,
    assumptions: Option<&Assumptions>,
) -> Result<u32, Error> {
    match invert_input(cx, cx.handle(inp_id), val, assumptions)? {
        None => cx.mk_const_u64(1, 0),
        Some((inner, bv)) => {
            let iid = cx.id(inner)?;
            let kid = cx.mk_const(&bv)?;
            cx.c_cmp(CmpOp::Eq, iid, kid)
        }
    }
}

fn reduce_bounded_subguards(
    cx: &mut Context,
    root: u32,
    assumptions: Option<&Assumptions>,
    fuel_left: &mut u64,
) -> Result<u32, Error> {
    let order = cx.post_order_ids(&[root]);
    if order.len() > 4096 {
        return Ok(root);
    }
    let mut map: IdMap<u32, u32> = IdMap::default();
    for id in order {
        let n = cx.node(id);
        let mut kids = [n.a, n.b, n.c];
        let mut changed = false;
        for (slot, c) in n.children().enumerate() {
            if let Some(&nc) = map.get(&c) {
                kids[slot] = nc;
                changed |= nc != c;
            }
        }
        let cur = if changed { cx.rebuild(id, kids)? } else { id };
        let cn = cx.node(cur);
        let mut replaced = None;
        if *fuel_left > 0
            && matches!(cn.op, OpCode::Eq | OpCode::Ne)
            && cx.wid(cn.a) == 64
            && may_contain_mixer(cx, cur)
        {
            let mut raw = Vec::new();
            collect_implied_equations(cx, cur, cn.op == OpCode::Eq, &mut raw);
            let systems = group_by_input(cx, raw);
            if let [sys] = systems.as_slice()
                && let Some(inp) = sys.input
            {
                let dom = Domain::derive(cx, inp, assumptions)?;
                if dom.len() <= u128::from(*fuel_left) {
                    let solved = solve_bounded(
                        sys,
                        &dom,
                        &Limits::default()
                            .with_max_inputs(*fuel_left)
                            .with_max_solutions(16),
                    );
                    if let SolveOutcome::Complete {
                        solutions,
                        evaluated,
                    } = solved
                    {
                        *fuel_left = fuel_left.saturating_sub(evaluated);
                        let inp_id = cx.id(inp)?;
                        // Verify every candidate against `cur`'s equality directly (in case `cur`
                        // was an OR with non-mixer siblings or weaker mask).
                        let eq_check = if cn.op == OpCode::Eq {
                            cur
                        } else {
                            cx.c_un(UnOp::Not, cur)?
                        };
                        let mut disj = cx.mk_const_u64(1, 0)?;
                        let mut exact_ok = true;
                        for &cand in &solutions {
                            let c64 = cx.mk_const_u64(64, cand)?;
                            let mut sub = IdMap::default();
                            sub.insert(inp_id, c64);
                            let res = eval_mixer_subst(cx, eq_check, &sub)?;
                            let guard = build_input_eq(cx, inp_id, cand, assumptions)?;
                            let arm = cx.c_bin(BinOp::And, guard, res)?;
                            disj = cx.c_bin(BinOp::Or, disj, arm)?;
                            if cx.tree_size(cx.handle(disj)).unwrap_or(u32::MAX) > 512 {
                                exact_ok = false;
                                break;
                            }
                        }
                        if exact_ok {
                            let final_node = if cn.op == OpCode::Ne {
                                cx.c_un(UnOp::Not, disj)?
                            } else {
                                disj
                            };
                            replaced = Some(final_node);
                        }
                    }
                }
            }
        }
        map.insert(id, replaced.unwrap_or(cur));
    }
    Ok(map[&root])
}

/// Proposes `(SymbolKey, BitVec)` candidate symbol assignments from any mixer equation systems
/// embedded inside `root`, for use by `sample_words::guard_samples`.
pub(super) fn candidate_symbol_patches(cx: &mut Context, root: u32) -> Vec<(crate::SymbolKey, BitVec)> {
    if !may_contain_mixer(cx, root) {
        return Vec::new();
    }
    let Ok(systems) = extract_all_systems(cx, cx.handle(root)) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let limits = WitnessLimits {
        max_inputs: 3 * (1 << 16) + 512,
    };
    for sys in &systems {
        if out.len() >= 8 {
            break;
        }
        if let Ok(ExprWitness::Found {
            inner, inner_value, ..
        }) = propose_expr_witness(cx, sys, None, &limits)
            && let Ok(Some(sym_id)) = cx.symbol_id(inner)
            && let Some(key) = cx.symbol_key(sym_id).cloned()
        {
            let pair = (key, inner_value);
            if !out.contains(&pair) {
                out.push(pair);
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ContextConfig, ParseOptions};
    use std::sync::Arc;

    #[test]
    fn round_and_inverse_are_exact_bijections_for_odd_keys() {
        let keys = [
            1u64,
            0x3188_e5d3_9d63_b2d3,
            0x9b1d_b13a_6e8e_3927,
            0x5f4f_e830_eff6_0791,
            u64::MAX,
        ];
        let mut x = 0x0123_4567_89ab_cdefu64;
        for &k in &keys {
            for i in 0..256u64 {
                let v = x.wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(i);
                let h = eval_round(v, k);
                assert_eq!(invert_round(h, k), Some(v));
                x = h;
            }
        }
        assert_eq!(invert_round(0, 2), None);
    }

    #[test]
    fn gf2_reduction_detects_contradictions_and_single_round_pivots() {
        let a = 0x3188_e5d3_9d63_b2d3;
        let b = 0x9b1d_b13a_6e8e_3927;
        let c = 0xd4a4_5b29_3511_446d;
        let x0 = 0xdead_beef_cafe_babeu64;
        let k_ab = eval_round(x0, a) ^ eval_round(x0, b);
        let k_bc = eval_round(x0, b) ^ eval_round(x0, c);
        let k_ac = eval_round(x0, a) ^ eval_round(x0, c);

        // Triangle contradiction: (a^b) ^ (b^c) != (a^c ^ 1)
        let bad_sys = System::new(vec![
            Equation::new(vec![a, b], k_ab),
            Equation::new(vec![b, c], k_bc),
            Equation::new(vec![a, c], k_ac ^ 1),
        ]);
        assert_eq!(bad_sys.reduce_gf2(), ReducedSystem::Unsatisfiable);

        // 3-way XOR + 2 pairs exposes 1-key pivot `H(x, c)` -> Unique(x0) in O(1)!
        let pivot_sys = System::new(vec![
            Equation::new(vec![a, b], k_ab),
            Equation::new(vec![a, b, c], k_ab ^ eval_round(x0, c)),
        ]);
        assert_eq!(pivot_sys.reduce_gf2(), ReducedSystem::Unique(x0));
    }

    #[test]
    fn registry_operators_pass_ext_contract_checks() {
        // Run full contract self-test via `Registry::builder().register(...)`!
        let reg = Registry::builder()
            .register(RoundOp::new())
            .unwrap()
            .register(UnroundOp::new())
            .unwrap()
            .build();
        let reg_exp = Registry::builder()
            .register(RoundOp::expanded())
            .unwrap()
            .register(UnroundOp::new())
            .unwrap()
            .build();
        let mut cx = Context::with_registry(ContextConfig::default(), Arc::new(reg));
        let x = cx.symbol("x", Width::W64).unwrap();
        let r = mk_round(&mut cx, x, 0x3188_e5d3_9d63_b2d3).unwrap();
        assert_eq!(match_round(&cx, r), Some((x, 0x3188_e5d3_9d63_b2d3)));

        let mut cx2 = Context::with_registry(ContextConfig::default(), Arc::new(reg_exp));
        let parsed = cx2
            .parse(
                "let %0 = (x:64 ^ 0x3188e5d39d63b2d3) * 0x3188e5d39d63b2d3; \
                 (%0 ^ %0 >>u 32 >>u (%0 >>u 60)) * 0x3188e5d39d63b2d3",
                &ParseOptions::width(Width::W64),
            )
            .unwrap();
        let folded = fold_rounds(&mut cx2, parsed).unwrap();
        assert_ne!(folded, parsed);
        let expanded = expand_rounds(&mut cx2, folded).unwrap();
        assert_eq!(expanded, parsed);
    }
}

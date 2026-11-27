//! 2-adic Hensel root-lifting engine for causal T-function equations and bit-vector systems
//! across widths `1..=512`.
//!
//! An operation `F` is *2-adically causal* (a T-function) when bit `k` of `F(x_0, ..., x_{m-1})`
//! depends only on bits `0..=k` of each input `x_j`. Arithmetic modulo `2^W` (`+`, `-`, `*`,
//! unary `-`), bitwise booleans (`~`, `&`, `|`, `^`), left shifts by constants, low-bit
//! truncations (`extract` from bit 0), concatenations, `zext`, `sext`, and `select` on a
//! bit-0 condition all preserve causality. Consequently, evaluating a causal DAG on `(k + 1)`-bit
//! prefixes (with bits `> k` cleared to zero) yields the exact bits `0..=k` of every node, so
//! roots can be lifted deterministically one bit level at a time (`k = 0..W_max`), pruning dead
//! branches as soon as a 2-adic obstruction arises.

use std::collections::BTreeSet;

use super::mul_inverse;
use crate::error::Error;
use crate::expr::{Context, Expr, OpCode};
use crate::facts::KnownBits;
use crate::hash::IdMap;
use crate::ops::{BinOp, UnOp};
use crate::value::wide::{self, Limbs, MAX_LIMBS};
use crate::{BitVec, SymbolKey, Width};

/// Hard ceiling on active symbols tracked in fixed-size prefix states.
const MAX_SYMS_HARD: usize = 8;
/// Maximum number of end-of-lift non-causal filter literals tested on lifted roots.
const MAX_SIDE_FILTERS: usize = 32;

/// Outcome of 2-adic Hensel root-lifting on a conjunction of predicates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum HenselOutcome {
    /// A concrete model verified on all input predicates.
    Sat(Vec<(SymbolKey, BitVec)>),
    /// Provably no assignment satisfies the predicates (a 2-adic obstruction at some bit k).
    Unsat,
    /// Outside the causal 2-adic fragment or exceeded the deterministic state/step budget.
    Unknown,
}

/// Deterministic resource bounds for [`solve`] and [`enumerate`].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) struct HenselLimits {
    /// Maximum active symbols (`1..=8`).
    pub(crate) max_symbols: usize,
    /// Maximum DAG nodes in the equation cone (`<= 512`).
    pub(crate) max_nodes: usize,
    /// Maximum surviving prefix states at any bit level k (`<= 1024`).
    pub(crate) max_states_per_level: usize,
    /// Maximum total node-evaluation steps (`<= 131_072`).
    pub(crate) max_steps: u64,
}

impl Default for HenselLimits {
    fn default() -> Self {
        Self {
            max_symbols: 6,
            max_nodes: 256,
            max_states_per_level: 512,
            max_steps: 65_536,
        }
    }
}

/// Solves `predicates` by 2-adic Hensel root-lifting within `limits`.
pub(crate) fn solve(
    cx: &Context,
    predicates: &[Expr],
    limits: &HenselLimits,
) -> Result<HenselOutcome, Error> {
    let pred_ids = validate_predicates(cx, predicates)?;
    if pred_ids.is_empty() {
        return Ok(HenselOutcome::Sat(Vec::new()));
    }

    let flat = match flatten_literals(cx, &pred_ids) {
        FlattenResult::Contradiction => return Ok(HenselOutcome::Unsat),
        FlattenResult::Literals(lits) => lits,
    };
    if flat.is_empty() {
        let model = default_model_for_roots(cx, &pred_ids)?;
        return Ok(if verify_predicates(cx, &pred_ids, &model)? {
            HenselOutcome::Sat(model)
        } else {
            HenselOutcome::Unknown
        });
    }

    let max_syms = limits.max_symbols.min(MAX_SYMS_HARD);
    if max_syms == 0 || limits.max_states_per_level == 0 {
        return Ok(HenselOutcome::Unknown);
    }

    let scan_cap = limits.max_nodes.saturating_mul(16).max(2048);
    let classified = match classify_system(cx, &flat, scan_cap)? {
        ClassifyResult::Unsat => return Ok(HenselOutcome::Unsat),
        ClassifyResult::Ok(sys) => sys,
    };

    if classified.causal_eqs.is_empty() {
        // Without at least one causal equation pinning the symbols, do not brute-force side filters.
        if classified.side_filters.is_empty() {
            let model = default_model_for_roots(cx, &pred_ids)?;
            return Ok(if verify_predicates(cx, &pred_ids, &model)? {
                HenselOutcome::Sat(model)
            } else {
                HenselOutcome::Unknown
            });
        }
        return Ok(HenselOutcome::Unknown);
    }

    let mut steps: u64 = 0;
    // When there are no side filters, bits at or above `max_active_bits` do not affect any
    // causal equation and can be filled directly from `declared_known` without branching.
    let lift_full_width = !classified.side_filters.is_empty();
    let lifted = match lift_causal(
        cx,
        &classified.causal_eqs,
        limits,
        max_syms,
        lift_full_width,
        &mut steps,
    )? {
        LiftResult::Unsat => return Ok(HenselOutcome::Unsat),
        LiftResult::Unknown => return Ok(HenselOutcome::Unknown),
        LiftResult::Roots { syms, states } => (syms, states),
    };
    let (causal_syms, causal_states) = lifted;

    if classified.side_filters.len() > MAX_SIDE_FILTERS {
        return Ok(HenselOutcome::Unknown);
    }

    // Collect all symbols appearing in the input predicates so the returned model is complete
    // and any extra symbols in side filters are accounted for soundly.
    let Some(all_pred_nodes) = collect_cone_bounded(cx, &pred_ids, scan_cap) else {
        return Ok(HenselOutcome::Unknown);
    };
    let all_syms = collect_symbols_sorted(cx, &all_pred_nodes);

    if classified.side_filters.is_empty() {
        // Any lifted root satisfies all causal equations; build complete model and verify.
        if let Some(state) = causal_states.first() {
            let model = build_model(cx, &all_syms, &causal_syms, state);
            if model_satisfies_declared(&all_syms, &model)
                && verify_predicates_counted(
                    cx,
                    &all_pred_nodes,
                    &pred_ids,
                    &model,
                    limits.max_steps,
                    &mut steps,
                )? == Some(true)
            {
                return Ok(HenselOutcome::Sat(model));
            }
        }
        return Ok(HenselOutcome::Unknown);
    }

    // Side filters are present: check whether any symbols appear only outside `causal_syms`.
    let extra_syms: Vec<SymInfo> = all_syms
        .iter()
        .filter(|s| !causal_syms.iter().any(|cs| cs.sym_idx == s.sym_idx))
        .cloned()
        .collect();

    let (full_syms, full_states, exhaustive_extra) = if extra_syms.is_empty() {
        (causal_syms, causal_states, true)
    } else if causal_syms.len() + extra_syms.len() <= max_syms {
        match expand_extra_symbols(
            &causal_syms,
            &causal_states,
            &extra_syms,
            limits.max_states_per_level,
        ) {
            Some((merged_syms, merged_states)) => (merged_syms, merged_states, true),
            None => (causal_syms, causal_states, false),
        }
    } else {
        (causal_syms, causal_states, false)
    };

    for state in &full_states {
        let model = build_model(cx, &all_syms, &full_syms, state);
        if !model_satisfies_declared(&all_syms, &model) {
            continue;
        }
        match verify_predicates_counted(
            cx,
            &all_pred_nodes,
            &pred_ids,
            &model,
            limits.max_steps,
            &mut steps,
        )? {
            Some(true) => return Ok(HenselOutcome::Sat(model)),
            Some(false) => {}
            None => return Ok(HenselOutcome::Unknown),
        }
    }

    Ok(if exhaustive_extra {
        HenselOutcome::Unsat
    } else {
        HenselOutcome::Unknown
    })
}

/// Enumerates all distinct values `target` can take under `predicates` when complete and at most
/// `limit` distinct values exist; returns `Ok(None)` if undecided or more than `limit` values exist.
pub(crate) fn enumerate(
    cx: &Context,
    predicates: &[Expr],
    target: Expr,
    limit: usize,
    limits: &HenselLimits,
) -> Result<Option<Vec<BitVec>>, Error> {
    let pred_ids = validate_predicates(cx, predicates)?;
    let target_id = cx.id(target)?;

    let flat = match flatten_literals(cx, &pred_ids) {
        FlattenResult::Contradiction => return Ok(Some(Vec::new())),
        FlattenResult::Literals(lits) => lits,
    };

    let max_syms = limits.max_symbols.min(MAX_SYMS_HARD);
    let scan_cap = limits.max_nodes.saturating_mul(16).max(2048);

    let classified = match classify_system(cx, &flat, scan_cap)? {
        ClassifyResult::Unsat => return Ok(Some(Vec::new())),
        ClassifyResult::Ok(sys) => sys,
    };

    if classified.side_filters.len() > MAX_SIDE_FILTERS {
        return Ok(None);
    }

    let mut roots_for_eval = pred_ids.clone();
    roots_for_eval.push(target_id);
    let Some(eval_cone) = collect_cone_bounded(cx, &roots_for_eval, scan_cap) else {
        return Ok(None);
    };
    let all_syms = collect_symbols_sorted(cx, &eval_cone);

    // Constant / symbol-free fast path when no predicates remain.
    if all_syms.is_empty() {
        let mut steps = 0u64;
        let model = Vec::new();
        if verify_predicates_counted(
            cx,
            &eval_cone,
            &pred_ids,
            &model,
            limits.max_steps,
            &mut steps,
        )? != Some(true)
        {
            return Ok(Some(Vec::new()));
        }
        let tv = eval_single_in_cone(cx, &eval_cone, target_id, &model)?;
        return Ok((1 <= limit).then(|| vec![tv]));
    }

    if max_syms == 0 || limits.max_states_per_level == 0 {
        return Ok(None);
    }

    let mut steps: u64 = 0;
    let (causal_syms, causal_states) = if classified.causal_eqs.is_empty() {
        if !classified.side_filters.is_empty() {
            return Ok(None);
        }
        (Vec::new(), vec![[ZERO_LIMBS; MAX_SYMS_HARD]])
    } else {
        match lift_causal(
            cx,
            &classified.causal_eqs,
            limits,
            max_syms,
            true,
            &mut steps,
        )? {
            LiftResult::Unsat => return Ok(Some(Vec::new())),
            LiftResult::Unknown => return Ok(None),
            LiftResult::Roots { syms, states } => (syms, states),
        }
    };

    // Any symbol in `predicates` or `target` not already in `causal_syms` must be expanded
    // completely so we neither miss a `target` value nor miss a `side_filters` witness.
    let extra_syms: Vec<SymInfo> = all_syms
        .iter()
        .filter(|s| !causal_syms.iter().any(|cs| cs.sym_idx == s.sym_idx))
        .cloned()
        .collect();

    let (full_syms, full_states) = if extra_syms.is_empty() {
        (causal_syms, causal_states)
    } else {
        if causal_syms.len() + extra_syms.len() > max_syms {
            return Ok(None);
        }
        let Some(expanded) = expand_extra_symbols(
            &causal_syms,
            &causal_states,
            &extra_syms,
            limits.max_states_per_level,
        ) else {
            return Ok(None);
        };
        expanded
    };

    let mut distinct: BTreeSet<BitVec> = BTreeSet::new();
    let eval_plan = EvalCone::new(&eval_cone);
    let mut reg_buf = vec![BitVec::zero(Width::W1); eval_cone.len()];

    for state in &full_states {
        let model = build_model(cx, &all_syms, &full_syms, state);
        if !model_satisfies_declared(&all_syms, &model) {
            continue;
        }
        steps = steps.saturating_add(eval_cone.len().max(1) as u64);
        if steps > limits.max_steps {
            return Ok(None);
        }
        eval_plan.run(cx, &model, &mut reg_buf)?;
        let preds_hold = pred_ids
            .iter()
            .all(|&pid| reg_buf[eval_plan.slot(pid)].bit(0) == Some(true));
        if !preds_hold {
            continue;
        }
        let tv = reg_buf[eval_plan.slot(target_id)];
        if distinct.insert(tv) && distinct.len() > limit {
            return Ok(None);
        }
    }

    Ok(Some(distinct.into_iter().collect()))
}

// ----- helpers & IR classification ---------------------------------------------------------------

const ZERO_LIMBS: Limbs = [0; MAX_LIMBS];

fn small_limbs(v: u64) -> Limbs {
    let mut l = ZERO_LIMBS;
    l[0] = v;
    l
}

fn validate_predicates(cx: &Context, predicates: &[Expr]) -> Result<Vec<u32>, Error> {
    let mut ids = Vec::with_capacity(predicates.len());
    for &p in predicates {
        let id = cx.id(p)?;
        if cx.wid(id) != 1 {
            return Err(Error::Unsupported("predicate must be 1 bit".into()));
        }
        ids.push(id);
    }
    Ok(ids)
}

enum FlattenResult {
    Contradiction,
    Literals(Vec<(u32, bool)>),
}

/// Flattens top-level `And`, `Not`, and negated `Or` into atomic 1-bit `(node_id, want)` literals.
fn flatten_literals(cx: &Context, roots: &[u32]) -> FlattenResult {
    let mut out = Vec::new();
    let mut seen: IdMap<u64, ()> = IdMap::default();
    let mut stack: Vec<(u32, bool)> = roots.iter().rev().map(|&id| (id, true)).collect();

    while let Some((mut id, mut want)) = stack.pop() {
        while cx.node(id).op == OpCode::Not {
            id = cx.node(id).a;
            want = !want;
        }
        let key = (u64::from(id) << 1) | u64::from(want);
        if seen.insert(key, ()).is_some() {
            continue;
        }
        let opp_key = (u64::from(id) << 1) | u64::from(!want);
        if seen.contains_key(&opp_key) {
            return FlattenResult::Contradiction;
        }
        if let Some(c) = cx.const_val(id) {
            if (c.bit(0) == Some(true)) != want {
                return FlattenResult::Contradiction;
            }
            continue;
        }
        let n = cx.node(id);
        if n.op == OpCode::And && want {
            stack.push((n.b, true));
            stack.push((n.a, true));
            continue;
        }
        if n.op == OpCode::Or && !want {
            stack.push((n.b, false));
            stack.push((n.a, false));
            continue;
        }
        out.push((id, want));
    }
    FlattenResult::Literals(out)
}

#[derive(Clone, Debug)]
enum CausalEq {
    /// `(node & mask) == target` on bits `0..active_bits`.
    ConstMask {
        node: u32,
        target: Limbs,
        mask: Limbs,
        active_bits: u16,
    },
    /// `a == b` (or `(a ^ b) == 1` at bit 0 when `xor_bit0` is true) on bits `0..active_bits`.
    Pair {
        a: u32,
        b: u32,
        active_bits: u16,
        xor_bit0: bool,
    },
}

struct ClassifiedSystem {
    causal_eqs: Vec<CausalEq>,
    side_filters: Vec<(u32, bool)>,
}

enum ClassifyResult {
    Unsat,
    Ok(ClassifiedSystem),
}

#[derive(Copy, Clone, Debug)]
struct NodeCausal {
    has_syms: bool,
    /// Number of low bits `0..causal_bits` whose values at bit `k` depend only on symbol bits `<= k`.
    causal_bits: u16,
}

type ConeAnalysis = (IdMap<u32, NodeCausal>, IdMap<u32, BitVec>);

/// Computes `NodeCausal` and constant values for symbol-free subexpressions over `cone`.
fn analyze_cone(cx: &Context, cone: &[u32]) -> Result<ConeAnalysis, Error> {
    let mut info: IdMap<u32, NodeCausal> = IdMap::default();
    let mut consts: IdMap<u32, BitVec> = IdMap::default();
    info.reserve(cone.len());

    for &id in cone {
        let n = cx.node(id);
        let w = n.width;
        if n.op == OpCode::Const {
            let v = cx
                .const_val(id)
                .unwrap_or_else(|| BitVec::zero(cx.width_of(id)));
            consts.insert(id, v);
            info.insert(
                id,
                NodeCausal {
                    has_syms: false,
                    causal_bits: w,
                },
            );
            continue;
        }
        if n.op == OpCode::Sym {
            info.insert(
                id,
                NodeCausal {
                    has_syms: true,
                    causal_bits: w,
                },
            );
            continue;
        }
        let has_syms = n.children().any(|c| info[&c].has_syms);
        if !has_syms {
            let v = cx.eval_node(id, |c| consts[&c], |_, _| None)?;
            consts.insert(id, v);
            info.insert(
                id,
                NodeCausal {
                    has_syms: false,
                    causal_bits: w,
                },
            );
            continue;
        }

        let ca = || info[&n.a].causal_bits;
        let cb = || info[&n.b].causal_bits;
        let causal_bits = match n.op {
            OpCode::Not | OpCode::Neg => ca(),
            OpCode::Add | OpCode::Sub | OpCode::Mul | OpCode::Xor => ca().min(cb()),
            OpCode::And => {
                let base = ca().min(cb());
                let masked = consts
                    .get(&n.b)
                    .map(|m| (n.a, m))
                    .or_else(|| consts.get(&n.a).map(|m| (n.b, m)));
                if let Some((other, mask)) = masked {
                    let req = highest_set_bit_plus_one(mask.raw(), w);
                    if info[&other].causal_bits >= req {
                        w
                    } else {
                        base
                    }
                } else {
                    base
                }
            }
            OpCode::Or => {
                let base = ca().min(cb());
                let masked = consts
                    .get(&n.b)
                    .map(|m| (n.a, m))
                    .or_else(|| consts.get(&n.a).map(|m| (n.b, m)));
                if let Some((other, mask)) = masked {
                    let inv = wide::not(w, mask.raw());
                    let req = highest_set_bit_plus_one(&inv, w);
                    if info[&other].causal_bits >= req {
                        w
                    } else {
                        base
                    }
                } else {
                    base
                }
            }
            OpCode::Shl => match consts.get(&n.b) {
                Some(cnt) => match cnt.to_u64() {
                    Some(s) if s < u64::from(w) => (s as u16).saturating_add(ca()).min(w),
                    _ => w,
                },
                None => 0,
            },
            OpCode::Zext | OpCode::Sext => {
                let wa = cx.wid(n.a);
                let inner_c = ca();
                if inner_c == wa { w } else { inner_c }
            }
            OpCode::Extract => {
                if n.b == 0 {
                    ca().min(w)
                } else {
                    0
                }
            }
            OpCode::Concat => {
                let wlo = cx.wid(n.b);
                let clo = cb();
                if clo < wlo { clo } else { wlo + ca() }
            }
            OpCode::Select => {
                if ca() == 1 {
                    cb().min(info[&n.c].causal_bits)
                } else {
                    0
                }
            }
            OpCode::Eq | OpCode::Ne => {
                let wu = cx.wid(n.a);
                if (wu == 1 && ca() == 1 && cb() == 1)
                    || bit0_pinned_vs_const(cx, n.a, n.b, &info, &consts)
                    || bit0_pinned_vs_const(cx, n.b, n.a, &info, &consts)
                {
                    1
                } else {
                    0
                }
            }
            _ => 0,
        };

        info.insert(
            id,
            NodeCausal {
                has_syms: true,
                causal_bits,
            },
        );
    }

    Ok((info, consts))
}

/// Whether `u` depends at most on symbol bit 0 (via `& 1` or `| ~1`) and `v` is symbol-free.
fn bit0_pinned_vs_const(
    cx: &Context,
    u: u32,
    v: u32,
    info: &IdMap<u32, NodeCausal>,
    consts: &IdMap<u32, BitVec>,
) -> bool {
    if !consts.contains_key(&v) {
        return false;
    }
    let nu = cx.node(u);
    let w = nu.width;
    match nu.op {
        OpCode::And => {
            let pair = consts
                .get(&nu.b)
                .map(|m| (nu.a, m))
                .or_else(|| consts.get(&nu.a).map(|m| (nu.b, m)));
            pair.is_some_and(|(src, m)| {
                highest_set_bit_plus_one(m.raw(), w) <= 1 && info[&src].causal_bits >= 1
            })
        }
        OpCode::Or => {
            let pair = consts
                .get(&nu.b)
                .map(|m| (nu.a, m))
                .or_else(|| consts.get(&nu.a).map(|m| (nu.b, m)));
            pair.is_some_and(|(src, m)| {
                let inv = wide::not(w, m.raw());
                highest_set_bit_plus_one(&inv, w) <= 1 && info[&src].causal_bits >= 1
            })
        }
        _ => false,
    }
}

fn highest_set_bit_plus_one(limbs: &Limbs, w: u16) -> u16 {
    for idx in (0..wide::nlimbs(w)).rev() {
        let word = limbs[idx];
        if word != 0 {
            return (idx as u16) * 64 + (64 - word.leading_zeros() as u16);
        }
    }
    0
}

fn classify_system(
    cx: &Context,
    flat: &[(u32, bool)],
    scan_cap: usize,
) -> Result<ClassifyResult, Error> {
    let mut causal_eqs = Vec::new();
    let mut side_filters = Vec::new();

    for &(lit_id, want) in flat {
        let Some(cone) = collect_cone_bounded(cx, &[lit_id], scan_cap) else {
            side_filters.push((lit_id, want));
            continue;
        };
        let (info, consts) = analyze_cone(cx, &cone)?;
        match classify_one_literal(cx, lit_id, want, &info, &consts, &mut causal_eqs) {
            LitStatus::Unsat => return Ok(ClassifyResult::Unsat),
            LitStatus::Causal => {}
            LitStatus::NeedsSideFilter => side_filters.push((lit_id, want)),
        }
    }

    Ok(ClassifyResult::Ok(ClassifiedSystem {
        causal_eqs,
        side_filters,
    }))
}

enum LitStatus {
    Unsat,
    Causal,
    NeedsSideFilter,
}

fn classify_one_literal(
    cx: &Context,
    lit_id: u32,
    want: bool,
    info: &IdMap<u32, NodeCausal>,
    consts: &IdMap<u32, BitVec>,
    out_causal: &mut Vec<CausalEq>,
) -> LitStatus {
    if let Some(bv) = consts.get(&lit_id) {
        return if (bv.bit(0) == Some(true)) == want {
            LitStatus::Causal
        } else {
            LitStatus::Unsat
        };
    }

    let n = cx.node(lit_id);
    match (n.op, want) {
        (OpCode::Eq, true) | (OpCode::Ne, false) => {
            decompose_equality(cx, n.a, n.b, info, consts, out_causal)
        }
        (OpCode::Ne, true) | (OpCode::Eq, false) => {
            if n.a == n.b {
                return LitStatus::Unsat;
            }
            if let (Some(ca), Some(cb)) = (consts.get(&n.a), consts.get(&n.b)) {
                return if ca != cb {
                    LitStatus::Causal
                } else {
                    LitStatus::Unsat
                };
            }
            if cx.wid(n.a) == 1 {
                if let Some(&c) = consts.get(&n.b) {
                    let flipped = BitVec::from_bool(c.is_zero());
                    return classify_const_eq(cx, n.a, flipped, info, consts, out_causal);
                }
                if let Some(&c) = consts.get(&n.a) {
                    let flipped = BitVec::from_bool(c.is_zero());
                    return classify_const_eq(cx, n.b, flipped, info, consts, out_causal);
                }
                if info[&n.a].causal_bits == 1 && info[&n.b].causal_bits == 1 {
                    out_causal.push(CausalEq::Pair {
                        a: n.a,
                        b: n.b,
                        active_bits: 1,
                        xor_bit0: true,
                    });
                    return LitStatus::Causal;
                }
            }
            LitStatus::NeedsSideFilter
        }
        _ => {
            if n.op == OpCode::Extract && n.b == 0 && info[&n.a].causal_bits >= 1 {
                out_causal.push(CausalEq::ConstMask {
                    node: n.a,
                    target: small_limbs(u64::from(want)),
                    mask: small_limbs(1),
                    active_bits: 1,
                });
                return LitStatus::Causal;
            }
            if info[&lit_id].causal_bits == 1 {
                out_causal.push(CausalEq::ConstMask {
                    node: lit_id,
                    target: small_limbs(u64::from(want)),
                    mask: small_limbs(1),
                    active_bits: 1,
                });
                return LitStatus::Causal;
            }
            LitStatus::NeedsSideFilter
        }
    }
}

fn decompose_equality(
    cx: &Context,
    lhs: u32,
    rhs: u32,
    info: &IdMap<u32, NodeCausal>,
    consts: &IdMap<u32, BitVec>,
    out_causal: &mut Vec<CausalEq>,
) -> LitStatus {
    let mut stack = vec![(lhs, rhs)];
    let mut all_causal = true;

    while let Some((mut a, mut b)) = stack.pop() {
        if a == b {
            continue;
        }
        match (consts.get(&a), consts.get(&b)) {
            (Some(ca), Some(cb)) => {
                if ca != cb {
                    return LitStatus::Unsat;
                }
                continue;
            }
            (None, Some(&c)) => {
                match peel_and_classify_const(cx, a, c, info, consts, out_causal) {
                    LitStatus::Unsat => return LitStatus::Unsat,
                    LitStatus::Causal => {}
                    LitStatus::NeedsSideFilter => all_causal = false,
                }
                continue;
            }
            (Some(&c), None) => {
                match peel_and_classify_const(cx, b, c, info, consts, out_causal) {
                    LitStatus::Unsat => return LitStatus::Unsat,
                    LitStatus::Causal => {}
                    LitStatus::NeedsSideFilter => all_causal = false,
                }
                continue;
            }
            (None, None) => {}
        }

        // Peel matching outer bijections / injections when not yet causal.
        let mut split = false;
        while a != b && (info[&a].causal_bits < cx.wid(a) || info[&b].causal_bits < cx.wid(b)) {
            let (na, nb) = (cx.node(a), cx.node(b));
            if na.op != nb.op || na.width != nb.width {
                break;
            }
            match na.op {
                OpCode::Not | OpCode::Neg | OpCode::Bswap | OpCode::BitRev => {
                    (a, b) = (na.a, nb.a);
                }
                OpCode::Zext | OpCode::Sext if cx.wid(na.a) == cx.wid(nb.a) => {
                    (a, b) = (na.a, nb.a);
                }
                OpCode::RotL | OpCode::RotR if na.b == nb.b => {
                    (a, b) = (na.a, nb.a);
                }
                OpCode::Concat if cx.wid(na.b) == cx.wid(nb.b) => {
                    stack.push((na.a, nb.a));
                    stack.push((na.b, nb.b));
                    split = true;
                    break;
                }
                _ => break,
            }
        }
        if split || a == b {
            continue;
        }
        let w = cx.wid(a);
        if info[&a].causal_bits == w && info[&b].causal_bits == w {
            out_causal.push(CausalEq::Pair {
                a,
                b,
                active_bits: w,
                xor_bit0: false,
            });
        } else {
            all_causal = false;
        }
    }

    if all_causal {
        LitStatus::Causal
    } else {
        LitStatus::NeedsSideFilter
    }
}

fn peel_and_classify_const(
    cx: &Context,
    mut expr: u32,
    mut c: BitVec,
    info: &IdMap<u32, NodeCausal>,
    consts: &IdMap<u32, BitVec>,
    out_causal: &mut Vec<CausalEq>,
) -> LitStatus {
    let mut depth = 0u32;
    while depth < 64 {
        depth += 1;
        if let Some(ev) = consts.get(&expr) {
            return if *ev == c {
                LitStatus::Causal
            } else {
                LitStatus::Unsat
            };
        }
        let n = cx.node(expr);
        if c.is_zero() && n.op == OpCode::Or {
            let s1 = peel_and_classify_const(cx, n.a, c, info, consts, out_causal);
            if matches!(s1, LitStatus::Unsat) {
                return LitStatus::Unsat;
            }
            let s2 = peel_and_classify_const(cx, n.b, c, info, consts, out_causal);
            if matches!(s2, LitStatus::Unsat) {
                return LitStatus::Unsat;
            }
            return if matches!((s1, s2), (LitStatus::Causal, LitStatus::Causal)) {
                LitStatus::Causal
            } else {
                LitStatus::NeedsSideFilter
            };
        }
        if c.is_ones() && n.op == OpCode::And {
            let s1 = peel_and_classify_const(cx, n.a, c, info, consts, out_causal);
            if matches!(s1, LitStatus::Unsat) {
                return LitStatus::Unsat;
            }
            let s2 = peel_and_classify_const(cx, n.b, c, info, consts, out_causal);
            if matches!(s2, LitStatus::Unsat) {
                return LitStatus::Unsat;
            }
            return if matches!((s1, s2), (LitStatus::Causal, LitStatus::Causal)) {
                LitStatus::Causal
            } else {
                LitStatus::NeedsSideFilter
            };
        }
        if n.op == OpCode::Concat {
            let wlo = cx.width_of(n.b);
            let whi = cx.width_of(n.a);
            let (Ok(chi), Ok(clo)) = (c.extract(wlo.bits(), whi), c.trunc(wlo)) else {
                break;
            };
            let s1 = peel_and_classify_const(cx, n.b, clo, info, consts, out_causal);
            if matches!(s1, LitStatus::Unsat) {
                return LitStatus::Unsat;
            }
            let s2 = peel_and_classify_const(cx, n.a, chi, info, consts, out_causal);
            if matches!(s2, LitStatus::Unsat) {
                return LitStatus::Unsat;
            }
            return if matches!((s1, s2), (LitStatus::Causal, LitStatus::Causal)) {
                LitStatus::Causal
            } else {
                LitStatus::NeedsSideFilter
            };
        }

        // Only peel further when `expr` is not already causal (or is a cast whose range check
        // could refute `c` immediately).
        if info[&expr].causal_bits == n.width && !matches!(n.op, OpCode::Zext | OpCode::Sext) {
            break;
        }

        match n.op {
            OpCode::Not => {
                expr = n.a;
                c = BitVec::un_unchecked(UnOp::Not, &c);
            }
            OpCode::Neg => {
                expr = n.a;
                c = BitVec::un_unchecked(UnOp::Neg, &c);
            }
            OpCode::Bswap => {
                expr = n.a;
                c = BitVec::un_unchecked(UnOp::Bswap, &c);
            }
            OpCode::BitRev => {
                expr = n.a;
                c = BitVec::un_unchecked(UnOp::BitRev, &c);
            }
            OpCode::Add => {
                if let Some(k) = consts.get(&n.b) {
                    expr = n.a;
                    c = BitVec::bin_unchecked(BinOp::Sub, &c, k);
                } else if let Some(k) = consts.get(&n.a) {
                    expr = n.b;
                    c = BitVec::bin_unchecked(BinOp::Sub, &c, k);
                } else {
                    break;
                }
            }
            OpCode::Sub => {
                if let Some(k) = consts.get(&n.b) {
                    expr = n.a;
                    c = BitVec::bin_unchecked(BinOp::Add, &c, k);
                } else if let Some(k) = consts.get(&n.a) {
                    expr = n.b;
                    c = BitVec::bin_unchecked(BinOp::Sub, k, &c);
                } else {
                    break;
                }
            }
            OpCode::Xor => {
                if let Some(k) = consts.get(&n.b) {
                    expr = n.a;
                    c = BitVec::bin_unchecked(BinOp::Xor, &c, k);
                } else if let Some(k) = consts.get(&n.a) {
                    expr = n.b;
                    c = BitVec::bin_unchecked(BinOp::Xor, &c, k);
                } else {
                    break;
                }
            }
            OpCode::Mul => {
                let const_factor = consts
                    .get(&n.b)
                    .map(|k| (n.a, k))
                    .or_else(|| consts.get(&n.a).map(|k| (n.b, k)));
                if let Some((other, k)) = const_factor
                    && let Some(inv) = mul_inverse(k)
                {
                    expr = other;
                    c = BitVec::bin_unchecked(BinOp::Mul, &c, &inv);
                } else {
                    break;
                }
            }
            OpCode::RotL => {
                if let Some(k) = consts.get(&n.b) {
                    expr = n.a;
                    c = BitVec::bin_unchecked(BinOp::RotR, &c, k);
                } else {
                    break;
                }
            }
            OpCode::RotR => {
                if let Some(k) = consts.get(&n.b) {
                    expr = n.a;
                    c = BitVec::bin_unchecked(BinOp::RotL, &c, k);
                } else {
                    break;
                }
            }
            OpCode::Zext => {
                let wa = cx.width_of(n.a);
                let Ok(t) = c.trunc(wa) else { break };
                let Ok(back) = t.zext(c.width()) else { break };
                if back != c {
                    return LitStatus::Unsat;
                }
                expr = n.a;
                c = t;
            }
            OpCode::Sext => {
                let wa = cx.width_of(n.a);
                let Ok(t) = c.trunc(wa) else { break };
                let Ok(back) = t.sext(c.width()) else { break };
                if back != c {
                    return LitStatus::Unsat;
                }
                expr = n.a;
                c = t;
            }
            _ => break,
        }
    }

    classify_const_eq(cx, expr, c, info, consts, out_causal)
}

fn classify_const_eq(
    cx: &Context,
    expr: u32,
    c: BitVec,
    info: &IdMap<u32, NodeCausal>,
    consts: &IdMap<u32, BitVec>,
    out_causal: &mut Vec<CausalEq>,
) -> LitStatus {
    if let Some(ev) = consts.get(&expr) {
        return if *ev == c {
            LitStatus::Causal
        } else {
            LitStatus::Unsat
        };
    }
    let n = cx.node(expr);
    let w = n.width;

    // Masked equality `(inner & mask) == c` or `(inner | mask) == c`.
    if n.op == OpCode::And {
        let masked = consts
            .get(&n.b)
            .map(|m| (n.a, m))
            .or_else(|| consts.get(&n.a).map(|m| (n.b, m)));
        if let Some((inner, mask)) = masked {
            let not_m = BitVec::un_unchecked(UnOp::Not, mask);
            if !BitVec::bin_unchecked(BinOp::And, &c, &not_m).is_zero() {
                return LitStatus::Unsat;
            }
            let req = highest_set_bit_plus_one(mask.raw(), w);
            if req == 0 {
                return LitStatus::Causal;
            }
            if info[&inner].causal_bits >= req {
                out_causal.push(CausalEq::ConstMask {
                    node: inner,
                    target: *c.raw(),
                    mask: *mask.raw(),
                    active_bits: req,
                });
                return LitStatus::Causal;
            }
        }
    }
    if n.op == OpCode::Or {
        let masked = consts
            .get(&n.b)
            .map(|m| (n.a, m))
            .or_else(|| consts.get(&n.a).map(|m| (n.b, m)));
        if let Some((inner, mask)) = masked {
            let not_c = BitVec::un_unchecked(UnOp::Not, &c);
            if !BitVec::bin_unchecked(BinOp::And, &not_c, mask).is_zero() {
                return LitStatus::Unsat;
            }
            let not_m = BitVec::un_unchecked(UnOp::Not, mask);
            let target_masked = BitVec::bin_unchecked(BinOp::And, &c, &not_m);
            let req = highest_set_bit_plus_one(not_m.raw(), w);
            if req == 0 {
                return LitStatus::Causal;
            }
            if info[&inner].causal_bits >= req {
                out_causal.push(CausalEq::ConstMask {
                    node: inner,
                    target: *target_masked.raw(),
                    mask: *not_m.raw(),
                    active_bits: req,
                });
                return LitStatus::Causal;
            }
        }
    }

    if info[&expr].causal_bits == w {
        out_causal.push(CausalEq::ConstMask {
            node: expr,
            target: *c.raw(),
            mask: wide::ones(w),
            active_bits: w,
        });
        return LitStatus::Causal;
    }

    LitStatus::NeedsSideFilter
}

// ----- compiled causal DAG & 2-adic lifting ------------------------------------------------------

#[derive(Clone, Debug)]
struct SymInfo {
    sym_idx: u32,
    key: SymbolKey,
    width: Width,
    known: Option<KnownBits>,
}

impl SymInfo {
    fn fixed_bit(&self, k: u16) -> Option<bool> {
        self.known.as_ref()?.bit(k)
    }

    fn default_limbs(&self) -> Limbs {
        self.known.map_or(ZERO_LIMBS, |kb| *kb.known_one().raw())
    }
}

#[derive(Copy, Clone, Debug)]
enum DagOp {
    Not(u16),
    Neg(u16),
    Add(u16, u16),
    Sub(u16, u16),
    Mul(u16, u16),
    And(u16, u16),
    Or(u16, u16),
    Xor(u16, u16),
    ShlConst(u16, u16),
    Zext(u16),
    Sext { src: u16, from_bits: u16 },
    Trunc(u16),
    Concat { hi: u16, lo: u16, lo_bits: u16 },
    Select { cond: u16, then_v: u16, else_v: u16 },
    Eq(u16, u16),
    Ne(u16, u16),
}

#[derive(Copy, Clone, Debug)]
struct DagInst {
    dst: u16,
    width: u16,
    op: DagOp,
}

#[derive(Clone, Debug)]
enum CompiledEq {
    ConstMask {
        reg: u16,
        target: Limbs,
        mask: Limbs,
        active_bits: u16,
    },
    Pair {
        a: u16,
        b: u16,
        active_bits: u16,
        xor_bit0: bool,
    },
}

enum LiftResult {
    Unsat,
    Unknown,
    Roots {
        syms: Vec<SymInfo>,
        states: Vec<[Limbs; MAX_SYMS_HARD]>,
    },
}

fn lift_causal(
    cx: &Context,
    causal_eqs: &[CausalEq],
    limits: &HenselLimits,
    max_syms: usize,
    lift_full_width: bool,
    steps: &mut u64,
) -> Result<LiftResult, Error> {
    let mut eq_roots = Vec::with_capacity(causal_eqs.len() * 2);
    for eq in causal_eqs {
        match *eq {
            CausalEq::ConstMask { node, .. } => eq_roots.push(node),
            CausalEq::Pair { a, b, .. } => {
                eq_roots.push(a);
                eq_roots.push(b);
            }
        }
    }

    // Collect the causal cone, pruning symbol-free subtrees past their root after evaluation.
    let Some(raw_cone) =
        collect_cone_bounded(cx, &eq_roots, limits.max_nodes.saturating_mul(4).max(512))
    else {
        return Ok(LiftResult::Unknown);
    };
    let (info, consts) = analyze_cone(cx, &raw_cone)?;

    // Prune symbol-free subtrees so constant expressions count as single `Const` leaves.
    let cone = collect_causal_cone_pruned(cx, &eq_roots, &info);
    if cone.len() > limits.max_nodes {
        return Ok(LiftResult::Unknown);
    }

    let syms = collect_symbols_sorted(cx, &cone);
    if syms.len() > max_syms {
        return Ok(LiftResult::Unknown);
    }

    let mut sym_pos: IdMap<u32, usize> = IdMap::default();
    for (idx, s) in syms.iter().enumerate() {
        sym_pos.insert(s.sym_idx, idx);
    }

    let mut slot_of: IdMap<u32, u16> = IdMap::default();
    slot_of.reserve(cone.len());
    let mut init_regs: Vec<Limbs> = Vec::with_capacity(cone.len());
    let mut sym_slots = [u16::MAX; MAX_SYMS_HARD];
    let mut insts: Vec<DagInst> = Vec::with_capacity(cone.len());
    let mut max_node_width: u16 = 1;

    for &id in &cone {
        let dst = init_regs.len() as u16;
        slot_of.insert(id, dst);
        let n = cx.node(id);
        let w = n.width;
        max_node_width = max_node_width.max(w);

        if !info[&id].has_syms {
            init_regs.push(*consts[&id].raw());
            continue;
        }
        init_regs.push(ZERO_LIMBS);
        if n.op == OpCode::Sym {
            let s_idx = sym_pos[&n.a];
            sym_slots[s_idx] = dst;
            continue;
        }

        let op = match n.op {
            OpCode::Not => DagOp::Not(slot_of[&n.a]),
            OpCode::Neg => DagOp::Neg(slot_of[&n.a]),
            OpCode::Add => DagOp::Add(slot_of[&n.a], slot_of[&n.b]),
            OpCode::Sub => DagOp::Sub(slot_of[&n.a], slot_of[&n.b]),
            OpCode::Mul => DagOp::Mul(slot_of[&n.a], slot_of[&n.b]),
            OpCode::And => DagOp::And(slot_of[&n.a], slot_of[&n.b]),
            OpCode::Or => DagOp::Or(slot_of[&n.a], slot_of[&n.b]),
            OpCode::Xor => DagOp::Xor(slot_of[&n.a], slot_of[&n.b]),
            OpCode::Shl => {
                let Some(cnt) = consts.get(&n.b) else {
                    return Ok(LiftResult::Unknown);
                };
                let s = cnt.to_u64().map_or(w, |v| (v as u16).min(w));
                DagOp::ShlConst(slot_of[&n.a], s)
            }
            OpCode::Zext => DagOp::Zext(slot_of[&n.a]),
            OpCode::Sext => DagOp::Sext {
                src: slot_of[&n.a],
                from_bits: cx.wid(n.a),
            },
            OpCode::Extract if n.b == 0 => DagOp::Trunc(slot_of[&n.a]),
            OpCode::Concat => DagOp::Concat {
                hi: slot_of[&n.a],
                lo: slot_of[&n.b],
                lo_bits: cx.wid(n.b),
            },
            OpCode::Select => DagOp::Select {
                cond: slot_of[&n.a],
                then_v: slot_of[&n.b],
                else_v: slot_of[&n.c],
            },
            OpCode::Eq => DagOp::Eq(slot_of[&n.a], slot_of[&n.b]),
            OpCode::Ne => DagOp::Ne(slot_of[&n.a], slot_of[&n.b]),
            _ => return Ok(LiftResult::Unknown),
        };
        insts.push(DagInst { dst, width: w, op });
    }

    let mut compiled_eqs = Vec::with_capacity(causal_eqs.len());
    let mut max_eq_bits: u16 = 0;
    for eq in causal_eqs {
        match *eq {
            CausalEq::ConstMask {
                node,
                target,
                mask,
                active_bits,
            } => {
                max_eq_bits = max_eq_bits.max(active_bits);
                compiled_eqs.push(CompiledEq::ConstMask {
                    reg: slot_of[&node],
                    target,
                    mask,
                    active_bits,
                });
            }
            CausalEq::Pair {
                a,
                b,
                active_bits,
                xor_bit0,
            } => {
                max_eq_bits = max_eq_bits.max(active_bits);
                compiled_eqs.push(CompiledEq::Pair {
                    a: slot_of[&a],
                    b: slot_of[&b],
                    active_bits,
                    xor_bit0,
                });
            }
        }
    }

    let max_sym_bits = syms.iter().map(|s| s.width.bits()).max().unwrap_or(0);
    let w_stop = if lift_full_width {
        max_sym_bits.max(max_eq_bits)
    } else {
        max_eq_bits
    };

    if max_node_width <= 64 {
        lift_narrow(
            syms,
            &sym_slots,
            &init_regs,
            &insts,
            &compiled_eqs,
            w_stop,
            lift_full_width,
            limits,
            steps,
        )
    } else {
        lift_wide(
            syms,
            &sym_slots,
            &init_regs,
            &insts,
            &compiled_eqs,
            w_stop,
            lift_full_width,
            limits,
            steps,
        )
    }
}

#[inline]
fn mask64(w: u16) -> u64 {
    if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
}

#[expect(clippy::too_many_arguments, reason = "compiled DAG tables passed flat")]
fn lift_narrow(
    syms: Vec<SymInfo>,
    sym_slots: &[u16; MAX_SYMS_HARD],
    init_regs: &[Limbs],
    insts: &[DagInst],
    eqs: &[CompiledEq],
    w_stop: u16,
    lift_full_width: bool,
    limits: &HenselLimits,
    steps: &mut u64,
) -> Result<LiftResult, Error> {
    let m = syms.len();
    let mut regs: Vec<u64> = init_regs.iter().map(|l| l[0]).collect();
    let step_cost = insts.len().max(1) as u64;

    let mut states: Vec<[u64; MAX_SYMS_HARD]> = vec![[0u64; MAX_SYMS_HARD]];
    let mut next_states: Vec<[u64; MAX_SYMS_HARD]> = Vec::new();

    for k in 0..w_stop {
        next_states.clear();
        let bit_mask = if k < 64 { 1u64 << k } else { 0 };

        // Partition symbols at level `k` into forced-1 bits and branching free bits.
        let mut forced_ones = [0u64; MAX_SYMS_HARD];
        let mut free_syms = [0usize; MAX_SYMS_HARD];
        let mut num_free = 0usize;
        for (j, s) in syms.iter().enumerate() {
            if k >= s.width.bits() {
                continue;
            }
            match s.fixed_bit(k) {
                Some(true) => forced_ones[j] = bit_mask,
                Some(false) => {}
                None => {
                    free_syms[num_free] = j;
                    num_free += 1;
                }
            }
        }

        let combos = 1usize << num_free;
        for base in &states {
            for choice in 0..combos {
                *steps = steps.saturating_add(step_cost);
                if *steps > limits.max_steps {
                    return Ok(LiftResult::Unknown);
                }

                let mut cand = *base;
                for j in 0..m {
                    cand[j] |= forced_ones[j];
                }
                for (b_idx, &sym_j) in free_syms[..num_free].iter().enumerate() {
                    if (choice >> b_idx) & 1 != 0 {
                        cand[sym_j] |= bit_mask;
                    }
                }
                for j in 0..m {
                    let slot = sym_slots[j];
                    if slot != u16::MAX {
                        regs[slot as usize] = cand[j];
                    }
                }

                eval_dag_narrow(&mut regs, insts);
                if check_eqs_narrow(&regs, eqs, k) {
                    if next_states.len() >= limits.max_states_per_level {
                        return Ok(LiftResult::Unknown);
                    }
                    next_states.push(cand);
                }
            }
        }

        if next_states.is_empty() {
            return Ok(LiftResult::Unsat);
        }
        core::mem::swap(&mut states, &mut next_states);
    }

    // Complete any remaining high bits `w_stop..width` using `declared_known` when `solve`
    // stopped early (`!lift_full_width`).
    let mut wide_states = Vec::with_capacity(states.len());
    for st in states {
        let mut out = [ZERO_LIMBS; MAX_SYMS_HARD];
        for (j, s) in syms.iter().enumerate() {
            let mut v = st[j];
            if !lift_full_width && w_stop < s.width.bits() {
                let high_mask = if w_stop >= 64 {
                    0
                } else {
                    !((1u64 << w_stop) - 1) & mask64(s.width.bits())
                };
                v |= s.default_limbs()[0] & high_mask;
            }
            out[j][0] = v;
        }
        wide_states.push(out);
    }

    Ok(LiftResult::Roots {
        syms,
        states: wide_states,
    })
}

#[inline]
fn eval_dag_narrow(regs: &mut [u64], insts: &[DagInst]) {
    for inst in insts {
        let m = mask64(inst.width);
        let v = match inst.op {
            DagOp::Not(a) => !regs[a as usize] & m,
            DagOp::Neg(a) => regs[a as usize].wrapping_neg() & m,
            DagOp::Add(a, b) => regs[a as usize].wrapping_add(regs[b as usize]) & m,
            DagOp::Sub(a, b) => regs[a as usize].wrapping_sub(regs[b as usize]) & m,
            DagOp::Mul(a, b) => regs[a as usize].wrapping_mul(regs[b as usize]) & m,
            DagOp::And(a, b) => regs[a as usize] & regs[b as usize],
            DagOp::Or(a, b) => regs[a as usize] | regs[b as usize],
            DagOp::Xor(a, b) => regs[a as usize] ^ regs[b as usize],
            DagOp::ShlConst(a, s) => {
                if s >= 64 {
                    0
                } else {
                    (regs[a as usize] << s) & m
                }
            }
            DagOp::Zext(a) => regs[a as usize],
            DagOp::Sext { src, from_bits } => {
                let sh = 64 - u32::from(from_bits);
                (((regs[src as usize] << sh) as i64 >> sh) as u64) & m
            }
            DagOp::Trunc(a) => regs[a as usize] & m,
            DagOp::Concat { hi, lo, lo_bits } => {
                let h = if lo_bits >= 64 {
                    0
                } else {
                    regs[hi as usize] << lo_bits
                };
                (h | regs[lo as usize]) & m
            }
            DagOp::Select {
                cond,
                then_v,
                else_v,
            } => {
                if regs[cond as usize] != 0 {
                    regs[then_v as usize]
                } else {
                    regs[else_v as usize]
                }
            }
            DagOp::Eq(a, b) => u64::from(regs[a as usize] == regs[b as usize]),
            DagOp::Ne(a, b) => u64::from(regs[a as usize] != regs[b as usize]),
        };
        regs[inst.dst as usize] = v;
    }
}

#[inline]
fn check_eqs_narrow(regs: &[u64], eqs: &[CompiledEq], k: u16) -> bool {
    for eq in eqs {
        match *eq {
            CompiledEq::ConstMask {
                reg,
                ref target,
                ref mask,
                active_bits,
            } => {
                if k < active_bits {
                    let diff = (regs[reg as usize] & mask[0]) ^ target[0];
                    if (diff >> k) & 1 != 0 {
                        return false;
                    }
                }
            }
            CompiledEq::Pair {
                a,
                b,
                active_bits,
                xor_bit0,
            } => {
                if k < active_bits {
                    let mut diff = regs[a as usize] ^ regs[b as usize];
                    if xor_bit0 {
                        diff ^= 1;
                    }
                    if (diff >> k) & 1 != 0 {
                        return false;
                    }
                }
            }
        }
    }
    true
}

#[expect(clippy::too_many_arguments, reason = "compiled DAG tables passed flat")]
fn lift_wide(
    syms: Vec<SymInfo>,
    sym_slots: &[u16; MAX_SYMS_HARD],
    init_regs: &[Limbs],
    insts: &[DagInst],
    eqs: &[CompiledEq],
    w_stop: u16,
    lift_full_width: bool,
    limits: &HenselLimits,
    steps: &mut u64,
) -> Result<LiftResult, Error> {
    let m = syms.len();
    let mut regs: Vec<Limbs> = init_regs.to_vec();
    let step_cost = insts.len().max(1) as u64;

    let mut states: Vec<[Limbs; MAX_SYMS_HARD]> = vec![[ZERO_LIMBS; MAX_SYMS_HARD]];
    let mut next_states: Vec<[Limbs; MAX_SYMS_HARD]> = Vec::new();

    for k in 0..w_stop {
        next_states.clear();
        let limb_idx = (k >> 6) as usize;
        let limb_bit = 1u64 << (k & 63);

        let mut forced_ones = [false; MAX_SYMS_HARD];
        let mut free_syms = [0usize; MAX_SYMS_HARD];
        let mut num_free = 0usize;
        for (j, s) in syms.iter().enumerate() {
            if k >= s.width.bits() {
                continue;
            }
            match s.fixed_bit(k) {
                Some(true) => forced_ones[j] = true,
                Some(false) => {}
                None => {
                    free_syms[num_free] = j;
                    num_free += 1;
                }
            }
        }

        let combos = 1usize << num_free;
        for base in &states {
            for choice in 0..combos {
                *steps = steps.saturating_add(step_cost);
                if *steps > limits.max_steps {
                    return Ok(LiftResult::Unknown);
                }

                let mut cand = *base;
                for j in 0..m {
                    if forced_ones[j] {
                        cand[j][limb_idx] |= limb_bit;
                    }
                }
                for (b_idx, &sym_j) in free_syms[..num_free].iter().enumerate() {
                    if (choice >> b_idx) & 1 != 0 {
                        cand[sym_j][limb_idx] |= limb_bit;
                    }
                }
                for j in 0..m {
                    let slot = sym_slots[j];
                    if slot != u16::MAX {
                        regs[slot as usize] = cand[j];
                    }
                }

                eval_dag_wide(&mut regs, insts);
                if check_eqs_wide(&regs, eqs, k) {
                    if next_states.len() >= limits.max_states_per_level {
                        return Ok(LiftResult::Unknown);
                    }
                    next_states.push(cand);
                }
            }
        }

        if next_states.is_empty() {
            return Ok(LiftResult::Unsat);
        }
        core::mem::swap(&mut states, &mut next_states);
    }

    if !lift_full_width {
        for st in &mut states {
            for (j, s) in syms.iter().enumerate() {
                let wb = s.width.bits();
                if w_stop < wb {
                    let def = s.default_limbs();
                    for bit in w_stop..wb {
                        if wide::bit(&def, bit as usize) {
                            st[j][(bit >> 6) as usize] |= 1u64 << (bit & 63);
                        }
                    }
                }
            }
        }
    }

    Ok(LiftResult::Roots { syms, states })
}

fn eval_dag_wide(regs: &mut [Limbs], insts: &[DagInst]) {
    for inst in insts {
        let w = inst.width;
        let v = match inst.op {
            DagOp::Not(a) => wide::not(w, &regs[a as usize]),
            DagOp::Neg(a) => wide::neg(w, &regs[a as usize]),
            DagOp::Add(a, b) => wide::add(w, &regs[a as usize], &regs[b as usize]),
            DagOp::Sub(a, b) => wide::sub(w, &regs[a as usize], &regs[b as usize]),
            DagOp::Mul(a, b) => wide::mul(w, &regs[a as usize], &regs[b as usize]),
            DagOp::And(a, b) => {
                let (ra, rb) = (&regs[a as usize], &regs[b as usize]);
                core::array::from_fn(|i| ra[i] & rb[i])
            }
            DagOp::Or(a, b) => {
                let (ra, rb) = (&regs[a as usize], &regs[b as usize]);
                core::array::from_fn(|i| ra[i] | rb[i])
            }
            DagOp::Xor(a, b) => {
                let (ra, rb) = (&regs[a as usize], &regs[b as usize]);
                core::array::from_fn(|i| ra[i] ^ rb[i])
            }
            DagOp::ShlConst(a, s) => wide::shl(w, &regs[a as usize], &small_limbs(u64::from(s))),
            DagOp::Zext(a) => regs[a as usize],
            DagOp::Sext { src, from_bits } => {
                if w == from_bits {
                    regs[src as usize]
                } else {
                    wide::sext(&regs[src as usize], from_bits, w)
                }
            }
            DagOp::Trunc(a) => {
                let mut r = regs[a as usize];
                wide::mask_top(&mut r, w);
                r
            }
            DagOp::Concat { hi, lo, lo_bits } => {
                let mut r = wide::concat(&regs[hi as usize], &regs[lo as usize], lo_bits);
                wide::mask_top(&mut r, w);
                r
            }
            DagOp::Select {
                cond,
                then_v,
                else_v,
            } => {
                if regs[cond as usize][0] != 0 {
                    regs[then_v as usize]
                } else {
                    regs[else_v as usize]
                }
            }
            DagOp::Eq(a, b) => small_limbs(u64::from(regs[a as usize] == regs[b as usize])),
            DagOp::Ne(a, b) => small_limbs(u64::from(regs[a as usize] != regs[b as usize])),
        };
        regs[inst.dst as usize] = v;
    }
}

#[inline]
fn check_eqs_wide(regs: &[Limbs], eqs: &[CompiledEq], k: u16) -> bool {
    let li = (k >> 6) as usize;
    let sh = k & 63;
    for eq in eqs {
        match *eq {
            CompiledEq::ConstMask {
                reg,
                ref target,
                ref mask,
                active_bits,
            } => {
                if k < active_bits {
                    let diff = (regs[reg as usize][li] & mask[li]) ^ target[li];
                    if (diff >> sh) & 1 != 0 {
                        return false;
                    }
                }
            }
            CompiledEq::Pair {
                a,
                b,
                active_bits,
                xor_bit0,
            } => {
                if k < active_bits {
                    let mut diff = regs[a as usize][li] ^ regs[b as usize][li];
                    if xor_bit0 && li == 0 {
                        diff ^= 1;
                    }
                    if (diff >> sh) & 1 != 0 {
                        return false;
                    }
                }
            }
        }
    }
    true
}

// ----- cone traversal, symbol expansion & model verification -------------------------------------

/// Ascending (topological) node indices reachable from `roots`, or `None` if more than `cap`.
fn collect_cone_bounded(cx: &Context, roots: &[u32], cap: usize) -> Option<Vec<u32>> {
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut out = Vec::new();
    let mut stack = roots.to_vec();
    while let Some(id) = stack.pop() {
        if seen.insert(id, ()).is_some() {
            continue;
        }
        out.push(id);
        if out.len() > cap {
            return None;
        }
        stack.extend(cx.node(id).children());
    }
    out.sort_unstable();
    Some(out)
}

/// Ascending causal cone where symbol-free subtrees are treated as constant leaves.
fn collect_causal_cone_pruned(
    cx: &Context,
    roots: &[u32],
    info: &IdMap<u32, NodeCausal>,
) -> Vec<u32> {
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut out = Vec::new();
    let mut stack = roots.to_vec();
    while let Some(id) = stack.pop() {
        if seen.insert(id, ()).is_some() {
            continue;
        }
        out.push(id);
        if info[&id].has_syms {
            stack.extend(cx.node(id).children());
        }
    }
    out.sort_unstable();
    out
}

fn collect_symbols_sorted(cx: &Context, cone: &[u32]) -> Vec<SymInfo> {
    let mut syms = Vec::new();
    for &id in cone {
        let n = cx.node(id);
        if n.op == OpCode::Sym {
            let entry = &cx.symbols.entries[n.a as usize];
            syms.push(SymInfo {
                sym_idx: n.a,
                key: entry.key.clone(),
                width: entry.width,
                known: entry.known,
            });
        }
    }
    syms.sort_by(|a, b| a.key.cmp(&b.key));
    syms
}

fn expand_extra_symbols(
    base_syms: &[SymInfo],
    base_states: &[[Limbs; MAX_SYMS_HARD]],
    extra_syms: &[SymInfo],
    max_states: usize,
) -> Option<(Vec<SymInfo>, Vec<[Limbs; MAX_SYMS_HARD]>)> {
    if base_syms.len() + extra_syms.len() > MAX_SYMS_HARD {
        return None;
    }
    let mut merged_syms = base_syms.to_vec();
    let mut cur_states = base_states.to_vec();

    for extra in extra_syms {
        let pos = merged_syms.len();
        let kb = extra
            .known
            .unwrap_or_else(|| KnownBits::unknown(extra.width));
        let vals = kb.enumerate_where(10, max_states, |_| true)?;
        if vals.is_empty() {
            return Some((merged_syms, Vec::new()));
        }
        let total = cur_states.len().checked_mul(vals.len())?;
        if total > max_states {
            return None;
        }
        let mut next = Vec::with_capacity(total);
        for st in &cur_states {
            for v in &vals {
                let mut ns = *st;
                ns[pos] = *v.raw();
                next.push(ns);
            }
        }
        merged_syms.push(extra.clone());
        cur_states = next;
    }

    Some((merged_syms, cur_states))
}

fn build_model(
    _cx: &Context,
    all_syms: &[SymInfo],
    state_syms: &[SymInfo],
    state: &[Limbs; MAX_SYMS_HARD],
) -> Vec<(SymbolKey, BitVec)> {
    let mut model = Vec::with_capacity(all_syms.len());
    for s in all_syms {
        let limbs = match state_syms.iter().position(|cs| cs.sym_idx == s.sym_idx) {
            Some(pos) => state[pos],
            None => s.default_limbs(),
        };
        let bv = BitVec::wrapping_from_limbs(s.width, &limbs);
        let fitted = s.known.map_or(bv, |kb| kb.fit(&bv));
        model.push((s.key.clone(), fitted));
    }
    model
}

fn model_satisfies_declared(all_syms: &[SymInfo], model: &[(SymbolKey, BitVec)]) -> bool {
    all_syms.iter().zip(model).all(|(s, (_, v))| {
        debug_assert_eq!(s.key, model.iter().find(|(k, _)| *k == s.key).unwrap().0);
        s.known.is_none_or(|kb| kb.contains(v))
    })
}

fn default_model_for_roots(cx: &Context, roots: &[u32]) -> Result<Vec<(SymbolKey, BitVec)>, Error> {
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut cone = Vec::new();
    let mut stack = roots.to_vec();
    while let Some(id) = stack.pop() {
        if seen.insert(id, ()).is_some() {
            continue;
        }
        cone.push(id);
        stack.extend(cx.node(id).children());
    }
    let syms = collect_symbols_sorted(cx, &cone);
    Ok(syms
        .into_iter()
        .map(|s| {
            let v = BitVec::wrapping_from_limbs(s.width, &s.default_limbs());
            (s.key, v)
        })
        .collect())
}

struct EvalCone<'a> {
    cone: &'a [u32],
    slots: IdMap<u32, usize>,
}

impl<'a> EvalCone<'a> {
    fn new(cone: &'a [u32]) -> Self {
        let mut slots = IdMap::default();
        slots.reserve(cone.len());
        for (idx, &id) in cone.iter().enumerate() {
            slots.insert(id, idx);
        }
        Self { cone, slots }
    }

    #[inline]
    fn slot(&self, id: u32) -> usize {
        self.slots[&id]
    }

    fn run(
        &self,
        cx: &Context,
        model: &[(SymbolKey, BitVec)],
        buf: &mut [BitVec],
    ) -> Result<(), Error> {
        for (idx, &id) in self.cone.iter().enumerate() {
            let v = cx.eval_node(
                id,
                |child| buf[self.slots[&child]],
                |key, _| model.iter().find(|(k, _)| k == key).map(|(_, v)| *v),
            )?;
            buf[idx] = v;
        }
        Ok(())
    }
}

fn verify_predicates(
    cx: &Context,
    pred_ids: &[u32],
    model: &[(SymbolKey, BitVec)],
) -> Result<bool, Error> {
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut cone = Vec::new();
    let mut stack = pred_ids.to_vec();
    while let Some(id) = stack.pop() {
        if seen.insert(id, ()).is_some() {
            continue;
        }
        cone.push(id);
        stack.extend(cx.node(id).children());
    }
    cone.sort_unstable();
    let plan = EvalCone::new(&cone);
    let mut buf = vec![BitVec::zero(Width::W1); cone.len()];
    plan.run(cx, model, &mut buf)?;
    Ok(pred_ids
        .iter()
        .all(|&pid| buf[plan.slot(pid)].bit(0) == Some(true)))
}

fn verify_predicates_counted(
    cx: &Context,
    cone: &[u32],
    pred_ids: &[u32],
    model: &[(SymbolKey, BitVec)],
    max_steps: u64,
    steps: &mut u64,
) -> Result<Option<bool>, Error> {
    *steps = steps.saturating_add(cone.len().max(1) as u64);
    if *steps > max_steps {
        return Ok(None);
    }
    let plan = EvalCone::new(cone);
    let mut buf = vec![BitVec::zero(Width::W1); cone.len()];
    plan.run(cx, model, &mut buf)?;
    Ok(Some(
        pred_ids
            .iter()
            .all(|&pid| buf[plan.slot(pid)].bit(0) == Some(true)),
    ))
}

fn eval_single_in_cone(
    cx: &Context,
    cone: &[u32],
    target_id: u32,
    model: &[(SymbolKey, BitVec)],
) -> Result<BitVec, Error> {
    let plan = EvalCone::new(cone);
    let mut buf = vec![BitVec::zero(Width::W1); cone.len()];
    plan.run(cx, model, &mut buf)?;
    Ok(buf[plan.slot(target_id)])
}

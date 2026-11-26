//! Lowering from the arena into an [`MbaExpr`], and lifting back.

use super::expr::{MNode, MOp, MbaExpr};
use crate::engine::pass::Lease;
use crate::error::Error;
use crate::expr::{Context, Expr, OpCode};
use crate::hash::IdMap;
use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

/// Caps on what is lowered and asked of a solver.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct MbaLimits {
    /// The most variables.
    pub max_vars: u32,
    /// The most nodes.
    pub max_nodes: u32,
    /// The widest node.
    pub max_width: u16,
    /// Fewer nodes than this are not worth a solver call.
    pub min_nodes: u32,
}

impl Default for MbaLimits {
    fn default() -> Self {
        MbaLimits {
            max_vars: 8,
            max_nodes: 2048,
            max_width: 512,
            min_nodes: 4,
        }
    }
}

setters!(MbaLimits {
    with_max_vars: max_vars: u32,
    with_max_nodes: max_nodes: u32,
    with_max_width: max_width: u16,
    with_min_nodes: min_nodes: u32,
});

/// Why an expression was not lowered or not solved.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Refusal {
    /// More variables than the limit.
    TooManyVars,
    /// More nodes than the limit.
    TooLarge,
    /// A node wider than the limit.
    TooWide,
    /// Fewer nodes than worth asking about.
    TooSmall,
    /// Not a mix of arithmetic and bitwise operators.
    NotMixed,
    /// The solver does not handle this input (its reason).
    Unsupported(String),
}

/// The expressions the variables of a lowered [`MbaExpr`] stand for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bindings {
    pub(crate) atoms: Vec<u32>,
}

impl Bindings {
    /// The number of variables.
    pub fn len(&self) -> usize {
        self.atoms.len()
    }

    /// Whether there are none.
    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty()
    }
}

/// Whether node `i` belongs to the fragment (otherwise it is an atom).
fn in_fragment(cx: &Context, i: u32) -> bool {
    let n = cx.node(i);
    match n.op {
        OpCode::Const
        | OpCode::Add
        | OpCode::Sub
        | OpCode::Mul
        | OpCode::Neg
        | OpCode::And
        | OpCode::Or
        | OpCode::Xor
        | OpCode::Not
        | OpCode::Zext
        | OpCode::Sext
        | OpCode::Concat => true,
        // any slice, as a right shift then a truncation (`extract<8, 8>(x)` is
        // `trunc<8>(x >> 8)`), so a byte of a value stays related to the value.
        OpCode::Extract => n.b + u32::from(n.width) <= u32::from(cx.width_of(n.a).bits()),
        OpCode::Shl | OpCode::LShr => cx
            .const_val(n.b)
            .and_then(|k| k.to_u64())
            .is_some_and(|k| k < u64::from(n.width)),
        _ => false,
    }
}

/// Whether a narrower reading's atoms `bindings` include a node the whole fragment reads
/// through (arithmetic under a bitwise operator, a value cut off): otherwise the reading is
/// the whole fragment's.
pub(crate) fn cuts(cx: &Context, bindings: &Bindings) -> bool {
    bindings.atoms.iter().any(|&a| in_fragment(cx, a))
}

/// Whether the fragment rooted at `root` is one [`lower_id`] takes (rooted at a fragment
/// operator, within `lim`): its interior nodes, operands first, when it is.
pub(crate) fn fits_nodes(cx: &Context, root: u32, lim: &MbaLimits) -> Result<Vec<u32>, Refusal> {
    let (_, order) = scan(cx, root, lim)?;
    Ok(order)
}

/// the narrower fragments [`lower_id_reading`] lowers.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Reading {
    /// `+ − neg`, products and left shifts by a constant, and `& | ^ ~` with any constants, at
    /// one width: a semi-linear MBA.
    SemiLinear,
    /// The same, with the operands of `& | ^ ~` bitwise functions of atoms: arithmetic under a
    /// bitwise operator is an atom, as obfuscators build a semi-linear MBA (`Σ cᵢ·fᵢ(x)` over
    /// whatever values they take for `x`).
    Shallow,
    /// The same with `& | ^ ~` only over 0 and all-ones: a linear MBA, decided at the corners.
    Linear,
    /// Semi-linear, with this node (shared by several terms) an atom: `Σ cᵢ·fᵢ(a)` over a
    /// value every term reads.
    Cut(u32),
    /// The whole fragment, casts included, with this node an atom: a block over a rotated value
    /// and over bytes and halves of it (`trunc<32>(t)`, `zext<64>(trunc<8>(n))`), which stay
    /// related to `t` and `n`.
    CutWhole(u32),
}

/// whether node `i` is interior to `reading`'s fragment.
fn in_reading(cx: &Context, i: u32, reading: Reading) -> bool {
    let n = cx.node(i);
    let uniform = |k: u32| cx.const_val(k).is_none_or(|v| v.is_zero() || v.is_ones());
    match n.op {
        OpCode::Const | OpCode::Add | OpCode::Sub | OpCode::Neg => true,
        OpCode::Mul => cx.const_val(n.a).is_some() || cx.const_val(n.b).is_some(),
        OpCode::Shl => reading == Reading::SemiLinear && in_fragment(cx, i),
        OpCode::And | OpCode::Or | OpCode::Xor | OpCode::Not => {
            reading == Reading::SemiLinear || n.children().all(uniform)
        }
        _ => false,
    }
}

/// The fragment rooted at `root`: its atoms (in order of discovery) and its other nodes,
/// operands first.
fn scan(cx: &Context, root: u32, lim: &MbaLimits) -> Result<(Vec<u32>, Vec<u32>), Refusal> {
    scan_in(cx, root, lim, &in_fragment)
}

/// [`scan`] over the fragment `in_fragment` defines.
fn scan_in(
    cx: &Context,
    root: u32,
    lim: &MbaLimits,
    in_fragment: &dyn Fn(&Context, u32) -> bool,
) -> Result<(Vec<u32>, Vec<u32>), Refusal> {
    Dense::with(&SEEN, cx.len(), |seen| {
        // (Sized for the fragments most questions have: grown a push at a time, the three
        // were a quarter of what a scan cost.)
        let mut atoms: Vec<u32> = Vec::with_capacity(16);
        let mut order: Vec<u32> = Vec::with_capacity(64);
        let mut met = 0u32;
        let record = |m: u32| SCAN_VISITS.with(|c| c.set(c.get().saturating_add(u64::from(m))));
        let mut stack: Vec<(u32, bool)> = Vec::with_capacity(64);
        stack.push((root, false));
        while let Some((i, expanded)) = stack.pop() {
            if expanded {
                order.push(i);
                continue;
            }
            if seen.insert(i, 0) {
                continue;
            }
            met += 1;
            if cx.node(i).width > lim.max_width {
                record(met);
                return Err(Refusal::TooWide);
            }
            if met > lim.max_nodes {
                record(met);
                return Err(Refusal::TooLarge);
            }
            if !in_fragment(cx, i) {
                if i == root {
                    record(met);
                    return Err(Refusal::Unsupported("not an MBA operator".into()));
                }
                atoms.push(i);
                if atoms.len() as u32 > lim.max_vars {
                    record(met);
                    return Err(Refusal::TooManyVars);
                }
                continue;
            }
            stack.push((i, true));
            for c in cx.node(i).children() {
                stack.push((c, false));
            }
        }
        record(met);
        Ok((atoms, order))
    })
}

/// A map from arena indices to `u32` that is emptied in constant time: a slot holds its value
/// while its stamp is the current generation. The lowering walks one fragment per reading of
/// every candidate, and a hash map built and dropped for each was most of what a walk cost.
#[derive(Default)]
struct Dense {
    stamp: Vec<u32>,
    value: Vec<u32>,
    generation: u32,
}

thread_local! {
    static SEEN: std::cell::RefCell<Dense> = std::cell::RefCell::new(Dense::default());
    static AT: std::cell::RefCell<Dense> = std::cell::RefCell::new(Dense::default());
    static SCAN_VISITS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Returns and resets the number of DAG nodes visited by `scan_in` / `under_bitwise` /
/// `shared_in` on this thread since the previous call.
pub(crate) fn take_scan_visits() -> u64 {
    SCAN_VISITS.with(|c| c.replace(0))
}

impl Dense {
    /// Runs `f` with the thread's map `key`, empty and sized for `len` indices.
    fn with<R>(
        key: &'static std::thread::LocalKey<std::cell::RefCell<Dense>>,
        len: usize,
        f: impl FnOnce(&mut Dense) -> R,
    ) -> R {
        let mut d = key.with(|c| std::mem::take(&mut *c.borrow_mut()));
        if d.generation == u32::MAX {
            d.stamp.clear();
            d.generation = 0;
        }
        d.generation += 1;
        if d.stamp.len() < len {
            d.stamp.resize(len, 0);
            d.value.resize(len, 0);
        }
        let out = f(&mut d);
        key.with(|c| *c.borrow_mut() = d);
        out
    }

    /// Sets `i` to `v`; whether it had a value.
    fn insert(&mut self, i: u32, v: u32) -> bool {
        let had = self.stamp[i as usize] == self.generation;
        self.stamp[i as usize] = self.generation;
        self.value[i as usize] = v;
        had
    }

    fn get(&self, i: u32) -> Option<u32> {
        (self.stamp[i as usize] == self.generation).then(|| self.value[i as usize])
    }
}

/// Lowers the fragment rooted at `root` (arena index); non-fragment subterms become variables.
pub(crate) fn lower_id(
    cx: &Context,
    root: u32,
    lim: &MbaLimits,
) -> Result<(MbaExpr, Bindings), Refusal> {
    let mut scan_lim = *lim;
    scan_lim.max_vars = lim.max_vars.saturating_add(4);
    let (mut atoms, order) = scan(cx, root, &scan_lim)?;
    let peers = deduplicate_peers(cx, &mut atoms);
    if atoms.len() as u32 > lim.max_vars {
        return Err(Refusal::TooManyVars);
    }
    build_with_peers(cx, atoms, order, &[], &peers)
}

/// [`lower_id`] over `reading`'s narrower fragment: every other subterm (a cast,
/// a right shift, a product of two non-constants, for [`Reading::Linear`] a bitwise operation
/// with another constant) is a variable. An identity of the result holds for independent
/// values of those, so for theirs.
pub(crate) fn lower_id_reading(
    cx: &Context,
    root: u32,
    lim: &MbaLimits,
    reading: Reading,
) -> Result<(MbaExpr, Bindings), Refusal> {
    lower_id_over(cx, root, lim, Some(reading), &IdMap::default())
}

/// [`lower_id`] (no reading) or [`lower_id_reading`] with every node of `opaque` below `root`
/// an atom whatever its operator: the fragment ends there. An identity of the result holds for
/// any values of those nodes, so for theirs.
pub(crate) fn lower_id_over(
    cx: &Context,
    root: u32,
    lim: &MbaLimits,
    reading: Option<Reading>,
    opaque: &IdMap<u32, ()>,
) -> Result<(MbaExpr, Bindings), Refusal> {
    let free = |i: u32| i == root || !opaque.contains_key(&i);
    let mut scan_lim = *lim;
    scan_lim.max_vars = lim.max_vars.saturating_add(4);
    let Some(reading) = reading else {
        let (mut atoms, order) =
            scan_in(cx, root, &scan_lim, &|cx, i| free(i) && in_fragment(cx, i))?;
        let peers = deduplicate_peers(cx, &mut atoms);
        if atoms.len() as u32 > lim.max_vars {
            return Err(Refusal::TooManyVars);
        }
        return build_with_peers(cx, atoms, order, &[], &peers);
    };
    let inside = |cx: &Context, i: u32, under: Option<&Lease>| {
        free(i)
            && match reading {
                Reading::Shallow => {
                    in_reading(cx, i, Reading::SemiLinear)
                        && (bitwise_or_const(cx, i) || under.is_none_or(|u| !is_under(u, i)))
                }
                Reading::Cut(cut) => i != cut && in_reading(cx, i, Reading::SemiLinear),
                Reading::CutWhole(cut) => i != cut && in_fragment(cx, i),
                _ => in_reading(cx, i, reading),
            }
    };
    let under = match reading {
        Reading::Shallow => Some(under_bitwise(cx, root, lim, opaque)?),
        _ => None,
    };
    let (mut atoms, order) = scan_in(cx, root, &scan_lim, &|cx, i| inside(cx, i, under.as_ref()))?;
    // An atom that is its operand and a constant added (`a = t + k`, `a = k − t`) or xored
    // (`a = t ^ k`), where the fragment reads `t` too: `t` is `a − k`, `k − a`, or `a ^ k` over
    // the atom, and nothing below `t` is read.
    let candidates: Vec<u32> = match reading {
        Reading::Shallow => atoms.clone(),
        Reading::Cut(cut) | Reading::CutWhole(cut) if atoms.contains(&cut) => vec![cut],
        _ => Vec::new(),
    };
    let mut solved: Vec<Solved> = Vec::new();
    for &a in &candidates {
        let Some((t, kind)) = offset_or_xor(cx, a) else {
            continue;
        };
        if t != root
            && (order.contains(&t) || atoms.contains(&t))
            && solved
                .iter()
                .all(|s| s.operand != t && s.atom != t && s.operand != a)
        {
            solved.push(Solved {
                operand: t,
                atom: a,
                kind,
            });
        }
    }
    let order = if !solved.is_empty() {
        let (a2, o2) = scan_in(cx, root, &scan_lim, &|cx, i| {
            solved.iter().all(|s| s.operand != i) && inside(cx, i, under.as_ref())
        })?;
        atoms = a2;
        solved.retain(|s| atoms.contains(&s.operand) && atoms.contains(&s.atom));
        atoms.retain(|a| solved.iter().all(|s| s.operand != *a));
        o2
    } else {
        order
    };
    let peers = deduplicate_peers(cx, &mut atoms);
    if atoms.len() as u32 > lim.max_vars {
        return Err(Refusal::TooManyVars);
    }
    build_with_peers(cx, atoms, order, &solved, &peers)
}

/// [`lower_id_over`] with no reading, and whether the fragment is semi-linear as it is (every
/// node of it one [`Reading::SemiLinear`] takes): the semi-linear reading is then this one, and
/// each cut of the whole fragment is the semi-linear cut at the same node, so a caller that
/// has this need not lower those.
pub(crate) fn lower_id_whole(
    cx: &Context,
    root: u32,
    lim: &MbaLimits,
    opaque: &IdMap<u32, ()>,
) -> Result<(MbaExpr, Bindings, bool), Refusal> {
    let free = |i: u32| i == root || !opaque.contains_key(&i);
    let mut scan_lim = *lim;
    scan_lim.max_vars = lim.max_vars.saturating_add(4);
    let (mut atoms, order) =
        scan_in(cx, root, &scan_lim, &|cx, i| free(i) && in_fragment(cx, i))?;
    let semi = order
        .iter()
        .all(|&i| in_reading(cx, i, Reading::SemiLinear));
    let peers = deduplicate_peers(cx, &mut atoms);
    if atoms.len() as u32 > lim.max_vars {
        return Err(Refusal::TooManyVars);
    }
    let (m, bindings) = build_with_peers(cx, atoms, order, &[], &peers)?;
    Ok((m, bindings, semi))
}

fn is_negated_pair(cx: &Context, a: u32, b: u32) -> bool {
    let na = cx.node(a);
    let nb = cx.node(b);
    if (na.op == OpCode::Neg && na.a == b) || (nb.op == OpCode::Neg && nb.a == a) {
        return true;
    }
    if let (
        Some((
            ta,
            SolvedKind::Sub {
                constant: ca,
                negated: nega,
            },
        )),
        Some((
            tb,
            SolvedKind::Sub {
                constant: cb,
                negated: negb,
            },
        )),
    ) = (offset_or_xor(cx, a), offset_or_xor(cx, b))
    {
        return ta == tb && nega != negb && BitVec::bin_unchecked(BinOp::Add, &ca, &cb).is_zero();
    }
    false
}

/// Deduplicate peer correlated atoms (`t` vs `t ^ c` / `t + c` / `c - t`, `t ^ c1` vs `t ^ c2`,
/// `t + c1` vs `t + c2` / `c2 - t`, nested bit-masks `x & m_sub` under `x & m_sup` or `x`, and
/// opposite-sign products `(K - X) * M` vs `(X - K) * M`), returning `PeerSolved` entries in
/// valid topological order so chained peers never reference an unbuilt source.
fn deduplicate_peers(cx: &Context, atoms: &mut Vec<u32>) -> Vec<PeerSolved> {
    if atoms.len() < 2 {
        return Vec::new();
    }
    let mut peers: Vec<PeerSolved> = Vec::new();
    let mut keep = vec![true; atoms.len()];
    for j in 0..atoms.len() {
        if !keep[j] {
            continue;
        }
        let aj = atoms[j];
        let wj = cx.wid(aj);
        // 1) Check if `aj` is `x & m_sub` covered by another kept atom `ai` (`x` or `x & m_sup`).
        if let Some((xj, m_sub)) = const_and_of(cx, aj) {
            let sup = (0..atoms.len()).find(|&i| {
                i != j
                    && keep[i]
                    && cx.wid(atoms[i]) == wj
                    && if atoms[i] == xj {
                        true
                    } else if let Some((xi, m_sup)) = const_and_of(cx, atoms[i]) {
                        xi == xj
                            && BitVec::bin_unchecked(
                                BinOp::And,
                                &m_sub,
                                &BitVec::un_unchecked(UnOp::Not, &m_sup),
                            )
                            .is_zero()
                            && (m_sub != m_sup || i < j)
                    } else {
                        false
                    }
            });
            if let Some(i) = sup {
                keep[j] = false;
                peers.push(PeerSolved {
                    target: aj,
                    source: atoms[i],
                    op: PeerOp::And(m_sub),
                });
                continue;
            }
        }
        // 2) Check if `aj` is `t ^ c` / `t + c` / `c - t` over another kept bare atom `t` (any
        // index `i != j`), or shares an affine/xor base with an earlier kept atom `ai` (`i < j`).
        if let Some((tj, kj)) = offset_or_xor(cx, aj) {
            if let Some(i) = (0..atoms.len()).find(|&i| i != j && keep[i] && atoms[i] == tj) {
                let op = match kj {
                    SolvedKind::Xor(c) => PeerOp::Xor(c),
                    SolvedKind::Sub {
                        constant: c,
                        negated: false,
                    } => PeerOp::Add(c),
                    SolvedKind::Sub {
                        constant: c,
                        negated: true,
                    } => PeerOp::SubFrom(c),
                };
                keep[j] = false;
                peers.push(PeerSolved {
                    target: aj,
                    source: atoms[i],
                    op,
                });
                continue;
            }
            let earlier = (0..j).find_map(|i| {
                if !keep[i] || cx.wid(atoms[i]) != wj {
                    return None;
                }
                let (ti, ki) = offset_or_xor(cx, atoms[i])?;
                if ti != tj {
                    return None;
                }
                match (ki, kj) {
                    (SolvedKind::Xor(c1), SolvedKind::Xor(c2)) => Some((
                        atoms[i],
                        PeerOp::Xor(BitVec::bin_unchecked(BinOp::Xor, &c1, &c2)),
                    )),
                    (
                        SolvedKind::Sub {
                            constant: c1,
                            negated: false,
                        },
                        SolvedKind::Sub {
                            constant: c2,
                            negated: false,
                        },
                    )
                    | (
                        SolvedKind::Sub {
                            constant: c1,
                            negated: true,
                        },
                        SolvedKind::Sub {
                            constant: c2,
                            negated: true,
                        },
                    ) => Some((
                        atoms[i],
                        PeerOp::Add(BitVec::bin_unchecked(BinOp::Sub, &c2, &c1)),
                    )),
                    (
                        SolvedKind::Sub {
                            constant: c1,
                            negated: false,
                        },
                        SolvedKind::Sub {
                            constant: c2,
                            negated: true,
                        },
                    )
                    | (
                        SolvedKind::Sub {
                            constant: c1,
                            negated: true,
                        },
                        SolvedKind::Sub {
                            constant: c2,
                            negated: false,
                        },
                    ) => Some((
                        atoms[i],
                        PeerOp::SubFrom(BitVec::bin_unchecked(BinOp::Add, &c1, &c2)),
                    )),
                    _ => None,
                }
            });
            if let Some((src, op)) = earlier {
                keep[j] = false;
                peers.push(PeerSolved {
                    target: aj,
                    source: src,
                    op,
                });
                continue;
            }
        }
        // 3) Unify narrow zero-extended XOR/complement peers (`zext<w>(t:iw ^ c2)` vs
        // `zext<w>(t:iw)` or `zext<w>(t:iw ^ c1)` or `zext<w>(~t:iw)`): exact at all bits via
        // `zext<w>(t ^ c2) == zext<w>(t ^ c1) ^ zext<w>(c1 ^ c2)`.
        if let Some(((tj, iwj), cj)) = zext_xor_of(cx, aj) {
            if !cj.is_zero()
                && let Some(i) = (0..atoms.len()).find(|&i| {
                    i != j
                        && keep[i]
                        && cx.wid(atoms[i]) == wj
                        && zext_xor_of(cx, atoms[i])
                            .is_some_and(|(key_i, ci)| key_i == (tj, iwj) && ci.is_zero())
                })
            {
                keep[j] = false;
                peers.push(PeerSolved {
                    target: aj,
                    source: atoms[i],
                    op: PeerOp::Xor(cj),
                });
                continue;
            }
            let earlier_zext = (0..j).find_map(|i| {
                if !keep[i] || cx.wid(atoms[i]) != wj {
                    return None;
                }
                let (key_i, ci) = zext_xor_of(cx, atoms[i])?;
                (key_i == (tj, iwj)).then(|| {
                    (
                        atoms[i],
                        PeerOp::Xor(BitVec::bin_unchecked(BinOp::Xor, &ci, &cj)),
                    )
                })
            });
            if let Some((src, op)) = earlier_zext {
                keep[j] = false;
                peers.push(PeerSolved {
                    target: aj,
                    source: src,
                    op,
                });
                continue;
            }
        }
        // 4) Check if `aj` is negated relative to an earlier kept product atom `(K - X) * M` vs
        // `(X - K) * M` (`aj == 0 - ai`).
        let nj = cx.node(aj);
        if nj.op == OpCode::Mul {
            let neg_src = (0..j).find(|&i| {
                if !keep[i] || cx.wid(atoms[i]) != wj {
                    return false;
                }
                let ni = cx.node(atoms[i]);
                ni.op == OpCode::Mul
                    && ((nj.a == ni.a && is_negated_pair(cx, nj.b, ni.b))
                        || (nj.b == ni.b && is_negated_pair(cx, nj.a, ni.a))
                        || (nj.a == ni.b && is_negated_pair(cx, nj.b, ni.a))
                        || (nj.b == ni.a && is_negated_pair(cx, nj.a, ni.b)))
            });
            if let Some(i) = neg_src {
                keep[j] = false;
                peers.push(PeerSolved {
                    target: aj,
                    source: atoms[i],
                    op: PeerOp::SubFrom(BitVec::zero(cx.width_of(aj))),
                });
            }
        }
    }
    if peers.is_empty() {
        return peers;
    }
    let mut idx = 0usize;
    atoms.retain(|_| {
        let k = keep[idx];
        idx += 1;
        k
    });
    let mut ready: IdMap<u32, ()> = atoms.iter().map(|&a| (a, ())).collect();
    let mut ordered = Vec::with_capacity(peers.len());
    let mut rem = peers;
    while !rem.is_empty() {
        let prev = rem.len();
        let mut next = Vec::new();
        for p in rem {
            if ready.contains_key(&p.source) {
                ready.insert(p.target, ());
                ordered.push(p);
            } else {
                next.push(p);
            }
        }
        if next.len() == prev {
            for p in next {
                atoms.push(p.target);
            }
            break;
        }
        rem = next;
    }
    ordered
}

fn zext_xor_of(cx: &Context, a: u32) -> Option<((u32, u16), BitVec)> {
    let n = cx.node(a);
    if n.op != OpCode::Zext {
        return None;
    }
    let w = cx.width_of(a);
    let inner = n.a;
    let iw = cx.wid(inner);
    if iw >= w.bits() {
        return None;
    }
    let in_node = cx.node(inner);
    match in_node.op {
        OpCode::Xor => match (cx.const_val(in_node.a), cx.const_val(in_node.b)) {
            (None, Some(k)) => Some(((in_node.a, iw), k.zext(w).ok()?)),
            (Some(k), None) => Some(((in_node.b, iw), k.zext(w).ok()?)),
            _ => Some(((inner, iw), BitVec::zero(w))),
        },
        OpCode::Not => Some((
            (in_node.a, iw),
            crate::facts::known::low_mask(w, u32::from(iw)),
        )),
        _ => Some(((inner, iw), BitVec::zero(w))),
    }
}

fn const_and_of(cx: &Context, a: u32) -> Option<(u32, BitVec)> {
    let n = cx.node(a);
    if n.op != OpCode::And {
        return None;
    }
    match (cx.const_val(n.a), cx.const_val(n.b)) {
        (None, Some(m)) => Some((n.a, m)),
        (Some(m), None) => Some((n.b, m)),
        _ => None,
    }
}

/// Node `a` as `t + k`, `k − t`, or `t ^ k` with `k` a constant.
fn offset_or_xor(cx: &Context, a: u32) -> Option<(u32, SolvedKind)> {
    let n = cx.node(a);
    if n.op == OpCode::Xor {
        return match (cx.const_val(n.a), cx.const_val(n.b)) {
            (None, Some(k)) => Some((n.a, SolvedKind::Xor(k))),
            (Some(k), None) => Some((n.b, SolvedKind::Xor(k))),
            _ => None,
        };
    }
    if !matches!(n.op, OpCode::Add | OpCode::Sub) {
        return None;
    }
    let (t, k) = match (n.op, cx.const_val(n.a), cx.const_val(n.b)) {
        (OpCode::Add, None, Some(k)) => (n.a, k),
        (OpCode::Add, Some(k), None) => (n.b, k),
        (OpCode::Sub, Some(k), None) => {
            return Some((
                n.b,
                SolvedKind::Sub {
                    constant: k,
                    negated: true,
                },
            ))
        }
        (OpCode::Sub, None, Some(k)) => (n.a, BitVec::un_unchecked(UnOp::Neg, &k)),
        _ => return None,
    };
    let m = cx.node(t);
    let (base, negated) = match m.op {
        OpCode::Neg => (m.a, true),
        OpCode::Mul => match (cx.const_val(m.a), cx.const_val(m.b)) {
            (None, Some(c)) if c.is_ones() => (m.a, true),
            (Some(c), None) if c.is_ones() => (m.b, true),
            _ => (t, false),
        },
        _ => (t, false),
    };
    Some((
        base,
        SolvedKind::Sub {
            constant: k,
            negated,
        },
    ))
}

#[derive(Clone, Copy)]
enum SolvedKind {
    Sub { constant: BitVec, negated: bool },
    Xor(BitVec),
}

/// An atom's operand written over the atom.
struct Solved {
    operand: u32,
    atom: u32,
    kind: SolvedKind,
}

#[derive(Clone, Copy)]
enum PeerOp {
    Xor(BitVec),
    Add(BitVec),
    SubFrom(BitVec),
    And(BitVec),
}

struct PeerSolved {
    target: u32,
    source: u32,
    op: PeerOp,
}

/// the non-constant interior nodes of the semi-linear fragment below `root` that
/// two or more of its nodes read, most read first (at most `n`): where a [`Reading::Cut`] may
/// cut. The fragment ends at the nodes of `opaque` below `root` (see [`lower_id_over`]).
pub(crate) fn shared_nodes(
    cx: &Context,
    root: u32,
    lim: &MbaLimits,
    n: usize,
    opaque: &IdMap<u32, ()>,
) -> Vec<u32> {
    shared_in(cx, root, lim, n, opaque, false)
}

/// [`shared_nodes`] of the whole fragment below `root`, casts and slices included: where a
/// [`Reading::CutWhole`] may cut (a value read once as it is and once through a truncation or
/// an extension is shared here and not there).
pub(crate) fn shared_nodes_whole(cx: &Context, root: u32, lim: &MbaLimits, n: usize) -> Vec<u32> {
    shared_in(cx, root, lim, n, &IdMap::default(), true)
}

fn shared_in(
    cx: &Context,
    root: u32,
    lim: &MbaLimits,
    n: usize,
    opaque: &IdMap<u32, ()>,
    whole: bool,
) -> Vec<u32> {
    let inside = |i: u32| {
        (i == root || !opaque.contains_key(&i))
            && match whole {
                true => in_fragment(cx, i),
                false => in_reading(cx, i, Reading::SemiLinear),
            }
    };
    // (Leased tables: this is asked of every candidate, and hash maps grown from empty for
    // each were a quarter of a large expression's run. The order the users are listed in is
    // of no account: they are sorted, and no two are equal.)
    let mut users = Lease::new(cx.len());
    let mut used: Vec<u32> = Vec::new();
    let mut seen = Lease::new(cx.len());
    let mut met = 0u32;
    let mut stack = vec![root];
    while let Some(i) = stack.pop() {
        if seen.insert(i, 0) {
            continue;
        }
        met += 1;
        if met > lim.max_nodes {
            continue;
        }
        if !inside(i) {
            continue;
        }
        for c in cx.node(i).children() {
            if !users.bump(c) {
                used.push(c);
            }
            stack.push(c);
        }
    }
    SCAN_VISITS.with(|c| c.set(c.get().saturating_add(u64::from(met))));
    let mut v: Vec<(u32, u32)> = used
        .into_iter()
        .map(|i| (i, users.get(i).unwrap_or(0)))
        .filter(|&(i, k)| k >= 2 && cx.const_val(i).is_none() && inside(i))
        .filter(|&(i, _)| cx.node(i).op != OpCode::Not)
        .map(|(i, k)| (k, i))
        .collect();
    v.sort_by(|a, b| b.cmp(a));
    v.into_iter().take(n).map(|(_, i)| i).collect()
}

/// Whether node `i` is a constant or `& | ^ ~`.
fn bitwise_or_const(cx: &Context, i: u32) -> bool {
    matches!(
        cx.node(i).op,
        OpCode::Const | OpCode::And | OpCode::Or | OpCode::Xor | OpCode::Not
    )
}

/// The nodes of the semi-linear fragment below `root` that a bitwise operator of it reads
/// (directly, or through other bitwise operators); the fragment ends at the nodes of `opaque`.
///
/// A node's number in the table says how it was met: 1 as it is, 2 under a bitwise operator
/// ([`is_under`]), 3 both ways.
fn under_bitwise(
    cx: &Context,
    root: u32,
    lim: &MbaLimits,
    opaque: &IdMap<u32, ()>,
) -> Result<Lease, Refusal> {
    let mut seen = Lease::new(cx.len());
    let mut met = 0u32;
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    while let Some((i, bw)) = stack.pop() {
        let (was, way) = (seen.get(i).unwrap_or(0), 1 << u32::from(bw));
        if was & way != 0 {
            continue;
        }
        seen.insert(i, was | way);
        met += 1;
        if met > lim.max_nodes.saturating_mul(2) {
            SCAN_VISITS.with(|c| c.set(c.get().saturating_add(u64::from(met))));
            return Err(Refusal::TooLarge);
        }
        let bitwise = bitwise_or_const(cx, i);
        // Arithmetic read by a bitwise operator is an atom: nothing below it is read here.
        if (bw && !bitwise)
            || (i != root && opaque.contains_key(&i))
            || !in_reading(cx, i, Reading::SemiLinear)
        {
            continue;
        }
        for c in cx.node(i).children() {
            stack.push((c, bitwise));
        }
    }
    SCAN_VISITS.with(|c| c.set(c.get().saturating_add(u64::from(met))));
    Ok(seen)
}

/// Whether [`under_bitwise`] met `i` under a bitwise operator.
fn is_under(under: &Lease, i: u32) -> bool {
    under.get(i).is_some_and(|way| way & 2 != 0)
}

/// The expression over `atoms` that the fragment's nodes `order` (operands first) compute,
/// each operand in `solved` / `peers` written over its atom.
fn build_with_peers(
    cx: &Context,
    atoms: Vec<u32>,
    order: Vec<u32>,
    solved: &[Solved],
    peers: &[PeerSolved],
) -> Result<(MbaExpr, Bindings), Refusal> {
    Dense::with(&AT, cx.len(), |at| {
        build_in(cx, atoms, order, solved, peers, at)
    })
}

fn build_in(
    cx: &Context,
    atoms: Vec<u32>,
    order: Vec<u32>,
    solved: &[Solved],
    peers: &[PeerSolved],
    at: &mut Dense,
) -> Result<(MbaExpr, Bindings), Refusal> {
    // An operand of a fragment's node is one of its atoms or an earlier node of it.
    let unmet = || Refusal::Unsupported("an operand outside the fragment".into());
    // (Room for a node per atom and per node of the fragment, two per operand written over an
    // atom, and the few a slice or a shift adds.)
    let room = atoms.len() + 2 * (solved.len() + peers.len()) + order.len() + 8;
    let mut m = MbaExpr::with_capacity(atoms.iter().map(|&a| cx.width_of(a)).collect(), room);
    for (&a, k) in atoms.iter().zip(0u32..) {
        let v = m
            .push(MOp::Var(k), &[])
            .map_err(|e| Refusal::Unsupported(e.to_string()))?;
        at.insert(a, v);
    }
    let bad = |e: super::expr::MbaError| Refusal::Unsupported(e.to_string());
    for p in peers {
        let src = at.get(p.source).ok_or_else(unmet)?;
        let v = match p.op {
            PeerOp::Xor(c) => {
                let k = m.push(MOp::Const(c), &[]).map_err(bad)?;
                m.push(MOp::Xor, &[src, k]).map_err(bad)?
            }
            PeerOp::Add(c) => {
                let k = m.push(MOp::Const(c), &[]).map_err(bad)?;
                m.push(MOp::Add, &[src, k]).map_err(bad)?
            }
            PeerOp::SubFrom(c) => {
                let k = m.push(MOp::Const(c), &[]).map_err(bad)?;
                m.push(MOp::Sub, &[k, src]).map_err(bad)?
            }
            PeerOp::And(c) => {
                let k = m.push(MOp::Const(c), &[]).map_err(bad)?;
                m.push(MOp::And, &[src, k]).map_err(bad)?
            }
        };
        at.insert(p.target, v);
    }
    for s in solved {
        let a = at.get(s.atom).ok_or_else(unmet)?;
        let v = match s.kind {
            SolvedKind::Sub { constant, negated } => {
                let k = m.push(MOp::Const(constant), &[]).map_err(bad)?;
                let args = if negated { [k, a] } else { [a, k] };
                m.push(MOp::Sub, &args).map_err(bad)?
            }
            SolvedKind::Xor(constant) => {
                let k = m.push(MOp::Const(constant), &[]).map_err(bad)?;
                m.push(MOp::Xor, &[a, k]).map_err(bad)?
            }
        };
        at.insert(s.operand, v);
    }
    for i in order {
        let n = cx.node(i);
        let arg = |k: u32| at.get(k).unwrap_or(u32::MAX);
        let bad = |e: super::expr::MbaError| Refusal::Unsupported(e.to_string());
        let v = match n.op {
            OpCode::Const => m.push(
                MOp::Const(cx.const_val(i).unwrap_or(BitVec::zero(Width::W1))),
                &[],
            ),
            OpCode::Add => m.push(MOp::Add, &[arg(n.a), arg(n.b)]),
            OpCode::Sub => m.push(MOp::Sub, &[arg(n.a), arg(n.b)]),
            OpCode::Mul => m.push(MOp::Mul, &[arg(n.a), arg(n.b)]),
            OpCode::And => m.push(MOp::And, &[arg(n.a), arg(n.b)]),
            OpCode::Or => m.push(MOp::Or, &[arg(n.a), arg(n.b)]),
            OpCode::Xor => m.push(MOp::Xor, &[arg(n.a), arg(n.b)]),
            OpCode::Neg => m.push(MOp::Neg, &[arg(n.a)]),
            OpCode::Not => m.push(MOp::Not, &[arg(n.a)]),
            OpCode::Shl | OpCode::LShr => {
                let k = cx.const_val(n.b).and_then(|k| k.to_u64()).unwrap_or(0) as u16;
                let op = if n.op == OpCode::Shl {
                    MOp::Shl(k)
                } else {
                    MOp::LShr(k)
                };
                m.push(op, &[arg(n.a)])
            }
            OpCode::Zext => m.push_cast(MOp::Zext, arg(n.a), cx.width_of(i)),
            OpCode::Sext => m.push_cast(MOp::Sext, arg(n.a), cx.width_of(i)),
            OpCode::Extract if n.b == 0 => m.push_cast(MOp::Trunc, arg(n.a), cx.width_of(i)),
            OpCode::Extract => (|| {
                let s = m.push(MOp::LShr(n.b as u16), &[arg(n.a)])?;
                if cx.width_of(i) == cx.width_of(n.a) {
                    return Ok(s);
                }
                m.push_cast(MOp::Trunc, s, cx.width_of(i))
            })(),
            // `concat(hi, lo)` is `(hi << |lo|) + lo`, both extended (their bits are disjoint);
            // a high part that is the low bits of a value of the full width is that value, the
            // rest shifting out (`concat(trunc<62>(y), 3)` is `(y << 2) + 3`).
            OpCode::Concat => (|| {
                let w = cx.width_of(i);
                let lw = cx.width_of(n.b);
                let hn = cx.node(n.a);
                let hi = if hn.op == OpCode::Extract && hn.b == 0 && cx.width_of(hn.a) == w {
                    arg(hn.a)
                } else {
                    m.push_cast(MOp::Zext, arg(n.a), w)?
                };
                let hi = m.push(MOp::Shl(lw.bits()), &[hi])?;
                let lo = match cx.const_val(n.b) {
                    Some(c) => m.push(MOp::Const(c.zext(w).unwrap_or(BitVec::zero(w))), &[])?,
                    None => m.push_cast(MOp::Zext, arg(n.b), w)?,
                };
                m.push(MOp::Add, &[hi, lo])
            })(),
            _ => return Err(Refusal::Unsupported("not an MBA operator".into())),
        }
        .map_err(bad)?;
        at.insert(i, v);
    }
    Ok((m, Bindings { atoms }))
}

/// Lowers the fragment rooted at `e` into an [`MbaExpr`]: `+ − * neg & | ^ ~`, shifts by
/// constants below the width, extensions and truncation; every other subterm becomes a variable,
/// bound in the returned [`Bindings`]. Fails with [`Error::Unsupported`] (the refusal) when `e` is
/// not in the fragment or is over a limit.
pub fn lower(cx: &Context, e: Expr, lim: &MbaLimits) -> Result<(MbaExpr, Bindings), Error> {
    let i = cx.id(e)?;
    lower_id(cx, i, lim).map_err(|r| Error::Unsupported(format!("{r:?}")))
}

/// Builds `m` in the arena through the canonicalizing constructors, with each variable bound to
/// its atom.
pub(crate) fn lift_id(cx: &mut Context, m: &MbaExpr, b: &Bindings) -> Result<u32, Error> {
    let mut v: Vec<u32> = Vec::with_capacity(m.nodes().len());
    for n in m.nodes() {
        let a = |k: usize| v[n.args[k] as usize];
        let r = match n.op {
            MOp::Const(c) => cx.mk_const(&c)?,
            MOp::Var(i) => *b
                .atoms
                .get(i as usize)
                .ok_or(Error::Unsupported("unbound MBA variable".into()))?,
            MOp::Add => cx.c_bin(BinOp::Add, a(0), a(1))?,
            MOp::Sub => cx.c_bin(BinOp::Sub, a(0), a(1))?,
            MOp::Mul => cx.c_bin(BinOp::Mul, a(0), a(1))?,
            MOp::And => cx.c_bin(BinOp::And, a(0), a(1))?,
            MOp::Or => cx.c_bin(BinOp::Or, a(0), a(1))?,
            MOp::Xor => cx.c_bin(BinOp::Xor, a(0), a(1))?,
            MOp::Neg => cx.c_un(UnOp::Neg, a(0))?,
            MOp::Not => cx.c_un(UnOp::Not, a(0))?,
            MOp::Shl(k) | MOp::LShr(k) => {
                let kc = cx.mk_const(&BitVec::wrapping_from_u64(n.width, u64::from(k)))?;
                let op = if matches!(n.op, MOp::Shl(_)) {
                    BinOp::Shl
                } else {
                    BinOp::LShr
                };
                cx.c_bin(op, a(0), kc)?
            }
            MOp::Zext => cx.c_zext(a(0), n.width.bits())?,
            MOp::Sext => cx.c_sext(a(0), n.width.bits())?,
            // a truncated right shift is the slice it was lowered from.
            MOp::Trunc => match m.nodes()[n.args[0] as usize] {
                MNode {
                    op: MOp::LShr(k),
                    width,
                    args,
                } if k + n.width.bits() <= width.bits() => {
                    cx.c_extract(v[args[0] as usize], k, n.width.bits())?
                }
                _ => cx.c_extract(a(0), 0, n.width.bits())?,
            },
        };
        v.push(r);
    }
    v.last()
        .copied()
        .ok_or(Error::Unsupported("empty MBA expression".into()))
}

/// Builds `m` in the arena through the canonicalizing constructors, each variable bound to the
/// subterm it stands for.
pub fn lift(cx: &mut Context, m: &MbaExpr, b: &Bindings) -> Result<Expr, Error> {
    let i = lift_id(cx, m, b)?;
    Ok(cx.handle(i))
}

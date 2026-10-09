//! Concrete evaluation and substitution.

use std::collections::{BTreeMap, HashMap};
use std::hash::BuildHasher;

use super::{Context, Expr, Node, OpCode};
use crate::error::Error;
use crate::hash::IdMap;
use crate::value::narrow;
use crate::{BitVec, SymbolKey, Width};

/// Only the most recent root set is cached. Nodes are immutable until `Context::clear`,
/// which invalidates this plan. Registers cover the reachable subgraph, not the whole arena.
#[derive(Default)]
pub(super) struct Plan {
    roots: Vec<u32>,
    outputs: Vec<u32>,
    instructions: Vec<Instruction>,
    narrow: bool,
    has_native: bool,
    /// Needed only by mixed plans; homogeneous plans keep their simpler loops.
    routes: Vec<Route>,
    words: Vec<u128>,
    values: Vec<BitVec>,
}

struct Route {
    native: bool,
    /// The result needs a word register: native output or input to native arithmetic.
    word: bool,
    /// Compact BitVec register, or u32::MAX when no fallback consumes the result.
    value: u32,
}

struct Instruction {
    id: u32,
    /// Child fields hold register indices; non-child fields retain their original meaning.
    node: Node,
}

impl Plan {
    pub(super) fn clear(&mut self) {
        self.roots.clear();
        self.outputs.clear();
        self.instructions.clear();
        self.routes.clear();
        self.words.clear();
        self.values.clear();
    }

    fn native_supported(node: Node, width: impl Fn(u32) -> u16) -> bool {
        node.width <= 128
            && !node.op.is_fp()
            && node.op.as_ext().is_none()
            && node
                .op
                .as_bin()
                .is_none_or(|op| narrow::bin_supported(op, node.width))
            && node.children().all(|child| width(child) <= 128)
    }

    fn prepare(&mut self, cx: &mut Context, roots: &[u32]) {
        self.clear();
        let order = cx.post_order_ids(roots);
        let mut slots = IdMap::default();
        slots.reserve(order.len());
        self.instructions.reserve(order.len());
        self.narrow = true;
        self.has_native = false;
        for id in order {
            let mut node = cx.node(id);
            let native = Self::native_supported(node, |child| cx.wid(child));
            self.narrow &= native;
            self.has_native |= native;
            let arity = node.op.arity();
            if arity > 0 {
                node.a = slots[&node.a];
            }
            if arity > 1 {
                node.b = slots[&node.b];
            }
            if arity > 2 {
                node.c = slots[&node.c];
            }
            slots.insert(id, self.instructions.len() as u32);
            self.instructions.push(Instruction { id, node });
        }
        self.outputs.extend(roots.iter().map(|r| slots[r]));
        self.roots.extend_from_slice(roots);
        if self.narrow {
            self.words.resize(self.instructions.len(), 0);
        } else if !self.has_native {
            self.values
                .resize(self.instructions.len(), BitVec::zero(Width::W1));
        } else {
            self.routes.reserve(self.instructions.len());
            for inst in &self.instructions {
                let native =
                    Self::native_supported(inst.node, |r| self.instructions[r as usize].node.width);
                self.routes.push(Route {
                    native,
                    word: native,
                    value: if native { u32::MAX } else { 0 },
                });
            }
            for (slot, inst) in self.instructions.iter().enumerate() {
                let native = self.routes[slot].native;
                for child in inst.node.children() {
                    let route = &mut self.routes[child as usize];
                    if native {
                        route.word = true;
                    } else {
                        route.value = 0;
                    }
                }
            }
            let mut values = 0;
            for route in &mut self.routes {
                if route.value != u32::MAX {
                    route.value = values;
                    values += 1;
                }
            }
            self.values.resize(values as usize, BitVec::zero(Width::W1));
            let words = self
                .routes
                .iter()
                .rposition(|r| r.word)
                .map_or(0, |i| i + 1);
            self.words.resize(words, 0);
        }
    }

    // This dispatch is shared by both loops, but a call per node slows cheap arithmetic.
    #[inline(always)]
    fn eval_word(
        &self,
        cx: &Context,
        inst: &Instruction,
        env: &(impl Env + ?Sized),
    ) -> Result<u128, Error> {
        let n = inst.node;
        let get = |r: u32| self.words[r as usize];
        let width = |r: u32| self.instructions[r as usize].node.width;
        Ok(match n.op {
            OpCode::Const => cx.const_val(inst.id).unwrap().to_u128().unwrap(),
            OpCode::Sym => cx.eval_symbol(n.a, env)?.to_u128().unwrap(),
            OpCode::Zext => get(n.a),
            OpCode::Sext => narrow::signed(get(n.a), width(n.a)) as u128 & narrow::mask(n.width),
            OpCode::Extract => (get(n.a) >> n.b) & narrow::mask(n.width),
            OpCode::Concat => (get(n.a) << width(n.b)) | get(n.b),
            OpCode::Select => {
                if get(n.a) != 0 {
                    get(n.b)
                } else {
                    get(n.c)
                }
            }
            op => {
                if let Some(u) = op.as_un() {
                    narrow::un(u, n.width, get(n.a))
                } else if let Some(b) = op.as_bin() {
                    narrow::bin(b, n.width, get(n.a), get(n.b))
                } else {
                    u128::from(narrow::cmp(
                        op.as_cmp().unwrap(),
                        width(n.a),
                        get(n.a),
                        get(n.b),
                    ))
                }
            }
        })
    }

    // Keep the homogeneous loop independent of the mixed dispatch's code size and branches.
    #[inline(never)]
    fn run_narrow(
        &mut self,
        cx: &Context,
        env: &(impl Env + ?Sized),
    ) -> Result<Vec<BitVec>, Error> {
        for (slot, inst) in self.instructions.iter().enumerate() {
            self.words[slot] = self.eval_word(cx, inst, env)?;
        }
        Ok(self
            .outputs
            .iter()
            .map(|&r| {
                BitVec::wrapping_from_u128(
                    cx.width_of(self.instructions[r as usize].id),
                    self.words[r as usize],
                )
            })
            .collect())
    }

    fn run(&mut self, cx: &Context, env: &(impl Env + ?Sized)) -> Result<Vec<BitVec>, Error> {
        if self.narrow {
            return self.run_narrow(cx, env);
        }
        if !self.has_native {
            for (slot, inst) in self.instructions.iter().enumerate() {
                let v = cx.eval_node_mapped(
                    inst.id,
                    inst.node,
                    |r| self.values[r as usize],
                    |key, width| env.value(key, width),
                )?;
                self.values[slot] = v;
            }
            Ok(self
                .outputs
                .iter()
                .map(|&r| self.values[r as usize])
                .collect())
        } else {
            for (slot, inst) in self.instructions.iter().enumerate() {
                let route = &self.routes[slot];
                if route.native {
                    let v = self.eval_word(cx, inst, env)?;
                    self.words[slot] = v;
                    if route.value != u32::MAX {
                        self.values[route.value as usize] =
                            BitVec::wrapping_from_u128(cx.width_of(inst.id), v);
                    }
                } else {
                    let v = cx.eval_node_mapped(
                        inst.id,
                        inst.node,
                        |r| self.values[self.routes[r as usize].value as usize],
                        |key, width| env.value(key, width),
                    )?;
                    self.values[route.value as usize] = v;
                    if route.word {
                        self.words[slot] = v.to_u128().unwrap();
                    }
                }
            }
            Ok(self
                .outputs
                .iter()
                .map(|&r| {
                    let slot = r as usize;
                    let value = self.routes[slot].value;
                    if value != u32::MAX {
                        self.values[value as usize]
                    } else {
                        BitVec::wrapping_from_u128(
                            cx.width_of(self.instructions[slot].id),
                            self.words[slot],
                        )
                    }
                })
                .collect())
        }
    }
}

#[cfg(test)]
mod plan_tests {
    use super::*;
    use crate::{BinOp, UnOp};

    fn interpreted(cx: &mut Context, roots: &[Expr], env: &(impl Env + ?Sized)) -> Vec<BitVec> {
        let ids = cx.ids(roots).unwrap();
        let mut values = IdMap::default();
        for id in cx.post_order_ids(&ids) {
            let v = cx
                .eval_node(id, |i| values[&i], |k, w| env.value(k, w))
                .unwrap();
            values.insert(id, v);
        }
        ids.iter().map(|i| values[i]).collect()
    }

    #[test]
    fn evaluation_plans_agree_with_interpretation_at_width_boundaries() {
        for bits in [1, 7, 8, 31, 63, 64, 65, 127, 128, 129, 512] {
            let w = Width::new(bits).unwrap();
            let mut cx = Context::new();
            let a = cx.symbol("a", w).unwrap();
            let b = cx.symbol("b", w).unwrap();
            let c = cx.symbol("c", Width::W1).unwrap();
            let mut roots = vec![a, cx.select(c, a, b).unwrap()];
            let mut fallback = Vec::new();
            for op in OpCode::ALL {
                if let Some(u) = op.as_un() {
                    if u != UnOp::Bswap || bits % 8 == 0 {
                        roots.push(cx.un(u, a).unwrap());
                    }
                } else if let Some(bin) = op.as_bin() {
                    let e = cx.bin(bin, a, b).unwrap();
                    if bits > 64 && matches!(bin, BinOp::UMulHi | BinOp::SMulHi) {
                        fallback.push(e);
                    } else {
                        roots.push(e);
                    }
                } else if let Some(cmp) = op.as_cmp() {
                    roots.push(cx.cmp(cmp, a, b).unwrap());
                }
            }
            if bits > 1 {
                let half = Width::new(bits / 2).unwrap();
                let low = cx.extract(a, 0, half).unwrap();
                let high = cx
                    .extract(b, bits / 2, Width::new(bits - bits / 2).unwrap())
                    .unwrap();
                roots.extend([
                    low,
                    high,
                    cx.concat(high, low).unwrap(),
                    cx.zext(low, w).unwrap(),
                    cx.sext(low, w).unwrap(),
                ]);
            }
            let wide = cx.zero(Width::W512).unwrap();
            let mut mixed = roots.clone();
            mixed.push(wide);
            let points = [
                BitVec::zero(w),
                BitVec::one(w),
                BitVec::ones(w),
                BitVec::smin(w),
                BitVec::wrapping_from_limbs(w, &[0xaaaa_aaaa_aaaa_aaaa; 8]),
            ];
            for (i, &av) in points.iter().enumerate() {
                for (j, &bv) in points.iter().enumerate() {
                    let env: HashMap<_, _> = [
                        (SymbolKey::from("a"), av),
                        (SymbolKey::from("b"), bv),
                        (SymbolKey::from("c"), BitVec::from_bool((i + j) % 2 == 0)),
                    ]
                    .into_iter()
                    .collect();
                    let want = interpreted(&mut cx, &roots, &env);
                    assert_eq!(cx.eval(&roots, &env).unwrap(), want, "width {bits}");
                    assert_eq!(cx.eval(&roots, &env).unwrap(), want, "warm width {bits}");
                    assert_eq!(cx.eval_plan.as_ref().unwrap().narrow, bits <= 128);
                    let mut mixed_want = want.clone();
                    mixed_want.push(BitVec::zero(Width::W512));
                    assert_eq!(
                        cx.eval(&mixed, &env).unwrap(),
                        mixed_want,
                        "mixed width {bits}"
                    );
                    assert_eq!(
                        cx.eval(&mixed, &env).unwrap(),
                        mixed_want,
                        "warm mixed width {bits}"
                    );
                    if !fallback.is_empty() {
                        let want = interpreted(&mut cx, &fallback, &env);
                        assert_eq!(cx.eval(&fallback, &env).unwrap(), want);
                        assert!(!cx.eval_plan.as_ref().unwrap().narrow);
                    }
                }
            }
        }
    }

    #[test]
    fn evaluation_plans_refresh_inputs_roots_and_context_generations() {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::W8).unwrap();
        let y = cx.symbol("y", Width::W8).unwrap();
        let sum = cx.add(x, y).unwrap();
        let env = |a, b| {
            FnEnv(move |k: &SymbolKey, w| {
                Some(BitVec::wrapping_from_u64(
                    w,
                    if k == &SymbolKey::from("x") { a } else { b },
                ))
            })
        };
        assert_eq!(
            cx.eval(&[sum, x, sum], &env(2, 3))
                .unwrap()
                .iter()
                .map(BitVec::to_u64)
                .collect::<Vec<_>>(),
            vec![Some(5), Some(2), Some(5)]
        );
        assert_eq!(
            cx.eval(&[sum, x, sum], &env(7, 9)).unwrap()[0].to_u64(),
            Some(16)
        );
        assert!(
            cx.eval(&[sum, x, sum], &FnEnv(|_: &SymbolKey, _| None))
                .is_err()
        );
        assert!(matches!(
            cx.eval(
                &[sum, x, sum],
                &FnEnv(|_: &SymbolKey, _| Some(BitVec::zero(Width::W16)))
            ),
            Err(Error::EnvWidth { .. })
        ));
        assert_eq!(
            cx.eval(&[sum, x, sum], &env(1, 4)).unwrap()[0].to_u64(),
            Some(5)
        );
        assert_eq!(cx.eval(&[y, sum], &env(1, 4)).unwrap()[0].to_u64(), Some(4));
        assert!(cx.eval(&[], &env(1, 4)).unwrap().is_empty());
        cx.clear();
        let x2 = cx.symbol("x", Width::W8).unwrap();
        let y2 = cx.symbol("y", Width::W8).unwrap();
        let product = cx.bin(BinOp::Mul, x2, y2).unwrap();
        assert_eq!(product.index(), sum.index());
        assert!(matches!(cx.eval(&[sum], &env(2, 3)), Err(Error::StaleExpr)));
        assert_eq!(
            cx.eval(&[product], &env(2, 3)).unwrap()[0].to_u64(),
            Some(6)
        );
    }

    #[test]
    fn sparse_evaluation_plans_only_store_reachable_values_and_read_shared_symbols_once() {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::W64).unwrap();
        let y = cx.symbol("y", Width::W64).unwrap();
        let sum = cx.add(x, y).unwrap();
        for i in 0..10_000 {
            cx.symbol(SymbolKey::U64(i), Width::W512).unwrap();
        }
        let reads = std::cell::RefCell::new(Vec::new());
        let env = FnEnv(|key: &SymbolKey, w| {
            reads.borrow_mut().push(key.clone());
            Some(BitVec::one(w))
        });
        let want_order = cx
            .post_order(&[sum, x, sum])
            .unwrap()
            .into_iter()
            .filter_map(|e| cx.symbol_id(e).unwrap())
            .map(|s| cx.symbol_key(s).unwrap().clone())
            .collect::<Vec<_>>();
        for _ in 0..2 {
            reads.borrow_mut().clear();
            cx.eval(&[sum, x, sum], &env).unwrap();
            assert_eq!(*reads.borrow(), want_order);
            let plan = cx.eval_plan.as_ref().unwrap();
            assert_eq!(plan.instructions.len(), 3);
            assert_eq!(plan.words.len(), 3);
            assert!(plan.values.is_empty());
        }
    }

    #[test]
    fn mixed_evaluation_plans_only_materialize_values_needed_by_fallbacks() {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::W64).unwrap();
        let one = cx.one(Width::W64).unwrap();
        let mut root = x;
        for _ in 0..1000 {
            root = cx.add(root, one).unwrap();
        }
        let wide = cx.zero(Width::W512).unwrap();
        let reads = std::cell::Cell::new(0);
        let env = FnEnv(|_: &SymbolKey, w| {
            reads.set(reads.get() + 1);
            Some(BitVec::one(w))
        });
        let expected = BitVec::from_u64(Width::W64, 1001).unwrap();
        for _ in 0..2 {
            let values = cx.eval(&[root, wide, root], &env).unwrap();
            assert_eq!(values, [expected, BitVec::zero(Width::W512), expected]);
            let plan = cx.eval_plan.as_ref().unwrap();
            // The independent wide root must not require a BitVec for every narrow node.
            assert_eq!(plan.values.len(), 1);
        }
        assert_eq!(reads.get(), 2);
        assert!(matches!(
            cx.eval(&[root, wide, root], &FnEnv(|_: &SymbolKey, _| None)),
            Err(Error::UnboundSymbol { .. })
        ));
        assert!(matches!(
            cx.eval(
                &[root, wide, root],
                &FnEnv(|_: &SymbolKey, _| Some(BitVec::one(Width::W128)))
            ),
            Err(Error::EnvWidth { .. })
        ));
        assert_eq!(
            cx.eval(&[root, wide, root], &env).unwrap()[0].to_u64(),
            Some(1001)
        );
        assert_eq!(cx.eval(&[root], &env).unwrap()[0].to_u64(), Some(1001));
        assert!(cx.eval_plan.as_ref().unwrap().narrow);
    }

    #[test]
    fn mixed_evaluation_plans_cross_width_and_kernel_boundaries() {
        for bits in [129, 192, 255, 256, 511, 512] {
            let w = Width::new(bits).unwrap();
            let mut cx = Context::new();
            let x = cx.symbol("x", w).unwrap();
            let y = cx.symbol("y", Width::W64).unwrap();
            let lo = cx.extract(x, 0, Width::W64).unwrap();
            let hi = cx.extract(x, bits - 64, Width::W64).unwrap();
            let sum = cx.add(lo, y).unwrap();
            let extended = cx.sext(sum, w).unwrap();
            let wide = cx.add(x, extended).unwrap();
            let predicate = cx.cmp(crate::CmpOpExt::Slt, x, wide).unwrap();
            let selected = cx.select(predicate, sum, hi).unwrap();
            let wide_selected = cx.select(predicate, wide, extended).unwrap();
            let truncated = cx.extract(wide_selected, bits - 64, Width::W64).unwrap();
            let round_trip = cx.add(truncated, selected).unwrap();
            let lhs = cx.concat(hi, lo).unwrap();
            let rhs = cx.sext(sum, Width::W128).unwrap();
            let mut roots = vec![sum, wide, predicate, selected, wide_selected, round_trip];
            for op in [BinOp::UMulHi, BinOp::SMulHi] {
                let product = cx.bin(op, lhs, rhs).unwrap();
                let resumed = cx.add(product, lhs).unwrap();
                roots.extend([product, resumed]);
            }
            let roots2 = roots
                .iter()
                .rev()
                .copied()
                .chain([round_trip, sum])
                .collect::<Vec<_>>();
            for value in [
                BitVec::zero(w),
                BitVec::one(w),
                BitVec::ones(w),
                BitVec::smin(w),
                BitVec::wrapping_from_limbs(w, &[0x0123_4567_89ab_cdef; 8]),
            ] {
                let env = [
                    (SymbolKey::from("x"), value),
                    (
                        SymbolKey::from("y"),
                        BitVec::wrapping_from_u64(Width::W64, value.limbs()[0]),
                    ),
                ];
                for roots in [&roots, &roots, &roots2, &roots2] {
                    let want = interpreted(&mut cx, roots, &env[..]);
                    assert_eq!(cx.eval(roots, &env[..]).unwrap(), want, "width {bits}");
                }
            }
        }
    }

    #[test]
    fn mixed_evaluation_plans_cross_floating_point_boundaries() {
        use crate::fp::{FpCmpOp, FpFormat, FpOp, RoundingMode};
        for format in [FpFormat::F32, FpFormat::F64, FpFormat::F128] {
            let mut cx = Context::new();
            let x = cx.symbol("x", Width::W64).unwrap();
            let y = cx.symbol("y", format.width()).unwrap();
            let one = cx.one(Width::W64).unwrap();
            let incremented = cx.add(x, one).unwrap();
            let f = cx
                .fp(FpOp::FromUInt(RoundingMode::Rne), format, &[incremented])
                .unwrap();
            let fsum = cx
                .fp(FpOp::Add(RoundingMode::Rne), format, &[f, y])
                .unwrap();
            let fma = cx
                .fp(FpOp::Fma(RoundingMode::Rne), format, &[f, y, fsum])
                .unwrap();
            let converted = cx
                .fp(
                    FpOp::Convert {
                        to: FpFormat::F32,
                        rm: RoundingMode::Rne,
                    },
                    format,
                    &[fma],
                )
                .unwrap();
            let raw_bits = cx.extract(converted, 0, Width::W8).unwrap();
            let resumed = cx.add(raw_bits, raw_bits).unwrap();
            let integer = cx
                .fp(FpOp::ToUInt(RoundingMode::Rtz, Width::W64), format, &[fsum])
                .unwrap();
            let predicate = cx.fp_cmp(format, FpCmpOp::Lt, y, f).unwrap();
            let selected = cx.select(predicate, integer, incremented).unwrap();
            let result = cx.add(selected, one).unwrap();
            let roots = [
                incremented,
                fsum,
                fma,
                converted,
                resumed,
                integer,
                predicate,
                result,
            ];
            for fv in [
                format.zero(false),
                format.zero(true),
                format.inf(false),
                format.nan(),
                format.from_uint(
                    RoundingMode::Rne,
                    &BitVec::from_u64(Width::W64, 17).unwrap(),
                ),
            ] {
                let env = [
                    (
                        SymbolKey::from("x"),
                        BitVec::from_u64(Width::W64, 42).unwrap(),
                    ),
                    (SymbolKey::from("y"), fv),
                ];
                let want = interpreted(&mut cx, &roots, &env[..]);
                for _ in 0..2 {
                    assert_eq!(cx.eval(&roots, &env[..]).unwrap(), want, "{format:?}");
                }
            }
        }
    }

    #[test]
    fn mixed_evaluation_plans_cross_extension_boundaries() {
        use crate::ext::{ExtOp, ExtSig, Registry};
        struct WidePair;
        impl ExtOp for WidePair {
            fn name(&self) -> &str {
                "test.widepair"
            }
            fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
                match args {
                    [w] => Ok(ExtSig::new(&[("wide", Width::W512), ("inverted", *w)])),
                    _ => Err("one argument".into()),
                }
            }
            fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
                out[0] = args[0].zext(Width::W512).unwrap();
                out[1] = BitVec::apply_un(UnOp::Not, &args[0]).unwrap();
            }
        }
        let registry = std::sync::Arc::new(Registry::builder().register(WidePair).unwrap().build());
        let op = registry.id("test.widepair").unwrap();
        let mut cx = Context::with_registry(crate::ContextConfig::default(), registry);
        let x = cx.symbol("x", Width::W64).unwrap();
        let one = cx.one(Width::W64).unwrap();
        let incremented = cx.add(x, one).unwrap();
        let outputs = cx.ext(op, &[incremented]).unwrap();
        let low = cx.extract(outputs[0], 0, Width::W64).unwrap();
        let sum = cx.add(low, outputs[1]).unwrap();
        let again = cx.ext(op, &[sum]).unwrap();
        let roots = [incremented, outputs[0], outputs[1], sum, again[0], again[1]];
        for value in [0, 1, u64::MAX, 0x0123_4567_89ab_cdef] {
            let env = [(
                SymbolKey::from("x"),
                BitVec::from_u64(Width::W64, value).unwrap(),
            )];
            let want = interpreted(&mut cx, &roots, &env[..]);
            for _ in 0..2 {
                assert_eq!(cx.eval(&roots, &env[..]).unwrap(), want);
            }
        }
    }
}

/// Values for symbols, used by [`Context::eval`].
pub trait Env {
    /// The value bound to the symbol `key` of width `width`, if any.
    fn value(&self, key: &SymbolKey, width: Width) -> Option<BitVec>;
}

impl<S: BuildHasher> Env for HashMap<SymbolKey, BitVec, S> {
    fn value(&self, key: &SymbolKey, _width: Width) -> Option<BitVec> {
        self.get(key).copied()
    }
}

impl Env for BTreeMap<SymbolKey, BitVec> {
    fn value(&self, key: &SymbolKey, _width: Width) -> Option<BitVec> {
        self.get(key).copied()
    }
}

impl Env for [(SymbolKey, BitVec)] {
    fn value(&self, key: &SymbolKey, _width: Width) -> Option<BitVec> {
        self.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
    }
}

/// An [`Env`] backed by a closure.
#[derive(Clone, Copy, Debug)]
pub struct FnEnv<F>(pub F);

impl<F: Fn(&SymbolKey, Width) -> Option<BitVec>> Env for FnEnv<F> {
    fn value(&self, key: &SymbolKey, width: Width) -> Option<BitVec> {
        (self.0)(key, width)
    }
}

impl Context {
    /// Evaluates `roots` under `env`. Iterative and memoized per call: a shared node is
    /// evaluated once. Repeating the same root set reuses its evaluation schedule and
    /// register storage; symbol values are read from `env` on every call.
    pub fn eval(
        &mut self,
        roots: &[Expr],
        env: &(impl Env + ?Sized),
    ) -> Result<Vec<BitVec>, Error> {
        let ids = self.ids(roots)?;
        self.eval_ids(&ids, env)
    }

    pub(crate) fn eval_ids(
        &mut self,
        roots: &[u32],
        env: &(impl Env + ?Sized),
    ) -> Result<Vec<BitVec>, Error> {
        if roots.is_empty() {
            return Ok(Vec::new());
        }
        let mut plan = self.eval_plan.take().unwrap_or_default();
        if plan.roots != roots {
            plan.prepare(self, roots);
        }
        let result = plan.run(self, env);
        self.eval_plan = Some(plan);
        result
    }

    fn eval_symbol(&self, symbol: u32, env: &(impl Env + ?Sized)) -> Result<BitVec, Error> {
        let entry = &self.symbols.entries[symbol as usize];
        let v = env
            .value(&entry.key, entry.width)
            .ok_or_else(|| Error::UnboundSymbol {
                key: entry.key.clone(),
            })?;
        if v.width() != entry.width {
            return Err(Error::EnvWidth {
                key: entry.key.clone(),
                expected: entry.width,
                got: v.width(),
            });
        }
        Ok(v)
    }

    /// The value of node `i` from its operands' values (`get`) and symbol values (`sym`).
    pub(crate) fn eval_node(
        &self,
        i: u32,
        get: impl Fn(u32) -> BitVec,
        sym: impl Fn(&SymbolKey, Width) -> Option<BitVec>,
    ) -> Result<BitVec, Error> {
        self.eval_node_mapped(i, self.node(i), get, sym)
    }

    fn eval_node_mapped(
        &self,
        i: u32,
        n: Node,
        get: impl Fn(u32) -> BitVec,
        sym: impl Fn(&SymbolKey, Width) -> Option<BitVec>,
    ) -> Result<BitVec, Error> {
        Ok(match n.op {
            OpCode::Const => self.const_val(i).unwrap_or(BitVec::zero(Width::W1)),
            OpCode::Sym => {
                let entry = &self.symbols.entries[n.a as usize];
                let v = sym(&entry.key, entry.width).ok_or_else(|| Error::UnboundSymbol {
                    key: entry.key.clone(),
                })?;
                if v.width() != entry.width {
                    return Err(Error::EnvWidth {
                        key: entry.key.clone(),
                        expected: entry.width,
                        got: v.width(),
                    });
                }
                v
            }
            OpCode::Zext => get(n.a).zext(self.width_of(i))?,
            OpCode::Sext => get(n.a).sext(self.width_of(i))?,
            OpCode::Extract => get(n.a).extract(n.b as u16, self.width_of(i))?,
            OpCode::Concat => BitVec::concat(&get(n.a), &get(n.b))?,
            OpCode::Select => BitVec::select(&get(n.a), &get(n.b), &get(n.c))?,
            op if op.as_ext().is_some() => {
                let args: Vec<BitVec> = n.children().map(&get).collect();
                self.eval_ext(i, &args)?
            }
            op => {
                if let Some(u) = op.as_un() {
                    BitVec::apply_un(u, &get(n.a))?
                } else if let Some(b) = op.as_bin() {
                    BitVec::bin_unchecked(b, &get(n.a), &get(n.b))
                } else if let Some(c) = op.as_cmp() {
                    BitVec::from_bool(BitVec::cmp_unchecked(c, &get(n.a), &get(n.b)))
                } else if let Some(d) = self.fp_desc(i) {
                    let args: Vec<BitVec> = n.children().map(&get).collect();
                    crate::fp::eval(&d, &args)
                } else {
                    unreachable!("every opcode is covered")
                }
            }
        })
    }

    /// The value of extension node `i` for argument values `args` (validated against the
    /// operation's declared widths).
    pub(crate) fn eval_ext(&self, i: u32, args: &[BitVec]) -> Result<BitVec, Error> {
        let n = self.node(i);
        let (_, k) = n.op.as_ext().unwrap_or((1, 0));
        let op = self
            .registry
            .as_deref()
            .and_then(|r| r.op_at(n.aux))
            .ok_or_else(|| Error::Contract("an extension node without its operation".into()))?;
        let out = crate::ext::run_eval(op, args)
            .map_err(|why| Error::Contract(format!("`{}`: {why}", op.name())))?;
        out.get(k)
            .copied()
            .ok_or_else(|| Error::Contract(format!("`{}` has no output {k}", op.name())))
    }

    /// Simultaneously replaces every occurrence of each `from` by its `to` in `roots`
    /// (replacements are not substituted again), rebuilding through the canonicalizing
    /// constructors. Each pair must have equal widths.
    pub fn substitute(&mut self, roots: &[Expr], map: &[(Expr, Expr)]) -> Result<Vec<Expr>, Error> {
        let ids = self.ids(roots)?;
        let mut repl: IdMap<u32, u32> = IdMap::default();
        for &(from, to) in map {
            let (f, t) = (self.id(from)?, self.id(to)?);
            let (wf, wt) = (self.wid(f), self.wid(t));
            if wf != wt {
                return Err(crate::WidthError::Mismatch {
                    left: wf,
                    right: wt,
                }
                .into());
            }
            if repl.insert(f, t).is_some() {
                return Err(Error::DuplicateSubstitution);
            }
        }
        let out = self.substitute_ids(&ids, &repl)?;
        Ok(out.into_iter().map(|i| self.handle(i)).collect())
    }

    /// Applies the substitution `s` to `roots`, working on at most `max_visits` nodes not
    /// already in its memo. `Ok(None)` when that limit stops it first: the progress is kept in
    /// `s`, so a later call continues where this one stopped. The walk never descends below a
    /// replaced node or a node the memo already answers.
    pub fn substitute_bounded(
        &mut self,
        roots: &[Expr],
        s: &mut Substitution,
        max_visits: u64,
    ) -> Result<Option<Vec<Expr>>, Error> {
        let ids = self.ids(roots)?;
        s.check_context(self)?;
        let mut visits = 0u64;
        // Resume the walk a previous call over the same roots stopped in.
        let (mut next_root, mut stack) = match s.pending.take() {
            Some(p) if p.roots == ids => (p.next_root, p.stack),
            _ => (0, Vec::new()),
        };
        loop {
            if stack.is_empty() {
                let Some(&root) = ids.get(next_root) else {
                    break;
                };
                next_root += 1;
                if !s.done.contains_key(&root) {
                    stack.push((root, false));
                }
                continue;
            }
            let Some(&(i, expanded)) = stack.last() else {
                break;
            };
            if s.done.contains_key(&i) {
                stack.pop();
                continue;
            }
            if let Some(&t) = s.repl.get(&i) {
                stack.pop();
                s.done.insert(i, t);
                continue;
            }
            let n = self.node(i);
            if !expanded {
                if visits >= max_visits {
                    s.pending = Some(Pending {
                        roots: ids,
                        next_root,
                        stack,
                    });
                    return Ok(None);
                }
                visits += 1;
                if let Some(top) = stack.last_mut() {
                    top.1 = true;
                }
                for c in n.children() {
                    if !s.done.contains_key(&c) {
                        stack.push((c, false));
                    }
                }
                continue;
            }
            stack.pop();
            let mut kids = [n.a, n.b, n.c];
            let mut changed = false;
            for (k, c) in n.children().enumerate() {
                let nc = s.done[&c];
                changed |= nc != c;
                kids[k] = nc;
            }
            let r = if changed { self.rebuild(i, kids)? } else { i };
            s.done.insert(i, r);
        }
        Ok(Some(ids.iter().map(|r| self.handle(s.done[r])).collect()))
    }

    pub(crate) fn substitute_ids(
        &mut self,
        roots: &[u32],
        repl: &IdMap<u32, u32>,
    ) -> Result<Vec<u32>, Error> {
        if repl.is_empty() {
            return Ok(roots.to_vec());
        }
        let order = self.post_order_ids_pruned(roots, |e| repl.contains_key(&e.index()));
        let mut new = repl.clone();
        for i in order {
            let n = self.node(i);
            let mut kids = [n.a, n.b, n.c];
            let mut changed = false;
            for (k, c) in n.children().enumerate() {
                let nc = new[&c];
                changed |= nc != c;
                kids[k] = nc;
            }
            let r = if changed { self.rebuild(i, kids)? } else { i };
            new.insert(i, r);
        }
        Ok(roots.iter().map(|r| new[r]).collect())
    }
}

/// A stopped substitution walk: the roots, the next root to start, and the stack.
#[derive(Clone, Debug)]
struct Pending {
    roots: Vec<u32>,
    next_root: usize,
    stack: Vec<(u32, bool)>,
}

/// A substitution applied incrementally by [`Context::substitute_bounded`]: the replacements,
/// and the result of every node rewritten so far. Repeated calls share that work, and a caller
/// can read which new node each old one became (to carry its own metadata along).
#[derive(Clone, Debug, Default)]
pub struct Substitution {
    repl: IdMap<u32, u32>,
    done: IdMap<u32, u32>,
    /// The walk a call stopped in, resumed by the next call over the same roots.
    pending: Option<Pending>,
    /// A handle of the context the substitution belongs to (to reject another context's).
    probe: Option<Expr>,
}

impl Substitution {
    /// An empty substitution.
    pub fn new() -> Self {
        Self::default()
    }

    /// Replaces every occurrence of `from` by `to` (not substituted again). The widths must
    /// match, `from` may be given once, and no node may have been rewritten yet.
    pub fn replace(&mut self, cx: &Context, from: Expr, to: Expr) -> Result<&mut Self, Error> {
        let (f, t) = (cx.id(from)?, cx.id(to)?);
        self.check_context(cx)?;
        let (wf, wt) = (cx.wid(f), cx.wid(t));
        if wf != wt {
            return Err(crate::WidthError::Mismatch {
                left: wf,
                right: wt,
            }
            .into());
        }
        if !self.done.is_empty() {
            return Err(Error::Unsupported(
                "a replacement added after the substitution was applied".into(),
            ));
        }
        if self.repl.insert(f, t).is_some() {
            return Err(Error::DuplicateSubstitution);
        }
        self.probe.get_or_insert(from);
        Ok(self)
    }

    /// What `e` became, if the substitution has reached it.
    pub fn image(&self, cx: &Context, e: Expr) -> Result<Option<Expr>, Error> {
        let i = cx.id(e)?;
        Ok(self.done.get(&i).map(|&r| cx.handle(r)))
    }

    /// Every node reached so far that changed, with what it became, in node order.
    pub fn changed(&self, cx: &Context) -> Vec<(Expr, Expr)> {
        let mut v: Vec<(u32, u32)> = self
            .done
            .iter()
            .filter(|(a, b)| a != b)
            .map(|(&a, &b)| (a, b))
            .collect();
        v.sort_unstable();
        v.into_iter()
            .map(|(a, b)| (cx.handle(a), cx.handle(b)))
            .collect()
    }

    fn check_context(&self, cx: &Context) -> Result<(), Error> {
        if let Some(p) = self.probe {
            cx.id(p)?;
        }
        Ok(())
    }
}

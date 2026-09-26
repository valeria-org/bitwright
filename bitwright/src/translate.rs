//! A host's IR in and out: its instructions translated into expressions ([`Semantics`],
//! [`Lowering`]), and results translated back into instructions ([`Raise`]), without text.
//!
//! A compiler describes what each of its instructions computes once, as a [`Semantics`]
//! implementation, in Rust or as a [`Template`] in the expression syntax, read at run time. A
//! [`Lowering`] then turns a function (or a block) into expressions: it maps the host's values
//! to expressions, and makes a symbol for each value defined elsewhere (a parameter, a load, a
//! call), with the known bits the host has of it if it has any. After simplifying,
//! [`Lowering::raise`] turns a result back into instructions: a node some host value already
//! computes is that value (equal expressions are equal values, so this is value numbering),
//! and only the nodes no value computes are emitted, operands first, through the host's
//! [`Raise`].
//!
//! ```
//! use bitwright::engine::{Engine, Strategy};
//! use bitwright::translate::{Lowering, Raise, Semantics, Template};
//! use bitwright::{Context, Error, Expr, View, Width};
//!
//! // A toy IR: SSA values are indices.
//! enum Op { Add, Sub, And, Or }
//! struct Inst { op: Op, dst: u32, a: u32, b: u32 }
//!
//! impl Semantics for Inst {
//!     type Value = u32;
//!     fn result(&self) -> Option<u32> { Some(self.dst) }
//!     fn lower(&self, lw: &mut Lowering<'_, u32>) -> Result<Expr, Error> {
//!         let (a, b) = (lw.value(self.a, Width::W32)?, lw.value(self.b, Width::W32)?);
//!         let cx = lw.context();
//!         match self.op {
//!             Op::Add => cx.add(a, b),
//!             Op::Sub => cx.sub(a, b),
//!             Op::And => cx.and(a, b),
//!             Op::Or => cx.or(a, b),
//!         }
//!     }
//! }
//!
//! // Emitting back: new instructions get new value numbers.
//! struct Emit { next: u32, out: Vec<String> }
//! impl Raise for Emit {
//!     type Value = u32;
//!     fn emit(&mut self, cx: &Context, _: Expr, node: &View, ops: &[u32]) -> Result<u32, Error> {
//!         let dst = self.next;
//!         self.next += 1;
//!         let text = match node {
//!             View::Bin(op, ..) => format!("%{dst} = {op:?} %{}, %{}", ops[0], ops[1]),
//!             other => return Err(Error::Unsupported(format!("{other:?}"))),
//!         };
//!         self.out.push(text);
//!         Ok(dst)
//!     }
//! }
//!
//! let engine = Engine::builder().builtin().strategy(Strategy::compile()).build()?;
//! let mut cx = Context::new();
//! let mut lw = Lowering::new(&mut cx);
//! // %2 = and %0, %1; %3 = or %0, %1; %4 = add %2, %3; %5 = sub %4, %1
//! let body = [
//!     Inst { op: Op::And, dst: 2, a: 0, b: 1 },
//!     Inst { op: Op::Or, dst: 3, a: 0, b: 1 },
//!     Inst { op: Op::Add, dst: 4, a: 2, b: 3 },
//!     Inst { op: Op::Sub, dst: 5, a: 4, b: 1 },
//! ];
//! lw.lower_all(&body)?;
//! let v5 = lw.get(5).unwrap();
//! let out = engine.simplify(lw.context(), v5)?;
//! // (x & y) + (x | y) - y is x: the parameter %0 itself, nothing to emit.
//! let mut emit = Emit { next: 6, out: Vec::new() };
//! assert_eq!(lw.raise(out.expr, &mut emit)?, 0);
//! assert!(emit.out.is_empty());
//!
//! // Semantics as text, read at run time: an absolute difference this IR has as one
//! // instruction.
//! let absdiff = Template::new("select(a <u b, b - a, a - b)", &["a", "b"])?;
//! let (a, b) = (lw.value(0, Width::W32)?, lw.value(1, Width::W32)?);
//! let d = absdiff.instantiate(lw.context(), &[a, b])?;
//! assert_eq!(lw.context().width(d)?, Width::W32);
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

use core::fmt;
use core::hash::Hash;
use std::collections::HashMap;
use std::sync::Mutex;

use crate::error::{Error, WidthError};
use crate::expr::{Context, Expr, View};
use crate::facts::KnownBits;
use crate::{ParseOptions, SymbolKey, Width};

/// What an instruction of the host's IR computes, as an expression.
pub trait Semantics {
    /// The host's handle of a value (an SSA value number, say).
    type Value: Copy + Eq + Hash;

    /// The value the instruction defines, if it defines one (a store or a branch does not,
    /// and is not lowered).
    fn result(&self) -> Option<Self::Value>;

    /// The expression of the instruction's result, over its operands' expressions (read
    /// with [`Lowering::value`], built with [`Lowering::context`]).
    fn lower(&self, lw: &mut Lowering<'_, Self::Value>) -> Result<Expr, Error>;
}

/// Turns expression nodes back into the host's instructions (see [`Lowering::raise`]).
pub trait Raise {
    /// The host's handle of a value.
    type Value: Copy;

    /// Emits instructions computing node `e` (`node` is its [`View`]) from the host values of
    /// its operands, in the order the view lists them (none for a constant or a symbol);
    /// returns the value that holds it. Called only for nodes no host value computes yet,
    /// operands first.
    fn emit(
        &mut self,
        cx: &Context,
        e: Expr,
        node: &View,
        operands: &[Self::Value],
    ) -> Result<Self::Value, Error>;
}

/// A function (or block) of the host's IR being translated into expressions of a context: the
/// expression of every host value it has seen, and a symbol for every value defined outside.
pub struct Lowering<'cx, V> {
    cx: &'cx mut Context,
    /// The expression of each host value: its definition, or its symbol.
    exprs: HashMap<V, Expr>,
    /// The values defined outside, in the order first read, with their symbols.
    inputs: Vec<(V, Expr)>,
    /// The first host value that computes each expression (its owner, for raising).
    owners: HashMap<Expr, V>,
}

impl<V> fmt::Debug for Lowering<'_, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Lowering")
            .field("values", &self.exprs.len())
            .field("inputs", &self.inputs.len())
            .finish_non_exhaustive()
    }
}

/// A [`Lowering`]'s values detached from its context: what a host keeps between the calls
/// that lower a function, when the context is used on its own in between (a language binding,
/// which cannot keep a borrow of it). [`attach`](Self::attach) it to the same context to go on;
/// with another, its expressions are foreign handles, rejected wherever they are used.
pub struct Lowered<V> {
    exprs: HashMap<V, Expr>,
    inputs: Vec<(V, Expr)>,
    owners: HashMap<Expr, V>,
}

impl<V> fmt::Debug for Lowered<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Lowered")
            .field("values", &self.exprs.len())
            .field("inputs", &self.inputs.len())
            .finish_non_exhaustive()
    }
}

impl<V> Default for Lowered<V> {
    fn default() -> Self {
        Lowered {
            exprs: HashMap::new(),
            inputs: Vec::new(),
            owners: HashMap::new(),
        }
    }
}

impl<V: Copy + Eq + Hash> Lowered<V> {
    /// The expression of host value `v`, if it has one ([`Lowering::get`]).
    pub fn get(&self, v: V) -> Option<Expr> {
        self.exprs.get(&v).copied()
    }

    /// The values defined outside that were read ([`Lowering::inputs`]).
    pub fn inputs(&self) -> &[(V, Expr)] {
        &self.inputs
    }

    /// A host value that computes `e` already, if one does ([`Lowering::owner`]).
    pub fn owner(&self, e: Expr) -> Option<V> {
        self.owners.get(&e).copied()
    }

    /// The lowering again, over `cx`.
    pub fn attach(self, cx: &mut Context) -> Lowering<'_, V> {
        Lowering {
            cx,
            exprs: self.exprs,
            inputs: self.inputs,
            owners: self.owners,
        }
    }
}

impl<'cx, V: Copy + Eq + Hash> Lowering<'cx, V> {
    /// A lowering into `cx` (reuse one context per function: [`Context::clear`] keeps its
    /// allocations).
    pub fn new(cx: &'cx mut Context) -> Self {
        Lowered::default().attach(cx)
    }

    /// Releases the context, keeping the values: [`Lowered::attach`] resumes.
    pub fn detach(self) -> Lowered<V> {
        Lowered {
            exprs: self.exprs,
            inputs: self.inputs,
            owners: self.owners,
        }
    }

    /// The context, to build expressions in (and to simplify).
    pub fn context(&mut self) -> &mut Context {
        self.cx
    }

    /// The expression of host value `v` of `width` bits: its definition, or for a value not
    /// defined here, a new symbol that stands for it (see [`input`](Self::input)). A width
    /// other than the value's is an error.
    pub fn value(&mut self, v: V, width: Width) -> Result<Expr, Error> {
        match self.exprs.get(&v) {
            Some(&e) => {
                let have = self.cx.width(e)?;
                if have != width {
                    return Err(WidthError::Mismatch {
                        left: have.bits(),
                        right: width.bits(),
                    }
                    .into());
                }
                Ok(e)
            }
            None => self.input(v, width, None),
        }
    }

    /// A value defined outside (a parameter, a load, a call result): a fresh symbol of
    /// `width` bits that stands for it, with the known bits the host has of it, if any
    /// ([`Context::declare_known`]). Its expression if it already has one.
    pub fn input(&mut self, v: V, width: Width, known: Option<KnownBits>) -> Result<Expr, Error> {
        if let Some(&e) = self.exprs.get(&v) {
            return Ok(e);
        }
        let s = self.cx.fresh_symbol(width)?;
        self.bind_input(v, s, known)
    }

    /// [`input`](Self::input) with a symbol of the host's choosing (a readable name, say).
    /// The key must not be a symbol of another width in the context.
    pub fn input_named(
        &mut self,
        v: V,
        key: impl Into<SymbolKey>,
        width: Width,
        known: Option<KnownBits>,
    ) -> Result<Expr, Error> {
        if let Some(&e) = self.exprs.get(&v) {
            return Ok(e);
        }
        let s = self.cx.symbol(key, width)?;
        self.bind_input(v, s, known)
    }

    fn bind_input(&mut self, v: V, s: Expr, known: Option<KnownBits>) -> Result<Expr, Error> {
        if let Some(k) = known {
            self.cx.declare_known(s, k)?;
        }
        self.exprs.insert(v, s);
        self.inputs.push((v, s));
        self.owners.entry(s).or_insert(v);
        Ok(s)
    }

    /// Records that host value `v` is `e` (an expression of this context).
    pub fn define(&mut self, v: V, e: Expr) -> Result<(), Error> {
        self.cx.id(e)?;
        self.exprs.insert(v, e);
        self.owners.entry(e).or_insert(v);
        Ok(())
    }

    /// Lowers one instruction: defines its result, if it has one, and returns its expression.
    pub fn lower<S: Semantics<Value = V> + ?Sized>(
        &mut self,
        inst: &S,
    ) -> Result<Option<Expr>, Error> {
        let Some(v) = inst.result() else {
            return Ok(None);
        };
        let e = inst.lower(self)?;
        self.define(v, e)?;
        Ok(Some(e))
    }

    /// Lowers instructions in order (each defines its result before the next reads it).
    pub fn lower_all<'i, S, I>(&mut self, insts: I) -> Result<(), Error>
    where
        S: Semantics<Value = V> + 'i,
        I: IntoIterator<Item = &'i S>,
    {
        for inst in insts {
            self.lower(inst)?;
        }
        Ok(())
    }

    /// The expression of host value `v`, if it has one.
    pub fn get(&self, v: V) -> Option<Expr> {
        self.exprs.get(&v).copied()
    }

    /// The values defined outside that were read, in order, with their symbols.
    pub fn inputs(&self) -> &[(V, Expr)] {
        &self.inputs
    }

    /// A host value that computes `e` already, if one does (the first defined).
    pub fn owner(&self, e: Expr) -> Option<V> {
        self.owners.get(&e).copied()
    }

    /// Turns `e` into host instructions: the value computing it. A node some host value
    /// computes is that value; every other node is emitted through `r`, operands first, and
    /// then owned by the value `r` returns (so later raises reuse it). A symbol no host value
    /// stands for is an error.
    pub fn raise<R: Raise<Value = V> + ?Sized>(&mut self, e: Expr, r: &mut R) -> Result<V, Error> {
        let mut ops: Vec<V> = Vec::new();
        for n in self.unraised(e)? {
            let view = self.cx.view(n)?;
            ops.clear();
            for c in self.cx.children(n)? {
                ops.push(self.owners[&c]);
            }
            let v = r.emit(self.cx, n, &view, &ops)?;
            self.emitted(n, v)?;
        }
        Ok(self.owners[&e])
    }

    /// The nodes of `e` that [`raise`](Self::raise) would emit, operands first: those no host
    /// value computes. With [`emitted`](Self::emitted), a raise in steps, for a host that must
    /// emit with the context released (a language binding calling back into its interpreter).
    /// A symbol no host value stands for is an error.
    pub fn unraised(&mut self, e: Expr) -> Result<Vec<Expr>, Error> {
        if self.owner(e).is_some() {
            return Ok(Vec::new());
        }
        let mut order = self.cx.post_order(&[e])?;
        order.retain(|n| !self.owners.contains_key(n));
        for &n in &order {
            if matches!(self.cx.view(n)?, View::Sym(_)) {
                return Err(Error::Unsupported(format!(
                    "symbol {} stands for no host value",
                    self.cx.display(n)
                )));
            }
        }
        Ok(order)
    }

    /// Records that host value `v` computes node `e`, emitted by the host: what
    /// [`raise`](Self::raise) does after each emit. Later raises reuse it.
    pub fn emitted(&mut self, e: Expr, v: V) -> Result<(), Error> {
        self.cx.id(e)?;
        self.exprs.entry(v).or_insert(e);
        self.owners.insert(e, v);
        Ok(())
    }
}

/// An instruction's semantics as an expression over named parameters, in the expression
/// syntax, read at run time: `select(a <s b, a, b)`, `(a >>u k) | (a << (0 - k))`. The
/// parameters take the widths of the operands it is instantiated with, and a literal whose
/// width the expression does not fix takes the widest operand's. It is compiled once per
/// combination of widths and then instantiated by copying, with no parsing. It can be shared
/// between threads.
pub struct Template {
    text: String,
    params: Vec<String>,
    /// Compiled forms by operand widths: a context holding the expression over the
    /// parameters' symbols.
    compiled: Mutex<Vec<(Vec<Width>, Compiled)>>,
}

struct Compiled {
    cx: Context,
    root: Expr,
    /// The parameters' symbol nodes, in order.
    params: Vec<u32>,
}

impl fmt::Debug for Template {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Template")
            .field("text", &self.text)
            .field("params", &self.params)
            .finish_non_exhaustive()
    }
}

impl Template {
    /// A template over parameters `params` (distinct symbol names in `text`). The text is
    /// read when the template is first instantiated at some widths, or checked at them with
    /// [`check`](Self::check).
    pub fn new(text: &str, params: &[&str]) -> Result<Template, Error> {
        for (k, p) in params.iter().enumerate() {
            if p.is_empty() || params[..k].contains(p) {
                return Err(Error::Unsupported(format!(
                    "template parameter `{p}` is empty or repeated"
                )));
            }
        }
        Ok(Template {
            text: text.to_string(),
            params: params.iter().map(|p| (*p).to_string()).collect(),
            compiled: Mutex::new(Vec::new()),
        })
    }

    /// Reads the text with the parameters of these widths (and keeps the result): a syntax or
    /// width error now, not at the first instantiation (to check a host's templates when it
    /// starts, say).
    pub fn check(&self, widths: &[Width]) -> Result<(), Error> {
        if widths.len() != self.params.len() {
            return Err(self.arity(widths.len()));
        }
        self.with_compiled(widths, |_| Ok(()))
    }

    fn arity(&self, got: usize) -> Error {
        Error::Unsupported(format!(
            "the template takes {} operands, not {got}",
            self.params.len()
        ))
    }

    /// Runs `f` on the template compiled at `widths`, compiling it first if needed.
    fn with_compiled<T>(
        &self,
        widths: &[Width],
        f: impl FnOnce(&Compiled) -> Result<T, Error>,
    ) -> Result<T, Error> {
        let mut compiled = self
            .compiled
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let k = match compiled.iter().position(|(w, _)| w == widths) {
            Some(k) => k,
            None => {
                let c = self.compile(widths)?;
                compiled.push((widths.to_vec(), c));
                compiled.len() - 1
            }
        };
        f(&compiled[k].1)
    }

    fn compile(&self, widths: &[Width]) -> Result<Compiled, Error> {
        let mut cx = Context::new();
        let mut params = Vec::with_capacity(self.params.len());
        for (p, &w) in self.params.iter().zip(widths) {
            let s = cx.symbol(p.as_str(), w)?;
            params.push(cx.id(s)?);
        }
        // Literals the expression does not give a width take the widest operand's.
        let default = widths.iter().copied().max().unwrap_or(Width::W64);
        let root = cx.parse(&self.text, &ParseOptions::width(default))?;
        Ok(Compiled { cx, root, params })
    }

    /// The template's expression in `cx`, with its parameters bound to `args` (one per
    /// parameter, in order).
    pub fn instantiate(&self, cx: &mut Context, args: &[Expr]) -> Result<Expr, Error> {
        if args.len() != self.params.len() {
            return Err(self.arity(args.len()));
        }
        let widths: Vec<Width> = args
            .iter()
            .map(|&a| cx.width(a))
            .collect::<Result<_, _>>()?;
        self.with_compiled(&widths, |c| {
            let pre: Vec<(u32, u32)> = c
                .params
                .iter()
                .zip(args)
                .map(|(&p, &a)| Ok((p, cx.id(a)?)))
                .collect::<Result<_, Error>>()?;
            Ok(cx.import_mapped(&c.cx, &[c.root], &pre)?[0])
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BinOp, BitVec, CmpOp, FnEnv};

    /// A test IR: `dst = op a, b` over 8-bit values.
    struct Bin(u32, BinOp, u32, u32);
    impl Semantics for Bin {
        type Value = u32;
        fn result(&self) -> Option<u32> {
            Some(self.0)
        }
        fn lower(&self, lw: &mut Lowering<'_, u32>) -> Result<Expr, Error> {
            let (a, b) = (lw.value(self.2, Width::W8)?, lw.value(self.3, Width::W8)?);
            lw.context().bin(self.1, a, b)
        }
    }

    /// Records what it emits; new values from 100.
    struct Rec(Vec<String>);
    impl Raise for Rec {
        type Value = u32;
        fn emit(&mut self, _: &Context, _: Expr, node: &View, ops: &[u32]) -> Result<u32, Error> {
            let v = 100 + self.0.len() as u32;
            let what = match node {
                View::Const(c) => format!("const {c}"),
                View::Bin(op, ..) => format!("{op:?} {ops:?}"),
                other => format!("{other:?}"),
            };
            self.0.push(format!("%{v} = {what}"));
            Ok(v)
        }
    }

    #[test]
    fn lowering_maps_values_and_inputs() {
        let mut cx = Context::new();
        let mut lw = Lowering::new(&mut cx);
        lw.lower_all(&[Bin(2, BinOp::Add, 0, 1), Bin(3, BinOp::Xor, 2, 0)])
            .unwrap();
        let ins: Vec<u32> = lw.inputs().iter().map(|&(v, _)| v).collect();
        assert_eq!(ins, [0, 1]);
        // A value read at another width is the host's error.
        assert!(matches!(lw.value(2, Width::W16), Err(Error::Width(_))));
        // Known bits of an input become its declaration.
        let k = KnownBits::constant(&BitVec::from_u64(Width::W8, 7).unwrap());
        let s = lw.input(9, Width::W8, Some(k)).unwrap();
        assert_eq!(lw.context().declared_known(s).unwrap(), Some(k));
        assert_eq!(lw.owner(s), Some(9));
    }

    #[test]
    fn raising_emits_only_new_nodes_operands_first() {
        let mut cx = Context::new();
        let mut lw = Lowering::new(&mut cx);
        lw.lower_all(&[Bin(2, BinOp::Add, 0, 1), Bin(3, BinOp::Mul, 2, 1)])
            .unwrap();
        let (v2, v0) = (lw.get(2).unwrap(), lw.get(0).unwrap());
        // (v0 + v1) ^ (v0 & 5): the sum is %2 already; the mask and the xor are new.
        let cx = lw.context();
        let five = cx.constant_u64(Width::W8, 5).unwrap();
        let mask = cx.bin(BinOp::And, v0, five).unwrap();
        let e = cx.bin(BinOp::Xor, v2, mask).unwrap();
        let mut rec = Rec(Vec::new());
        let v = lw.raise(e, &mut rec).unwrap();
        assert_eq!(v, 102);
        assert_eq!(
            rec.0,
            [
                "%100 = const 0x5:8",
                "%101 = And [0, 100]",
                "%102 = Xor [2, 101]"
            ]
        );
        // Raised values are owned: raising again emits nothing.
        assert_eq!(lw.raise(e, &mut rec).unwrap(), 102);
        assert_eq!(rec.0.len(), 3);
        // A symbol the lowering did not make stands for no host value.
        let stray = lw.context().symbol("stray", Width::W8).unwrap();
        assert!(lw.raise(stray, &mut rec).is_err());
    }

    #[test]
    fn a_detached_lowering_resumes() {
        let mut cx = Context::new();
        let mut lw = Lowering::new(&mut cx);
        lw.lower(&Bin(2, BinOp::Add, 0, 1)).unwrap();
        let kept = lw.detach();
        // The context on its own in between.
        let one = cx.constant_u64(Width::W8, 1).unwrap();
        let mut lw = kept.attach(&mut cx);
        let v2 = lw.get(2).unwrap();
        let e = lw.context().bin(BinOp::Add, v2, one).unwrap();
        lw.define(3, e).unwrap();
        assert_eq!(lw.inputs().len(), 2);
        assert_eq!(lw.owner(v2), Some(2));
        let mut rec = Rec(Vec::new());
        assert_eq!(lw.raise(e, &mut rec).unwrap(), 3);
        assert!(rec.0.is_empty());
    }

    #[test]
    fn raising_in_steps() {
        let mut cx = Context::new();
        let mut lw = Lowering::new(&mut cx);
        lw.lower(&Bin(2, BinOp::Add, 0, 1)).unwrap();
        let (v2, v0) = (lw.get(2).unwrap(), lw.get(0).unwrap());
        let cx = lw.context();
        let e = cx.bin(BinOp::Mul, v2, v0).unwrap();
        let todo = lw.unraised(e).unwrap();
        assert_eq!(todo, [e]);
        lw.emitted(e, 7).unwrap();
        assert!(lw.unraised(e).unwrap().is_empty());
        assert_eq!(lw.raise(e, &mut Rec(Vec::new())).unwrap(), 7);
        // A stray symbol fails before anything is emitted.
        let stray = lw.context().symbol("stray", Width::W8).unwrap();
        let f = lw.context().bin(BinOp::Sub, e, stray).unwrap();
        assert!(lw.unraised(f).is_err());
    }

    #[test]
    fn templates_agree_with_direct_construction_at_every_width() {
        let smin = Template::new("select(a <s b, a, b)", &["a", "b"]).unwrap();
        let absdiff = Template::new("select(a <u b, b - a, a - b)", &["a", "b"]).unwrap();
        let pick = Template::new("select(c, a + 1, b)", &["c", "a", "b"]).unwrap();
        for bits in [1u16, 7, 8, 32, 64] {
            let w = Width::new(bits).unwrap();
            let mut cx = Context::new();
            let (a, b) = (cx.symbol("a", w).unwrap(), cx.symbol("b", w).unwrap());
            let c = cx.symbol("c", Width::W1).unwrap();
            // Hash-consed: the same node as built directly.
            let got = smin.instantiate(&mut cx, &[a, b]).unwrap();
            let lt = cx.cmp(CmpOp::Slt, a, b).unwrap();
            assert_eq!(got, cx.select(lt, a, b).unwrap());
            // Equal values: the template against its meaning, at points.
            let d = absdiff.instantiate(&mut cx, &[a, b]).unwrap();
            let p = pick.instantiate(&mut cx, &[c, a, b]).unwrap();
            assert_eq!(cx.width(p).unwrap(), w);
            for k in 0..64u64 {
                let x = BitVec::wrapping_from_u64(w, k.wrapping_mul(0x9e37_79b9_7f4a_7c15));
                let y = BitVec::wrapping_from_u64(w, k.wrapping_mul(3));
                let cond = k % 2 == 0;
                let env = FnEnv(|key: &SymbolKey, _| match key.to_string().as_str() {
                    "a" => Some(x),
                    "b" => Some(y),
                    _ => Some(BitVec::from_bool(cond)),
                });
                let v = cx.eval(&[d, p], &env).unwrap();
                let (xs, ys) = (x.to_u64().unwrap(), y.to_u64().unwrap());
                let mask = u64::MAX >> (64 - bits);
                assert_eq!(
                    v[0].to_u64(),
                    Some(xs.abs_diff(ys)),
                    "absdiff at {bits} bits"
                );
                let want = if cond { xs.wrapping_add(1) & mask } else { ys };
                assert_eq!(v[1].to_u64(), Some(want), "pick at {bits} bits");
            }
        }
        assert_eq!(
            smin.compiled.lock().unwrap().len(),
            5,
            "compiled once per width"
        );
        // Arity, parameter, syntax and width errors.
        let mut cx = Context::new();
        let a = cx.symbol("a", Width::W8).unwrap();
        assert!(smin.instantiate(&mut cx, &[a]).is_err());
        assert!(Template::new("a + a", &["a", "a"]).is_err());
        let broken = Template::new("a +", &["a"]).unwrap();
        assert!(broken.check(&[Width::W8]).is_err());
        assert!(pick.check(&[Width::W8, Width::W8, Width::W8]).is_err());
        assert!(pick.check(&[Width::W1, Width::W8, Width::W8]).is_ok());
        fn shared<T: Send + Sync>() {}
        shared::<Template>();
    }
}

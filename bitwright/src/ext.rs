//! Extension operations: host-defined, total, multi-output operators.
//!
//! A host whose instruction set has operations bitwright does not model as a composition of its
//! own (a flags bundle, a funnel shift, a vendor-specific count) registers them as [`ExtOp`]s.
//! An extension call takes one to three arguments and has one to eight outputs; each output is a
//! node of its own, hash-consed by the operation, the output and the arguments, so its value is a
//! function of its arguments like any other node. Evaluation, facts, sampled verification and
//! SMT-LIB export go through the operation's own methods; to the rules and the passes an
//! extension node is an opaque atom (its arguments are still simplified, unless the operation
//! asks otherwise).
//!
//! Operations are collected into an immutable [`Registry`] before a context uses it
//! ([`Context::with_registry`](crate::Context::with_registry)). Registering one runs a contract
//! self-test: declared widths, determinism, known-bits soundness against `eval`,
//! `expand ≡ eval`, and invertibility declarations against `invert`, at a battery of widths.
//!
//! An output that is injective or bijective in one argument (the others fixed) can say so
//! ([`ExtOp::invertible`], [`ExtOp::invert`]): the simplifier then cancels the call on both
//! sides of an equality and solves it at a constant, and [`Query::Injective`] sees through it.
//!
//! [`Query::Injective`]: crate::Query::Injective
//!
//! An operation that must not be merged with another call on the same arguments (an
//! occurrence), takes a fresh symbol as one of its arguments.
//!
//! ```
//! use std::sync::Arc;
//! use bitwright::ext::{ExtOp, ExtSig, Registry};
//! use bitwright::{BitVec, BinOp, Context, ContextConfig, Width};
//!
//! /// Unsigned average rounding down, without overflow.
//! struct AvgU;
//! impl ExtOp for AvgU {
//!     fn name(&self) -> &str { "acme.avgu" }
//!     fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
//!         match args {
//!             [a, b] if a == b => Ok(ExtSig::new(&[("avg", *a)])),
//!             _ => Err("two operands of one width".into()),
//!         }
//!     }
//!     fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
//!         let (a, b) = (&args[0], &args[1]);
//!         let both = BitVec::apply_bin(BinOp::And, a, b).unwrap();
//!         let either = BitVec::apply_bin(BinOp::Xor, a, b).unwrap();
//!         let one = BitVec::one(a.width());
//!         let half = BitVec::apply_bin(BinOp::LShr, &either, &one).unwrap();
//!         out[0] = BitVec::apply_bin(BinOp::Add, &both, &half).unwrap();
//!     }
//! }
//!
//! let registry = Arc::new(Registry::builder().register(AvgU)?.build());
//! let mut cx = Context::with_registry(ContextConfig::default(), registry.clone());
//! let avg = registry.id("acme.avgu").unwrap();
//! let x = cx.symbol("x", Width::W8)?;
//! let c = cx.constant_u64(Width::W8, 200)?;
//! let d = cx.constant_u64(Width::W8, 100)?;
//! let folded = cx.ext(avg, &[c, d])?;
//! assert_eq!(cx.as_const(folded[0])?.and_then(|v| v.to_u64()), Some(150));
//! let open = cx.ext(avg, &[x, d])?;
//! assert_eq!(cx.display(open[0]).to_string(), "@acme.avgu(x, 100:8)");
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

use core::fmt;
use std::borrow::Cow;
use std::collections::HashMap;
use std::sync::Arc;

use crate::error::Error;
use crate::expr::{Context, Expr};
use crate::facts::KnownBits;
use crate::hash::combine;
use crate::{BitVec, Width};

/// The most arguments an extension call takes.
pub const MAX_ARGS: usize = 3;
/// The most outputs an extension operation has.
pub const MAX_OUTPUTS: usize = 8;
/// The most operations a registry holds.
pub const MAX_OPS: usize = 256;

/// The outputs of an extension operation at some argument widths: a role name and a width each.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExtSig {
    outputs: Vec<(Cow<'static, str>, Width)>,
}

impl ExtSig {
    /// Outputs by role name and width, in order (1 to 8 of them).
    pub fn new(outputs: &[(&'static str, Width)]) -> ExtSig {
        ExtSig {
            outputs: outputs
                .iter()
                .map(|&(r, w)| (Cow::Borrowed(r), w))
                .collect(),
        }
    }

    /// The outputs: role name and width.
    pub fn outputs(&self) -> impl Iterator<Item = (&str, Width)> {
        self.outputs.iter().map(|(r, w)| (&**r, *w))
    }

    /// The number of outputs.
    pub fn len(&self) -> usize {
        self.outputs.len()
    }

    /// Whether there are no outputs (never valid).
    pub fn is_empty(&self) -> bool {
        self.outputs.is_empty()
    }

    /// The width of output `k`.
    pub fn width(&self, k: usize) -> Option<Width> {
        self.outputs.get(k).map(|(_, w)| *w)
    }
}

/// Properties of an extension operation the builder and simplifier may use.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct ExtTraits {
    /// The first two arguments may be swapped (they are put in canonical order).
    pub commutative: bool,
    /// The simplifier leaves the arguments as they are (the call is an atom, arguments
    /// included).
    pub opaque: bool,
}

setters!(ExtTraits {
    with_commutative: commutative: bool,
    with_opaque: opaque: bool,
});

/// How an output of an extension operation depends on one argument when the others are fixed
/// (see [`ExtOp::invertible`]).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Invertible {
    /// Nothing is claimed.
    #[default]
    No,
    /// Distinct values of the argument give distinct values of the output.
    Injective,
    /// Injective, and every value of the output is reached (the output and the argument have
    /// one width).
    Bijective,
}

/// An argument of an inverse call (see [`ExtOp::inverse`]).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum InverseArg {
    /// The output being undone.
    Output,
    /// The undone call's own argument at this position (a key, say).
    Arg(u8),
}

/// The operation that undoes an output of another in one argument (see [`ExtOp::inverse`]).
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct ExtInverse {
    /// The operation's name, in the same registry.
    pub op: Cow<'static, str>,
    /// Its output that gives the argument back.
    pub output: u8,
    /// Its arguments, in order.
    pub args: Vec<InverseArg>,
}

impl ExtInverse {
    /// Output `output` of `op` over `args` gives the argument back.
    pub fn new(op: &'static str, output: u8, args: &[InverseArg]) -> ExtInverse {
        ExtInverse {
            op: Cow::Borrowed(op),
            output,
            args: args.to_vec(),
        }
    }
}

/// A host-defined operation. Every method must be deterministic; `eval` must be total.
pub trait ExtOp: Send + Sync + 'static {
    /// A namespaced name: `acme.avgu`. Letters, digits, `_` and `.`, starting with a letter.
    fn name(&self) -> &str;

    /// Bumped whenever `eval` changes; it enters every structural hash and cache key.
    fn revision(&self) -> u32 {
        1
    }

    /// The outputs at these argument widths (1 to 3 arguments), or why they are not accepted.
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String>;

    /// The outputs for these arguments. `out` holds one value per output, of the declared
    /// widths (zero); write every one.
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]);

    /// Known bits of the outputs from known bits of the arguments. `out` starts unknown; leave an
    /// output unknown when nothing is known. Must be sound: every value `eval` gives for
    /// arguments inside `args` must be inside `out`.
    fn known_bits(&self, _args: &[KnownBits], _out: &mut [KnownBits]) {}

    /// The outputs built from bitwright's own operators, if the operation has such a definition
    /// (it must agree with `eval`).
    fn expand(&self, _cx: &mut Context, _args: &[Expr]) -> Option<Result<Vec<Expr>, Error>> {
        None
    }

    /// An SMT-LIB term for output `output`, given the argument terms and widths; `None` exports
    /// it as an uninterpreted function.
    fn smtlib(&self, _output: u8, _args: &[&str], _widths: &[Width]) -> Option<String> {
        None
    }

    /// Properties the builder and simplifier may use.
    fn traits(&self) -> ExtTraits {
        ExtTraits::default()
    }

    /// Whether output `output` is an injective (or bijective) function of argument `arg` when
    /// every other argument is fixed at any value inside its known bits in `args` (`args[arg]`
    /// is always unknown). A declaration lets the simplifier cancel the call on both sides of
    /// `==` and `!=` (`op(k, x) == op(k, y)` becomes `x == y`) and solve it at a constant
    /// through [`invert`](Self::invert); it must hold for *every* such value. The self-test
    /// checks it against `invert` and `eval` at sampled points.
    fn invertible(&self, _output: u8, _arg: u8, _args: &[KnownBits]) -> Invertible {
        Invertible::No
    }

    /// For an output declared [`invertible`](Self::invertible) in `arg`: the value of argument
    /// `arg` at which output `output` equals `value`, the other arguments as in `args` (whose
    /// entry `arg` is to be ignored), or `None` if there is none (never for a bijection).
    /// Answers are checked by evaluation before they are used.
    fn invert(&self, _output: u8, _arg: u8, _args: &[BitVec], _value: &BitVec) -> Option<BitVec> {
        None
    }

    /// Another operation of the registry that undoes output `output` in argument `arg`: for
    /// every argument values, that operation's output [`ExtInverse::output`] over
    /// [`ExtInverse::args`] (this call's output, or its other arguments) is `args[arg]`. A
    /// decryption for an encryption under one key, say. The builder then cancels the round
    /// trip: that call over this call's output is `args[arg]` itself (`dec(k, enc(k, x))` is
    /// `x`). The registry checks the declaration by sampled evaluation once both operations
    /// are registered; one whose other operation never is, is unused.
    fn inverse(&self, _output: u8, _arg: u8) -> Option<ExtInverse> {
        None
    }
}

/// The arguments of an extension call (1 to 3).
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct ExtArgs {
    args: [Expr; MAX_ARGS],
    len: u8,
}

impl ExtArgs {
    /// `args` must hold 1 to 3 handles.
    pub(crate) fn new(args: &[Expr]) -> ExtArgs {
        let mut a = [args[0]; MAX_ARGS];
        a[..args.len()].copy_from_slice(args);
        ExtArgs {
            args: a,
            len: args.len() as u8,
        }
    }

    /// The arguments in order.
    pub fn as_slice(&self) -> &[Expr] {
        &self.args[..usize::from(self.len)]
    }
}

/// An operation in a [`Registry`]: its position, and a tag of its name and revision, so an id
/// used with a registry that has another operation at that position is refused.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ExtId {
    index: u8,
    tag: u32,
}

impl ExtId {
    /// The position of the operation in its registry.
    pub fn index(self) -> usize {
        usize::from(self.index)
    }

    pub(crate) fn raw(self) -> u8 {
        self.index
    }

    /// An id no registry has (for a node whose registry is gone; never built by the builder).
    pub(crate) fn dangling() -> ExtId {
        ExtId {
            index: u8::MAX,
            tag: 0,
        }
    }
}

/// Why an operation was refused by [`RegistryBuilder::register`].
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExtError {
    /// The name is empty or not of the allowed form.
    BadName(String),
    /// Another operation has the name.
    Duplicate(String),
    /// The registry is full.
    TooMany,
    /// The self-test found the operation breaking its contract (the operation, the reason).
    Contract(String, String),
}

impl fmt::Display for ExtError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExtError::BadName(n) => write!(f, "`{n}` is not a valid extension operation name"),
            ExtError::Duplicate(n) => write!(f, "`{n}` is already registered"),
            ExtError::TooMany => write!(f, "a registry holds at most {MAX_OPS} operations"),
            ExtError::Contract(n, why) => write!(f, "`{n}` breaks its contract: {why}"),
        }
    }
}

impl std::error::Error for ExtError {}

/// An immutable set of extension operations.
#[derive(Clone, Default)]
pub struct Registry {
    ops: Vec<Arc<dyn ExtOp>>,
    by_name: HashMap<String, ExtId>,
    /// Per operation: a hash of its name and revision (enters structural hashes).
    hashes: Vec<u64>,
    /// Declared and checked round trips, by the undoing operation's position.
    round_trips: HashMap<u8, Vec<RoundTrip>>,
    /// Declarations waiting for their undoing operation: (declaring position, output, argument,
    /// declaration, whether to check it).
    pending: Vec<(u8, u8, u8, ExtInverse, bool)>,
}

/// A checked round trip: output `g_output` of operation `g` over `args` undoes output
/// `f_output` of operation `f` in argument `f_arg`.
#[derive(Clone, Debug)]
pub(crate) struct RoundTrip {
    pub(crate) f: u8,
    pub(crate) f_output: u8,
    pub(crate) f_arg: u8,
    pub(crate) g_output: u8,
    pub(crate) args: Vec<InverseArg>,
}

impl fmt::Debug for Registry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(
                self.ops
                    .iter()
                    .map(|o| format!("{}#{}", o.name(), o.revision())),
            )
            .finish()
    }
}

impl Registry {
    /// A builder.
    pub fn builder() -> RegistryBuilder {
        RegistryBuilder::default()
    }

    /// The operation named `name`.
    pub fn id(&self, name: &str) -> Option<ExtId> {
        self.by_name.get(name).copied()
    }

    /// The operation `id`, if this registry has it (at that position, by name and revision).
    pub fn op(&self, id: ExtId) -> Option<&dyn ExtOp> {
        (self.id_at(id.index)? == id).then(|| self.ops.get(id.index()).map(|o| &**o))?
    }

    /// The id of the operation at position `index`.
    pub(crate) fn id_at(&self, index: u8) -> Option<ExtId> {
        let h = *self.hashes.get(usize::from(index))?;
        Some(ExtId {
            index,
            tag: h as u32,
        })
    }

    /// The operation at position `index` (for nodes, which store only the position).
    pub(crate) fn op_at(&self, index: u8) -> Option<&dyn ExtOp> {
        self.ops.get(usize::from(index)).map(|o| &**o)
    }

    /// The number of operations.
    pub fn len(&self) -> usize {
        self.ops.len()
    }

    /// Whether there are none.
    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }

    /// Every operation, in registration order.
    pub fn ids(&self) -> impl Iterator<Item = ExtId> + '_ {
        (0..self.ops.len()).filter_map(|i| self.id_at(i as u8))
    }

    /// The hash of the operation at position `index` (its name and revision).
    pub(crate) fn hash_at(&self, index: u8) -> u64 {
        self.hashes.get(usize::from(index)).copied().unwrap_or(0)
    }

    /// The round trips output `g_output` of the operation at position `g` undoes.
    pub(crate) fn round_trips(&self, g: u8) -> &[RoundTrip] {
        self.round_trips.get(&g).map_or(&[], Vec::as_slice)
    }

    /// Resolves the declarations of the operation at `f` and those waiting for it.
    fn resolve(&mut self, f: u8, check: bool) -> Result<(), ExtError> {
        let op = self.ops[usize::from(f)].clone();
        for output in 0..MAX_OUTPUTS as u8 {
            for arg in 0..MAX_ARGS as u8 {
                if let Some(inv) = op.inverse(output, arg) {
                    self.pending.push((f, output, arg, inv, check));
                }
            }
        }
        let pending = core::mem::take(&mut self.pending);
        for (f, output, arg, inv, check) in pending {
            let Some(g) = self.by_name.get(&*inv.op).map(|id| id.index) else {
                self.pending.push((f, output, arg, inv, check));
                continue;
            };
            let (fop, gop) = (
                self.ops[usize::from(f)].clone(),
                self.ops[usize::from(g)].clone(),
            );
            if check {
                check_round_trip(&*fop, output, arg, &*gop, &inv)
                    .map_err(|why| ExtError::Contract(fop.name().to_string(), why))?;
            }
            self.round_trips.entry(g).or_default().push(RoundTrip {
                f,
                f_output: output,
                f_arg: arg,
                g_output: inv.output,
                args: inv.args,
            });
        }
        Ok(())
    }
}

/// Checks a declared round trip by sampled evaluation at the argument widths the declaring
/// operation accepts.
fn check_round_trip(
    f: &dyn ExtOp,
    output: u8,
    arg: u8,
    g: &dyn ExtOp,
    inv: &ExtInverse,
) -> Result<(), String> {
    let mut rng = Rng(0x7e7e ^ u64::from(f.revision()));
    let mut tested = 0;
    for tuple in width_tuples() {
        if tested >= TESTED_TUPLES {
            break;
        }
        let widths: Vec<Width> = tuple
            .iter()
            .map(|&w| Width::new(w).map_err(|e| e.to_string()))
            .collect::<Result<_, _>>()?;
        let Ok(sig) = f.signature(&widths) else {
            continue;
        };
        if usize::from(output) >= sig.len() || usize::from(arg) >= widths.len() {
            continue;
        }
        let at = || format!(" (inverse `{}`) at argument widths {tuple:?}", inv.op);
        let gw: Vec<Width> = inv
            .args
            .iter()
            .map(|a| match *a {
                InverseArg::Output => sig.width(usize::from(output)),
                InverseArg::Arg(i) => widths.get(usize::from(i)).copied(),
            })
            .collect::<Option<_>>()
            .ok_or_else(|| format!("an inverse argument out of range{}", at()))?;
        let gsig = g
            .signature(&gw)
            .map_err(|e| format!("the inverse refuses its arguments: {e}{}", at()))?;
        if gsig.width(usize::from(inv.output)) != Some(widths[usize::from(arg)]) {
            return Err(format!("the inverse's output has another width{}", at()));
        }
        tested += 1;
        for _ in 0..16 {
            let args: Vec<BitVec> = widths.iter().map(|&w| rng.value(w)).collect();
            let out = run_eval(f, &args)?;
            let gargs: Vec<BitVec> = inv
                .args
                .iter()
                .map(|a| match *a {
                    InverseArg::Output => out[usize::from(output)],
                    InverseArg::Arg(i) => args[usize::from(i)],
                })
                .collect();
            let back = run_eval(g, &gargs)?;
            if back[usize::from(inv.output)] != args[usize::from(arg)] {
                return Err(format!(
                    "the inverse gives {} for argument {}{}",
                    back[usize::from(inv.output)],
                    args[usize::from(arg)],
                    at()
                ));
            }
        }
    }
    if tested == 0 {
        return Err(format!(
            "no argument widths to check the inverse `{}` at",
            inv.op
        ));
    }
    Ok(())
}

/// Collects operations into a [`Registry`].
#[derive(Default, Debug)]
pub struct RegistryBuilder {
    reg: Registry,
}

impl RegistryBuilder {
    /// Adds `op` after its contract self-test (and the check of each round trip it declares,
    /// or completes, with [`ExtOp::inverse`]).
    pub fn register(self, op: impl ExtOp) -> Result<Self, ExtError> {
        check(&op)?;
        self.add(op, true)
    }

    /// Adds `op` without its contract self-test (names are still checked). For a host that
    /// registers the same operations in many registries, and runs [`check`] on each of them once,
    /// in its own tests: the self-test samples hundreds of evaluations, too many to repeat per
    /// registry. A broken operation registered this way makes facts and folds wrong.
    pub fn register_unchecked(self, op: impl ExtOp) -> Result<Self, ExtError> {
        self.add(op, false)
    }

    fn add(mut self, op: impl ExtOp, check: bool) -> Result<Self, ExtError> {
        let name = op.name().to_string();
        let good = name.chars().next().is_some_and(|c| c.is_ascii_alphabetic())
            && name
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.')
            && !name.ends_with('.')
            && !name.contains("..");
        if !good {
            return Err(ExtError::BadName(name));
        }
        if self.reg.by_name.contains_key(&name) {
            return Err(ExtError::Duplicate(name));
        }
        if self.reg.ops.len() >= MAX_OPS {
            return Err(ExtError::TooMany);
        }
        let index = self.reg.ops.len() as u8;
        let h = name
            .bytes()
            .fold(combine(0x6578_7400, u64::from(op.revision())), |h, b| {
                combine(h, u64::from(b))
            });
        self.reg.hashes.push(h);
        let id = ExtId {
            index,
            tag: h as u32,
        };
        self.reg.by_name.insert(name, id);
        self.reg.ops.push(Arc::new(op));
        self.reg.resolve(index, check)?;
        Ok(self)
    }

    /// The registry.
    pub fn build(self) -> Registry {
        self.reg
    }
}

/// The contract self-test [`RegistryBuilder::register`] runs (see the module docs): `Ok` if the
/// sampled checks found no breach. For hosts that register with
/// [`register_unchecked`](RegistryBuilder::register_unchecked) and test their operations once.
pub fn check(op: &dyn ExtOp) -> Result<(), ExtError> {
    self_test(op).map_err(|why| ExtError::Contract(op.name().to_string(), why))
}

/// Checks the declared outputs, and runs `eval` for them, validating widths.
pub(crate) fn run_eval(op: &dyn ExtOp, args: &[BitVec]) -> Result<Vec<BitVec>, String> {
    let widths: Vec<Width> = args.iter().map(|a| a.width()).collect();
    let sig = op.signature(&widths)?;
    if sig.is_empty() || sig.len() > MAX_OUTPUTS {
        return Err(format!(
            "{} outputs declared (1 to {MAX_OUTPUTS})",
            sig.len()
        ));
    }
    let mut out: Vec<BitVec> = sig.outputs().map(|(_, w)| BitVec::zero(w)).collect();
    op.eval(args, &mut out);
    for (k, (v, (_, w))) in out.iter().zip(sig.outputs()).enumerate() {
        if v.width() != w {
            return Err(format!(
                "output {k} has {} bits, declared {}",
                v.width().bits(),
                w.bits()
            ));
        }
    }
    Ok(out)
}

/// Runs `known_bits`, validating widths and consistency.
pub(crate) fn run_known_bits(
    op: &dyn ExtOp,
    sig: &ExtSig,
    args: &[KnownBits],
) -> Result<Vec<KnownBits>, String> {
    let mut out: Vec<KnownBits> = sig.outputs().map(|(_, w)| KnownBits::unknown(w)).collect();
    op.known_bits(args, &mut out);
    for (k, (v, (_, w))) in out.iter().zip(sig.outputs()).enumerate() {
        if v.width() != w {
            return Err(format!(
                "known bits of output {k} have {} bits, declared {}",
                v.width().bits(),
                w.bits()
            ));
        }
    }
    Ok(out)
}

/// A small deterministic generator for the self-test.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn value(&mut self, w: Width) -> BitVec {
        let limbs: Vec<u64> = (0..8)
            .map(|_| match self.next() % 5 {
                0 => 0,
                1 => u64::MAX,
                _ => self.next(),
            })
            .collect();
        BitVec::wrapping_from_limbs(w, &limbs)
    }
}

/// Argument widths the self-test tries: for one argument every width of the battery, for two
/// every pair, for three every triple with at least two equal (a value, a count, a carry...).
fn width_tuples() -> Vec<Vec<u16>> {
    const W: [u16; 11] = [1, 3, 8, 13, 16, 32, 64, 65, 128, 256, 512];
    let mut out: Vec<Vec<u16>> = W.iter().map(|&a| vec![a]).collect();
    for &a in &W {
        for &b in &W {
            out.push(vec![a, b]);
        }
    }
    for &a in &W {
        for &b in &W {
            for t in [vec![a, a, b], vec![a, b, a], vec![b, a, a]] {
                if !out.contains(&t) {
                    out.push(t);
                }
            }
        }
    }
    out
}

/// Checks the invertibility declarations at one sample: for every output and argument
/// declared invertible under the known bits `kb` of the other arguments, `invert` recovers the
/// argument from the output (at a completion of `kb` with the argument random), and for a
/// bijection also finds an argument for a random output value.
fn check_invertible(
    op: &dyn ExtOp,
    sig: &ExtSig,
    widths: &[Width],
    args: &[BitVec],
    kb: &[KnownBits],
    rng: &mut Rng,
) -> Result<(), String> {
    use crate::facts::known::{bv_and, bv_not, bv_or};
    for k in 0..sig.len() {
        for a in 0..widths.len() {
            let mut fixed = kb.to_vec();
            fixed[a] = KnownBits::unknown(widths[a]);
            let decl = op.invertible(k as u8, a as u8, &fixed);
            if decl == Invertible::No {
                continue;
            }
            if decl == Invertible::Bijective && sig.width(k) != Some(widths[a]) {
                return Err(format!(
                    "declared bijective in argument {a}, but output {k} has another width"
                ));
            }
            // A completion of the fixed arguments' known bits; the argument itself random.
            let inst: Vec<BitVec> = args
                .iter()
                .zip(&fixed)
                .map(|(v, f)| {
                    let r = rng.value(v.width());
                    bv_or(&bv_and(v, &f.known()), &bv_and(&r, &bv_not(&f.known())))
                })
                .collect();
            let y = run_eval(op, &inst)?[k];
            if op.invert(k as u8, a as u8, &inst, &y).as_ref() != Some(&inst[a]) {
                return Err(format!(
                    "declared invertible, but invert does not recover argument {a} from output \
                     {k}"
                ));
            }
            if decl == Invertible::Bijective {
                let target = rng.value(widths[a]);
                let found = op.invert(k as u8, a as u8, &inst, &target);
                let mut hit = inst.clone();
                match found {
                    Some(v) if v.width() == widths[a] => hit[a] = v,
                    _ => {
                        return Err(format!(
                            "declared bijective, but invert finds no argument {a} for a value \
                             of output {k}"
                        ));
                    }
                }
                if run_eval(op, &hit)?[k] != target {
                    return Err(format!(
                        "invert's argument {a} does not give the value asked of output {k}"
                    ));
                }
            }
        }
    }
    Ok(())
}

/// The most argument-width tuples the self-test exercises (the first accepted, in the order of
/// [`width_tuples`], which starts from single and equal widths).
const TESTED_TUPLES: usize = 64;

/// The contract self-test (see the module docs): at every argument-width tuple the signature
/// accepts (up to [`TESTED_TUPLES`] of them), declared output widths, determinism, known-bits
/// soundness against `eval`, a commutative operation's symmetry, invertibility declarations
/// against `invert`, and `expand ≡ eval`.
fn self_test(op: &dyn ExtOp) -> Result<(), String> {
    use crate::facts::known::{bv_and, bv_not};
    let mut rng = Rng(0x5e1f_7e57 ^ u64::from(op.revision()));
    let commutative = op.traits().commutative;
    let mut accepted = 0;
    for tuple in width_tuples() {
        if accepted >= TESTED_TUPLES {
            break;
        }
        let widths: Vec<Width> = tuple
            .iter()
            .map(|&w| Width::new(w).map_err(|e| e.to_string()))
            .collect::<Result<_, _>>()?;
        let Ok(sig) = op.signature(&widths) else {
            continue;
        };
        if sig.is_empty() || sig.len() > MAX_OUTPUTS {
            return Err(format!(
                "{} outputs declared (1 to {MAX_OUTPUTS})",
                sig.len()
            ));
        }
        accepted += 1;
        let at = || format!(" at argument widths {tuple:?}");
        for _ in 0..16 {
            let args: Vec<BitVec> = widths.iter().map(|&w| rng.value(w)).collect();
            let a = run_eval(op, &args).map_err(|e| e + &at())?;
            if run_eval(op, &args)? != a {
                return Err(format!("eval is not deterministic{}", at()));
            }
            if commutative && widths.len() >= 2 && widths[0] == widths[1] {
                let mut swapped = args.clone();
                swapped.swap(0, 1);
                if run_eval(op, &swapped)? != a {
                    return Err(format!(
                        "declared commutative, but swapping the first two arguments changes \
                         the result{}",
                        at()
                    ));
                }
            }
            // Known bits: random partial knowledge of the arguments, checked on random
            // completions.
            let masks: Vec<BitVec> = widths.iter().map(|&w| rng.value(w)).collect();
            let kb: Vec<KnownBits> = args
                .iter()
                .zip(&masks)
                .map(|(v, m)| {
                    KnownBits::new(bv_and(&bv_not(v), m), bv_and(v, m))
                        .unwrap_or(KnownBits::unknown(v.width()))
                })
                .collect();
            let out = run_known_bits(op, &sig, &kb).map_err(|e| e + &at())?;
            for _ in 0..4 {
                let inst: Vec<BitVec> = args
                    .iter()
                    .zip(&masks)
                    .map(|(v, m)| {
                        let r = rng.value(v.width());
                        crate::facts::known::bv_or(&bv_and(v, m), &bv_and(&r, &bv_not(m)))
                    })
                    .collect();
                for (k, (v, o)) in run_eval(op, &inst)?.iter().zip(&out).enumerate() {
                    if !o.contains(v) {
                        return Err(format!("known bits of output {k} exclude {v}{}", at()));
                    }
                }
            }
            check_invertible(op, &sig, &widths, &args, &kb, &mut rng).map_err(|e| e + &at())?;
        }
        // expand ≡ eval.
        let mut cx = Context::new();
        let syms: Vec<Expr> = widths
            .iter()
            .enumerate()
            .map(|(i, &w)| cx.symbol(format!("a{i}").as_str(), w))
            .collect::<Result<_, _>>()
            .map_err(|e| e.to_string())?;
        if let Some(ex) = op.expand(&mut cx, &syms) {
            let ex = ex.map_err(|e| format!("expand failed: {e}{}", at()))?;
            if ex.len() != sig.len() {
                return Err(format!(
                    "expand gave {} outputs, not {}{}",
                    ex.len(),
                    sig.len(),
                    at()
                ));
            }
            for _ in 0..8 {
                let args: Vec<BitVec> = widths.iter().map(|&w| rng.value(w)).collect();
                let env: Vec<(crate::SymbolKey, BitVec)> = args
                    .iter()
                    .enumerate()
                    .map(|(i, v)| (crate::SymbolKey::from(format!("a{i}").as_str()), *v))
                    .collect();
                let got = cx.eval(&ex, &env[..]).map_err(|e| e.to_string())?;
                if got != run_eval(op, &args)? {
                    return Err(format!("expand disagrees with eval{}", at()));
                }
            }
        }
    }
    if accepted == 0 {
        return Err("no signature accepted at any tested argument widths".into());
    }
    Ok(())
}

# bitwright design

Status: **accepted design, pre-implementation** (v0 of this document). It is the reference for
milestones M0–M8 in §13. Where the code and this document disagree once implementation starts, the
code and its tests win and this document is corrected.

bitwright is a Rust library for **fixed-width bit-vector expressions**. It provides:

- an exact bit-vector value type, 1..=512 bits;
- a hash-consed, context-owned expression arena with construction-time canonicalization;
- bit-level facts (known bits, unsigned and signed ranges) and tri-state proofs;
- a directed simplifier built from normal-form passes plus a small rule corpus;
- a rule language (`.bwr`) with a mandatory, machine-checked soundness gate;
- optional services, off by default: MBA (mixed boolean-arithmetic) simplification with pluggable
  solvers, and a bounded equality-saturation search.

The intended users are binary-analysis tools, deobfuscators, decompilers, lifters, and anyone who needs
to simplify or reason about machine-integer expressions with predictable cost.

---

## 1. Principles and key decisions

**Principles.** These are part of the contract, not aspirations.

1. **Sound or silent.** A transformation either preserves the value of every root at every input, or it
   does not happen. Unsupported input stays unsupported. A decline is never replaced by an
   approximation.
2. **No hidden state.** There are no process globals, no thread-locals that affect results, and no
   environment variables. Every knob is a typed configuration field. All mutable state lives in a
   `Context`, an `Engine`, an `Allowance`, or a caller-supplied backend.
3. **Deterministic.** The same inputs and configuration give bit-identical output. The only wall-clock
   input is an optional, caller-injected deadline, and a deadline can only *stop* work. It never
   changes what a completed result is.
4. **Bounded and accountable.** Every loop is bounded by a caller-visible budget. Exhausting a budget is
   an *outcome*, reported per root, never an error and never a panic. Work spent is never refunded.
5. **Termination by construction.** The rewrite system terminates because every directed rule
   strictly decreases a well-founded measure, which the rule compiler checks. Budgets bound latency,
   not correctness or termination.
6. **Few rules, strong passes.** Algebra that can be decided by a normal form (linear forms, truth
   tables, comparison lattices) is decided by a normal form, not approximated by thousands of rules.
7. **No panics on data.** Every constructor, decoder and query returns `Result` or `Option`. The crates
   are `#![forbid(unsafe_code)]`.

**Key decisions.**

| # | Decision | Alternatives considered | Why |
|-|-|-|-|
| D1 | **Total, SMT-LIB QF_BV semantics** for every operator, including division and remainder | partial division with a "may be invalid" flag per node | Every rule becomes a closed QF_BV validity that an enumerator, an SMT solver or Lean `BitVec` can check without side conditions. "Equal handle ⇒ equal value" holds unconditionally. The definedness-erasure class of bugs cannot be written. Hosts that need fault semantics build explicit trap guards (§3.4), which they can simplify and often prove false. |
| D2 | **Directed core**; equality saturation is an opt-in boundary service | an e-graph core | Workloads are large shared DAGs under tight per-call latency. Measured prototypes found saturation's wins narrow and its cost dominated by unproductive search; normal forms carry the deobfuscation workload (§10). |
| D3 | **Context-independent canonical form**: commutative operands ordered by a structural key, constants on the right | order by creation index | The same expression built in any order, in any context, has the same shape and prints the same text; cache keys derived from structure are portable. |
| D4 | **Exact up to 512 bits, a native fast path at ≤128** | cap at 128 | 256- and 512-bit vector lanes are real inputs, and 128-bit multiply-high needs a 256-bit intermediate anyway. Narrow nodes never pay for wide storage (§4.2). |
| D5 | **Termination by a Knuth–Bendix-style order**, checked by the rule compiler | recursion caps, re-entry counters | A capped system produces output that depends on where a counter saturated. |
| D6 | **One text syntax** for the expression parser, the printer, rule patterns and templates, diagnostics and counterexamples | separate rule syntax | Users read rules the way they read printed output; `parse(print(e)) == e` is a tested property. |
| D7 | **Identities and rewrites are distinct declarations** (`identity … <=>` vs `rule … =>`) | inferring equations from guard-free rules | The equality-saturation service must admit only unconditional equations; the distinction must be explicit and machine-checked. |
| D8 | **Own e-graph**, in-crate | `egg`, `egglog` | Budgets must be charged inside insertion, matching and rebuild against a caller-owned allowance; no wall clock; deterministic iteration; no global symbol table; MSRV under our control. |

---

## 2. Workspace, features, dependencies

```text
bitwright/                       workspace; edition 2024; rust-version 1.88; PolyForm-Noncommercial-1.0.0
├─ bitwright/                    the library (published)
│  ├─ src/value/                 Width, BitVec, u64/u128/wide kernels
│  ├─ src/ops.rs                 operator kinds, typing, semantics metadata
│  ├─ src/expr/                  Context, Expr, Node, builder, canonicalizer, OrderKey, views, maps
│  ├─ src/facts/                 KnownBits, URange, SRange, transfers, proofs, assumptions
│  ├─ src/eval.rs                iterative evaluator, substitute
│  ├─ src/ext/                   ExtOp trait, Registry, contract self-test
│  ├─ src/text/                  lexer, expression parser, bounded DAG printer, diagnostics
│  ├─ src/rules/                 RuleIr, compiler, termination order, reference matcher, corpus/ (*.bwr, *.bwr.proof)
│  ├─ src/check/                 soundness checker, evidence, ledger (feature "check")
│  ├─ src/engine/                Engine, Strategy/Phase, Run/Outcome, budgets, dispatch net, memo, stats
│  ├─ src/passes/                linear, xor, bitwise, compares, casts, demanded, linear_mba, shuffle, fact_fold
│  ├─ src/mba/                   classifier, MbaExpr, lower/lift, gate, traits (feature "mba"); cobra.rs ("cobra")
│  └─ src/eqsat/                 e-graph, admission, schedule, extraction (feature "eqsat")
├─ bitwright-ref/                independent bit-serial reference evaluator (publish = false)
├─ bitwright-cli/                `bitwright check | lint | smt | catalog | explain | simplify` (published after 0.1)
├─ fuzz/                         cargo-fuzz targets (publish = false)
└─ xtask/                        regenerate corpus tables, verify ledgers, release checks (publish = false)
```

`bitwright-ref` shares **no code** with the library's kernels. It evaluates its own tiny term type
bit by bit, transcribed from the SMT-LIB definitions. Tests convert bitwright expressions and rule
instances into it. The kernels are checked against it (exhaustively at every width ≤ 8, where the
rule checker's exhaustive tier lives, and by boundary sampling to 512), and the rule checker evaluates
with those kernels, so a kernel bug cannot hide a rule bug in the region the checker proves.

**Features of `bitwright`** (additive; none changes the result of a computation that does not use it).
The rule compiler is not optional: the built-in corpus is compiled from embedded source (§7.3).
Features other than `check` arrive with their milestones.

| Feature | Default | Adds |
|-|-|-|
| `check` | yes | `bitwright::check`: the rule soundness checker, evidence and ledgers |
| `smtlib` | no | SMT-LIB export of expressions and rule obligations; import of a QF_BV subset |
| `mba` | no | `MbaExpr`, lowering/lifting, the evidence gate, solver/prover/cache traits, `SignatureSolver`, `MemoryCache`, `Phase::Mba` |
| `cobra` | no | `mba` plus `CobraSolver` (the `cobra-mba` 0.4 backend) |
| `eqsat` | no | `bitwright::eqsat`: the bounded equality-saturation search service and its built-in equations |
| `deobf` | no | GF(2) linear-map normal form (mixer inversion is in the core: §8.1) |
| `serde` | no | serialization of configs, stats, values, facts |

**Dependencies.** One required dependency: `hashbrown` (no default features) for `HashTable<u32>`
interning without duplicated keys. Hashing uses an in-crate, specified, versioned 64-bit mixer, so
there is no hasher dependency. Optional: `cobra-mba ~0.4` (Apache-2.0), `serde`. Dev-only: `criterion`
(benches), `libfuzzer-sys`/`arbitrary` (fuzz). Random numbers in tests come from in-crate SplitMix64
with explicit seeds. The library has **no `build.rs`** and embeds no binary artifacts; the built-in rule
corpus is embedded `.bwr` source compiled at run time, with a checked-in proof ledger and a
freshness test (§7.3, §7.4).

---

## 3. Semantics

### 3.1 Widths and values

```rust
/// A bit width in 1..=512. Invalid widths cannot be constructed.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Width(NonZeroU16);
impl Width { pub const MAX_BITS: u16 = 512; pub const fn new(bits: u16) -> Result<Width, WidthError>; pub const fn bits(self) -> u16; }

/// Exact W-bit value. Bits at and above W are always zero (canonical), so derived Eq/Hash are exact.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct BitVec { width: Width, limbs: [u64; 8] }
```

`BitVec` is `Copy` (72 bytes) and lives on the stack; nodes never store it (§4.2). Constructors that could
violate canonical padding return `Result`; explicit truncation is spelled `wrapping_from_*`. Every
operation is dispatched once on the width: a native `u128` path for W ≤ 128 (multiply-high above 64
bits excepted) and `u64`-limb kernels up to 512 bits. Wide multiplication is schoolbook; wide
division is shift-subtract long division over whole limbs (about 3 µs at 512 bits), with Knuth's
algorithm D as the planned replacement if profiling shows it matters. `BitVec` orders by width,
then unsigned value (`Ord`), and implements `FromStr`/`Display` (`0xff:8`, `-1:32`, `8'hff`).

### 3.2 Operators (node kinds)

Shift and rotate counts have the same width as the value and are read as unsigned. `c` below is the
full W-bit unsigned count.

| Kind | Typing | Semantics at every W | SMT-LIB |
|-|-|-|-|
| `Const`, `Sym` | → W | literal; free symbol `(key, W)` | `#x…`, `declare-const` |
| `Not`, `Neg` | W → W | complement; two's-complement negation | `bvnot`, `bvneg` |
| `Popcnt`, `Clz`, `Ctz` | W → W | counts; `clz(0) = ctz(0) = W` | expansion |
| `Bswap` | W → W, **W % 8 = 0** (typing rule) | byte reversal | expansion |
| `BitRev` | W → W | bit reversal | expansion |
| `Add`, `Sub`, `Mul` | W,W → W | modulo 2^W | `bvadd`, `bvsub`, `bvmul` |
| `UMulHi`, `SMulHi` | W,W → W | high W bits of the 2W-bit unsigned / signed product | `extract` of 2W `bvmul` |
| `UDiv`, `URem` | W,W → W | `udiv(x,0) = ones`, `urem(x,0) = x`; else ⌊x/y⌋, x mod y | `bvudiv`, `bvurem` |
| `SDiv`, `SRem` | W,W → W | truncating; `sdiv(x,0) = (x <s 0 ? 1 : −1)`, `sdiv(smin,−1) = smin`; `srem(x,0) = x`, `srem(smin,−1) = 0`; remainder takes the dividend's sign | `bvsdiv`, `bvsrem` |
| `And`, `Or`, `Xor` | W,W → W | bitwise | `bvand`, `bvor`, `bvxor` |
| `Shl`, `LShr` | W,W → W | c ≥ W gives 0 | `bvshl`, `bvlshr` |
| `AShr` | W,W → W | c ≥ W gives the sign fill | `bvashr` |
| `RotL`, `RotR` | W,W → W | rotate by c mod W (W need not be a power of two) | `ite` expansion |
| `Pdep`, `Pext` | W,W → W | bit deposit / extract of x under mask y | expansion |
| `Eq`, `Ne`, `Ult`, `Ule`, `Slt`, `Sle` | W,W → 1 | comparison | `=`, `distinct`, `bvult`, … |
| `Zext<N>`, `Sext<N>` | W → N, N > W | extension (N = W is the identity at construction; N < W is an error) | `zero_extend`, `sign_extend` |
| `Extract<lo,N>` | W → N, lo + N ≤ W | bits [lo, lo + N) | `extract` |
| `Concat` | H, L → H + L ≤ 512 | hi · 2^L + lo | `concat` |
| `Select` | 1, W, W → W | c ? a : b | `ite` |
| `Ext(op, k)` | per registry | output k of a registered total extension operation | user body or uninterpreted |

That is under 50 kinds; the opcode is a `u8`.

**Derived constructors** build existing kinds and are not node kinds: `ugt uge sgt sge` (operand
swap), `trunc<N>` (= `extract<0,N>`), `umin umax smin smax` (compare + select), `andn orn xnor`,
`bit(x, i)`, `low_mask`, `abs`, `add_carry`, `sub_borrow`, `sadd_overflow`, `ssub_overflow`,
`mul_wide_{u,s}`, and saturating arithmetic (`add_sat_{u,s}`, `sub_sat_{u,s}`). Each is defined in
one place and checked against its definition on every operand pair at widths 1 to 5
(`derived_constructors_are_exact`); the text syntax spells the binary ones by name. (The printer
does not yet raise them back to their idioms.)

### 3.3 Extension operations

```rust
pub trait ExtOp: Send + Sync + 'static {
    fn name(&self) -> &str;                                     // namespaced: "acme.avgu"
    fn revision(&self) -> u32 { 1 }                             // bump when `eval` changes; enters hashes
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String>;   // 1..=3 args, 1..=8 outputs
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]);        // exact and TOTAL
    fn known_bits(&self, _args: &[KnownBits], _out: &mut [KnownBits]) {}
    fn expand(&self, _cx: &mut Context, _args: &[Expr]) -> Option<Result<Vec<Expr>, Error>> { None }
    fn smtlib(&self, _output: u8, _args: &[&str], _widths: &[Width]) -> Option<String> { None }
    fn traits(&self) -> ExtTraits { ExtTraits::default() }      // commutative, opaque
    fn invertible(&self, _output: u8, _arg: u8, _args: &[KnownBits]) -> Invertible { Invertible::No }
    fn invert(&self, _output: u8, _arg: u8, _args: &[BitVec], _value: &BitVec) -> Option<BitVec> { None }
}
```

- Operations are registered into an immutable `Registry` (at most 256), which a context is built
  with (`Context::with_registry`, or `extend_registry` with a registry keeping every current
  operation, its revision and traits at its position). Registration runs a **contract
  self-test** at up to 64 argument-width tuples the signature accepts, drawn from widths 1 to 512
  (every width for one argument, every pair for two, every triple with two equal for three, so
  mixed widths such as a value and a count are covered): declared output widths, determinism (two
  calls), a commutative operation's symmetry, known-bits soundness against `eval` on random
  partial-knowledge inputs, `expand ≡ eval`, and every invertibility declaration (`invert`
  recovers the argument from the output at a completion of the other arguments' known bits, and
  for a bijection finds an argument for a random output value). An operation no tuple is
  accepted for is refused.
  The self-test samples: an operation that breaks its contract only elsewhere is not caught.
  `ext::check` runs it alone, and `register_unchecked` skips it, for a host that registers the
  same operations in many registries (one per arena) and checks them once in its own tests.
- An `ExtId` is a position plus a tag of the operation's name and revision; a registry refuses an
  id whose tag does not match the operation at that position.
- **Representation.** Each output is a node of its own whose children are the call's arguments
  (1 to 3): the opcode says the arity and the output (24 opcodes after the built-in ones, so
  built-in ranks are unchanged), and `aux` holds the operation's registry index. So an output's
  value is a function of its children like any node's, and every traversal (evaluation, facts,
  substitution, the engine's bottom-up walk, sampled verification) needs no special case beyond
  asking the operation. Outputs are hash-consed by operation (its name and revision enter the
  structural hash), output and arguments; commutative operations get their first two arguments in
  canonical order when those have one width; calls on constants fold (unless `eval` breaks its
  contract on them; the node is built instead). An operation that must never be merged takes a fresh
  symbol as an argument (an occurrence key).
- Every `eval`/`known_bits` result is checked against the declared widths; a violation is
  `Error::Contract` in construction and evaluation, and `top` in facts. Facts are exact when every
  argument's facts pin it, otherwise from `known_bits`.
- To rules and passes, an extension node is an atom (no rule has one as a pattern; the dispatch net
  has no entries for their opcodes, and a static assertion keeps every opcode inside its mask;
  passes and MBA lowering treat unknown operators as atoms). Equality saturation declines a root
  containing one under its default `UnsupportedPolicy::Decline` and treats it as an atom under
  `Atomize`. The engine simplifies the arguments and rebuilds the call through the
  builder, unless `traits().opaque`, which makes the call an atom arguments included.
- Text: `@name(args)` for output 0 and `@name[k](args)` otherwise; literal arguments carry their
  widths, and the output width comes from the signature (leaves under a call's arguments take the
  default width before other leaves, so a leaf next to an output takes its width). SMT-LIB: the
  operation's `smtlib` term (refused unless it is one balanced expression), or an uninterpreted
  function `|ext!name#rev[k]@w1,w2|` (the `ext!` prefix is reserved) declared once per output and
  argument widths, in which case scripts declare `QF_UFBV`: `unsat` still proves, but a `sat` model
  may rest on values the real operation never takes. Import does not read such functions back.

### 3.4 Faults and traps

Division by zero and signed overflow are **values** in bitwright (D1). A host that models a trapping
divide builds a trap guard next to the value:

```rust
let q    = cx.udiv(x, y)?;
let trap = bitwright::traps::udiv(&mut cx, x, y)?;   // (y == 0), a 1-bit expression
```

The guard is an ordinary expression: the host keeps its effect anchor while
`prove(trap == 0) != True`, and may drop it once the guard is proved false. `traps::{udiv, urem, sdiv,
srem}` cover `y == 0` and, for signed forms, `x == smin & y == −1`; `traps::{shift, rotate}` cover a
count `>=u W`, for hosts where an out-of-range count faults or is undefined. On a path that does not
fault, the host assumes the guard false (§5, constraints).

---

## 4. Term store

### 4.1 Ownership and handles

```rust
pub struct Context { /* Arc<Registry>, arena, facts, memo, config */ }
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Expr { index: u32, tag: NonZeroU32 }     // tag: unique per context generation
```

- An `Expr` is valid only in the context *and generation* that created it. Every new context and
  every `Context::clear()` draws a fresh 32-bit tag from a process-wide counter (the only
  process-wide state; it never affects results), so a stale or foreign handle is rejected with
  `Error::StaleExpr`/`Error::ForeignExpr` (one compare per call). Tags repeat only after 2^32
  generations have been created in one process. `Mark`s carry the tag too.
- Traversals (`post_order`, `symbols_in`, `dag_size`, `eval`, facts) take `&mut self` because they
  reuse generation-stamped scratch owned by the context; `Context` is `Send`, not `Sync`.
- The arena is **append-only**, and every child index is lower than its parent's, so **ascending index
  is a topological order**. There is no API that mutates or replaces a node.
- `Context::new(registry)` allocates nothing until the first node. Hosts can afford one context per
  basic block, region or function.
- "Equal `Expr` ⇒ equal value" is a documented, tested contract (hosts use handles as value numbers).
  The converse does not hold.

### 4.2 Layout

```rust
#[repr(C)] struct Node { op: OpCode /*u8*/, aux: u8, width: u16, a: u32, b: u32, c: u32 }   // 16 B
// side columns, one entry per node:
//   shash: u64    structural hash (also the interning fingerprint and the OrderKey payload)
//   height: u32   saturating structural depth
//   tree: u32     saturating unfolded tree size
```

Constants of ≤ 128 bits live in a `u128` pool; wider constants in a limb pool. Extension arguments live in
an argument pool. About 32 bytes per node plus the interner slot. Facts, memo and pass products are
separate side tables, allocated lazily. A `BitVec` takes 72 bytes whatever its width (a `Facts`,
six of them, 432), so the tables that hold a value per node pack widths up to 64 into words: base
facts are six words per node (the known bits and both ranges' bounds) in computation order, found
through a slot per node index; facts under assumptions and the linear and xor passes' forms are
packed the same way; the rewrite memo keeps result nodes in pages of 512 node indices per phase,
with the constraints a result relied on apart (there are none without assumptions). Wider values
are kept whole. At 520k nodes this is a ninth of the memory for facts and a fifth for a
simplification, which also takes a sixth of the last-level cache misses.

**Interning.** `hashbrown::HashTable<u32>` keyed by `shash`; full node equality is checked on every
hit; hits are free against the node budget. The hash seed changes table layout only, never results.

### 4.3 Canonicalization at construction

Every stored node is in canonical form; there is no raw mode, because matching relies on the invariant.
All steps are O(1), documented, and exhaustively tested at W ≤ 4 against the reference evaluator.

1. **Validation.** Arity, widths, conversion direction, `Bswap` byte width. Errors, never panics.
2. **Folding.** All-constant operands evaluate, for every core kind and for extension ops.
3. **Operand order.** Commutative operands (`Add Mul UMulHi SMulHi And Or Xor Eq Ne`, and an extension
   op's declared pair) are ordered by `OrderKey`, with constants always on the right.
   `ugt/uge/sgt/sge` build the swapped `ult/ule/slt/sle`.
4. **Normalizing spellings.** `sub(x, c) → add(x, −c)`, `sub(0, x) → neg(x)`, `rotr(x, c) → rotl(x, (W − c
   mod W) mod W)` for constant c, constant rotate counts reduced mod W, `not(cmp) → inverse cmp`.
5. **Identities that are sound under total semantics:** `x+0, x·1, x·0, x&0, x&ones, x|0, x|ones, x^0,
   x^x, x−x`, shifts and rotates by 0, shifts by a constant ≥ W, `not∘not`, `neg∘neg`, `bswap∘bswap`,
   `bitrev∘bitrev`, reflexive compares, `select` with a constant condition or equal arms,
   `select(c, 1, 0) → c` at width 1.
6. **Cast collapse.** Same-width casts vanish; `zext∘zext`, `sext∘sext`, `sext∘zext → zext`;
   `extract` of the full width; `extract∘extract`; `extract` of a `zext/sext/concat` that stays inside
   one part; `concat` of constants and of adjacent extracts of one value.

The construction table is itself covered by the soundness gate (§7.5) and never increases the
termination measure (§6.5).

**OrderKey** (u64, context-independent): 2 bits of class (compound < symbol < constant), 6 bits of op
rank, 56 bits of payload (the top of `shash` for compounds, the key for symbols, the value for
constants). Ties are broken deterministically by the full key, then a bounded structural comparison,
then the index. The hash function is part of the output-stability contract (§11).

### 4.4 Symbols

`cx.symbol(key, w)` with `SymbolKey::{U64(u64), Str(Arc<str>)}` returns the one symbol for that key. A
key has exactly one width per context; asking for another width is `Error::SymbolWidthConflict`
(there is no width-polymorphic identity). `find_symbol(&key)` is O(1) and never creates.
`fresh_symbol(w)` draws from a reserved namespace. `symbol_key(id)` is the reverse lookup.

### 4.5 Structural metadata and growth accounting

- `height(e)`, `tree_size(e)`: exact up to saturation, O(1). Depth-triggered maintenance in a host is a
  field read, never a traversal.
- `dag_size(roots, cap) -> Bounded` walks with reusable generation-stamped marks, no sorting, and stops
  at `cap + 1`, returning `AtLeast(cap + 1)`. Exact results for a root are cached. **An unknown size
  never establishes profitability.**
- `counters() -> ArenaCounters { caller_nodes, engine_nodes }` and `mark()`/`caller_growth_since(mark)`
  let a host retry maintenance only after enough *input* growth; nodes built by bitwright's own
  simplification, MBA or search are counted separately.

### 4.6 Views, traversal, evaluation, substitution, text

- `view(e) -> View<'_>`: an allocation-free `Copy` enum carrying children; `children(e)` iterator;
  `post_order(roots)` iterative, multi-root, deduplicated; `symbols_in(roots)` sorted by key.
- `ExprMap<T>` / `ExprSet`: dense side tables and reusable bitsets.
- `eval(roots, &dyn Env) -> Result<Vec<BitVec>>`: iterative, memoized per call; an unbound symbol is an
  error.
- `substitute(roots, &[(Expr, Expr)])`: simultaneous, width-checked, DAG-preserving, rebuilt through
  the builder (so re-canonicalized and folded), charged before allocating.
  `substitute_bounded(roots, &mut Substitution, max_visits)` does the same incrementally: it never
  walks below a replaced or already-rewritten node, stops at `max_visits` new nodes (`Ok(None)`)
  and resumes its own walk on the next call over the same roots, so total work stays linear; the
  `Substitution` keeps every node's image (`image`, `changed`) for hosts carrying metadata along.
- `set_max_nodes(n)`: changes the node limit at run time; interning an existing node never counts.
- `cx.parse(src, &ParseOptions)` and `cx.display(e)`: the shared text syntax (§7.1). The printer is
  DAG-aware (`let`-binds shared subterms), bounded by `max_nodes`/`max_chars` with an explicit
  truncation marker, and never walks a DAG as a tree.
- **SMT-LIB 2.6** (feature `smtlib`). `smtlib::export(cx, roots)` writes one `declare-const` per
  symbol and one `define-fun` per node, operands first (sharing kept; no nesting deeper than a
  constant), then `rootK` per root. Operators without a QF_BV counterpart (population count,
  leading/trailing zeros, byte swap, bit reverse, `pdep`, `pext`, high products, rotations by a
  symbolic count) are expanded through flat chains of helper definitions. Symbols keep their names
  where SMT-LIB can spell them (`|name|`, `|#k|` for integer keys, `|$k|` for fresh keys) and are
  otherwise `sym!id`; names of the exporter's own form are never used for symbols.
  `equivalence_query(cx, a, b)` is a complete script whose `unsat` proves `a = b`.
  `smtlib::import(cx, script)` reads a QF_BV subset: `declare-const`, `declare-fun` and
  `define-fun` without parameters, `assert`, `let`, `ite`, `=`, `distinct`, the Boolean core, every
  QF_BV operator and its extensions (`bvsmod` expanded); Booleans become 1-bit expressions. It
  checks the whole script's syntax first (a syntax error leaves the context untouched), then reads
  one top-level command at a time, its tokens borrowed from the script, and evaluates it before
  reading the next, so memory follows the largest command, not the script. It reads with an
  explicit stack and evaluates terms recursively within the same 512-level nesting cap, refuses
  widths outside 1..=512, and returns an error, never a panic, for
  anything else. Symbols named after SMT-LIB's reserved words and theory symbols (`and`, `true`,
  `_`, `bvadd`, …) are exported as `sym!id`, never as `|name|`, which would redefine them. An exported script imports back to the
  same function over the same symbol keys.

---

## 5. Facts and proofs

```rust
pub struct KnownBits { width: Width, zero: [u64; 8], one: [u64; 8] }   // zero & one == 0
pub struct URange { lo: BitVec, hi: BitVec }                            // non-wrapping, lo ≤ hi
pub struct SRange { lo: BitVec, hi: BitVec }                            // signed order
pub struct Facts { /* private: known, urange, srange — always mutually reduced */ }
impl Facts { pub fn new(k: KnownBits, u: URange, s: SRange) -> Option<Facts>;   // width-checked
             pub fn known(&self) -> KnownBits; pub fn urange(&self) -> URange; pub fn srange(&self) -> SRange;
             pub fn meet(&self, o: &Facts) -> Option<Facts>; pub fn join(&self, o: &Facts) -> Option<Facts>; }
pub enum Truth { True, False, Unknown }
#[non_exhaustive] pub enum Query<'q> {
    IsZero(Expr), IsNonZero(Expr), Bit { e: Expr, bit: u16, value: bool }, Eq(Expr, Expr),
    Cmp(CmpOpExt, Expr, Expr), InURange { .. }, InSRange { .. }, Aligned { e: Expr, log2: u16 },
    MaskRedundant { e: Expr, mask: &'q BitVec }, FitsUnsigned { e: Expr, bits: u16 },
    FitsSigned { e: Expr, bits: u16 }, IsConstant(Expr),
    Injective { e: Expr, of: Expr }, Bijective { e: Expr, of: Expr },   // §8.1
}
impl Context {
    pub fn facts(&mut self, e: Expr) -> Result<Facts, Error>;             // cap reached → top (sound)
    pub fn try_facts(&mut self, e: Expr) -> Result<Option<Facts>, Error>; // None: cap reached; resumable
    pub fn prove(&mut self, q: Query<'_>) -> Result<Truth, Error>;        // Err only for bad handles/widths
    pub fn exact(&mut self, e: Expr) -> Result<Option<BitVec>, Error>;   // constant or fully known
    pub fn enumerate_values(&mut self, e: Expr, limit: u32) -> Result<Option<Vec<BitVec>>, Error>;
    pub fn facts_with(&mut self, e: Expr, a: &Assumptions) -> Result<Option<Facts>, Error>; // None: infeasible
    pub fn prove_with(&mut self, q: Query<'_>, a: &Assumptions) -> Result<Truth, Error>;
    pub fn prove_under(&mut self, q: Query<'_>, a: &Assumptions) -> Result<Proof, Error>; // + reliance
}
```

- **Lazy, iterative, cached, resumable.** Facts are computed on demand in topological order (no
  recursion) and cached per node; each query runs at most `ContextConfig::fact_work` transfers.
  A node is cached only when its transfer completed; reaching the cap answers a sound `top`, and the
  next query for the same expression resumes from a saved post-order, so total work stays linear.
- **Fact queries never allocate arena nodes.** The fact engine borrows the arena immutably.
- **Reduced product.** After every transfer, known bits refine ranges and ranges refine known bits.
- **Transfers** for every kind, each exhaustively tested at W ≤ 4 over all known-bit input states and
  sampled above: carry-propagating add/sub; multiply low bits and trailing zeros; multiply-high leading
  zeros from ranges; division and remainder by constants and by ranges; shifts and rotates by constant
  and by symbolic counts (bounded by the count's range); counts; byte and bit permutations;
  pdep/pext; casts; select (join); compares decided from bits and ranges; extension ops through their
  declared transfer, width-validated. Three refinements read the node's structure as well as its
  operands' facts: a select between the operands of its own comparison (a minimum or maximum), a
  `concat` of a high product and its low product (the wide product), and a right shift by the
  value's own top bits, `a >>u (a >>u k)` (when the count is `t`, `a < (t + 1)·2^k`, so the
  result is below `2^k` wherever `2^t ≥ t + 1`: the data-dependent xorshift of murmur-style
  mixers changes only its low `k` bits).
- **Proofs** are tri-state and fail closed; `Unknown` is always legal. `Eq(a, b)` is `True` iff the
  handles are equal, `False` iff the facts conflict.
- **Constraints** (`Assumptions`, consumer-defined): facts about expressions
  (`assume(cx, e, facts)`) and 1-bit predicates assumed true or false (`assume_true`,
  `assume_false`), each numbered by a `ConstraintId` (its position). A constraint restricts values
  and never changes an operator's meaning, so every proof under constraints is valid wherever
  they hold. Adding one propagates it, bounded at 4096 steps with 3 re-propagation rounds
  (`is_truncated` reports a stop):
  *backwards* through a backward transfer per operator (`facts/backward.rs`: bitwise with known
  bits, add/sub/odd-multiply low bits and constant offsets, constant shifts and rotations,
  permutations, bit counts, casts, extract/concat, select, comparisons against the other operand's
  range), and *between comparisons*: an assumed comparison of two expressions records their
  possible orderings (five worlds: unsigned and signed order, equal in both or neither), which
  decide every other comparison of the pair, in the overlay and in `prove_under`. Equalities are
  transitive: expressions assumed equal (or ordered so only equality is left) join one class
  (union-find, the lowest index represents it), and orderings are kept between classes, so
  `x == y`, `y == z`, `x != z` is a contradiction and `x == y`, `y <u w` decides `x <u w`. Every derived
  fact carries the constraints it rests on (`Reliance`, a 64-bit over-approximating set, from the
  64th constraint on tracked together). Contradictions make the set infeasible
  (`conflict()` names the constraints involved); an infeasible set proves every well-formed query
  and the engine proves nothing from it. Facts under constraints live in an overlay keyed by the
  set (pointer equality first), never pollute the base cache, and are computed only for nodes at
  or above the lowest constrained node; every node a query walks is cached in the overlay (those
  depending on no constraint with their base facts), so later queries stop at it. Propagation
  drops only the cached facts at or above a changed node, and re-propagates only from recorded
  facts whose operands have a changed node below them (each costing a step), so adding
  constraints takes linear work. A set used with another context, or kept across `clear`, is an
  error (`StaleExpr`, `ForeignExpr`) in every query and in `Engine::run`; the engine ignores an
  infeasible set (simplifies as without constraints). Sets are `Arc`-shared: a clone is O(1), and
  the first change to a shared clone copies it (adding to a set that is also the context's
  overlay key does not: the key is dropped instead). Validation: every backward transfer is sound exhaustively at
  W ≤ 3 and sampled at 4..6; end to end, facts, proofs, orderings and infeasibility are checked
  against every satisfying assignment; engine results are checked equal to their inputs wherever
  the constraints they rely on hold, exhaustively, and by z3 and bitwuzla at widths up to 64.
- **Public transfers.** `Facts::apply_un/apply_bin/apply_cmp`, `zext/sext/extract/concat/select`
  and `KnownBits::apply_un/apply_bin` expose the transfer functions (width-checked), so a host can
  compose facts for its own operations.
- **Fact providers** (host-supplied facts for symbols) are not a separate mechanism in 0.x:
  assumptions about symbol nodes cover the same need.
- **Storage (current).** The cache is a sparse map keyed by node, filled only for nodes that were
  queried or lie under a queried node (a `Facts` is 432 bytes). A compact dense tier for
  ≤ 128-bit nodes is planned once the engine's access pattern is measured (M4).
- **Enumeration.** `enumerate_values` returns every value the facts allow (from the unsigned range
  when it is narrow, from the known bits otherwise), so it includes every value the expression can
  take and may include impossible ones.
- **Validation.** Every transfer is sound exhaustively at W ≤ 3 over every known-bits state plus
  facts of random value sets and intervals, sampled at W = 4..8 and wide widths; the known-bits
  transfers of the bitwise, additive, constant-shift/rotate and cast operators are *optimal* at
  W ≤ 3 (equal to the best transformer). Planted transfer bugs, including precision-only ones, are
  used to check that the suite catches them.

---

## 6. The simplifier

### 6.1 Engine, strategy, run, outcome

```rust
pub struct Engine { /* Arc: linked rules, Strategy, dispatch nets, Verify, config hash */ }
impl Engine {
    pub fn standard() -> Engine;                               // built-in corpus, Strategy::standard()
    pub fn builder() -> EngineBuilder;                         // .builtin(), .program(p, &ledger),
                                                               // .unproven_program(p), .allow_unproven(b),
                                                               // .strategy(s), .verify(v), .build()
    pub fn simplify(&self, cx: &mut Context, e: Expr) -> Result<RootOutcome, Error>;
    pub fn run(&self, cx: &mut Context, roots: &[Expr], run: Run<'_>) -> Result<Outcome, Error>;
}
pub struct Run<'a> {
    pub allowance: Option<&'a mut Allowance>,   // caller-owned, shared across calls; None = none
    pub per_call: Budget,                       // caps on this call, applied inside the allowance
    pub admission: Admission,                   // per-root caps, checked before any work
    pub observer: Option<&'a mut dyn Observer>, pub hooks: Option<&'a dyn Hooks>,
    pub assumptions: Option<&'a Assumptions>, pub deadline: Option<Deadline<'a>>,
}
pub struct Outcome { pub roots: Vec<RootOutcome>, pub stats: Stats }   // roots[i] answers input i
pub struct RootOutcome { pub expr: Expr, pub changed: bool, pub end: End, pub relies_on: Reliance }
pub enum End { Completed, BudgetTerminated(Exhausted), Declined(Decline) }
pub enum Decline { AdmissionCap(Cap) }        // Unsupported(..) arrives with extension ops
```

- **Every root reports one outcome**, and `changed` is orthogonal: a root may be changed *and*
  budget-terminated. Roots may repeat and arrive in any order; each distinct root is processed once
  and output *i* always answers input *i*.
- A `BudgetTerminated` root is still **value-equivalent** to its input (every committed step preserves
  value), but it is not final. A call's budget or deadline stops the call; the context's per-query
  fact cap (`ContextConfig::fact_work`) or the matcher's per-application step cap only declines the
  rule at hand, the call goes on, and a root whose result depends on such a decline also ends
  `BudgetTerminated` (with `FactWork` or `MatchSteps`). `Completed` therefore always means final.
- `Engine` is `Send + Sync` and cheap to clone. `Context` is `Send`, not `Sync`. The engine never
  spawns threads.
- **Linking.** Every rule must be vouched for by its program's ledger (name and content hash), or the
  build fails (`BuildError::Unproven`) unless `allow_unproven` is set; unproven rules get sampled
  verification by default (§6.4). The built-in corpus is compiled once per process into an
  immutable cache (it never influences a result).

`Strategy` is named, typed and hashable policy:

```rust
pub enum Phase {
    Local { groups: Vec<String> },   // directed rules of these groups, bottom-up fixpoint
    FactFold, Linear, Xor, Bitwise, Compares, Casts, Demanded, LinearMba, Shuffle,  // passes (§8)
    Invert,                          // equalities through invertible maps (§8.1)
    // M6: Mba(MbaConfig); later: Raise (display idioms, last phase only)
}
pub struct Strategy { pub name: Cow<'static, str>, pub phases: Vec<Phase>, pub max_rounds: u8 }
// Strategy::standard(), Strategy::deobfuscate(), Strategy::new(name, phases), .with_max_rounds(n)
```

Phases run in order within a round; rounds repeat until nothing changes or `max_rounds` is reached.
A `Local` phase reaches its fixpoint within one round by itself; rounds exist for the interplay of
phases.

### 6.2 Budgets and allowances

```rust
pub struct Budget { pub node_visits: u64, pub candidates: u64, pub match_steps: u64,
                    pub rewrites: u64, pub new_nodes: u64, pub fact_work: u64,
                    pub pass_work: u64 }                                          // #[non_exhaustive]
// Budget::UNLIMITED, Budget::ZERO, Budget::default() (generous per-call caps)
pub enum Exhausted { NodeVisits, Candidates, MatchSteps, Rewrites, NewNodes, FactWork,
                     PassWork, Deadline, ArenaCapacity }
pub struct Allowance { /* remaining: Budget, spent: Budget */ }
pub trait Clock { fn now_ticks(&self) -> u64; }
pub struct Deadline<'a> { pub clock: &'a dyn Clock, pub at: u64, pub check_every: u32 }
pub struct Admission { pub max_root_height: u32, pub max_root_tree_size: u32,
                       pub max_root_dag_size: Option<u32> }
```

- An `Allowance` is a spendable account that can span every call of a unit of work (for example every
  block of one pass). **Spent work is never refunded.** A call's effective limit is the minimum of
  its `per_call` budget and what remains of the allowance. Budgets for passes, MBA and search join
  the struct with their milestones (it is `#[non_exhaustive]`).
- Charging is by a fixed schedule: one per node visit, per candidate after the dispatch prefilter,
  per matcher step (pattern/node pair), per committed rewrite, per created node, and per fact
  transfer run for a guard (each fact query is capped by what remains, so the budget is never
  overrun); sampled verification charges one visit per node it evaluates, and a node answered from
  the memo is free. Budgets are therefore deterministic; deadlines are not, and are for hosts that
  prefer wall-clock bounds. A passed deadline stays passed: every later root of the call stops too.
- **Admission is checked first**, from O(1) node metadata (height, tree size) and, if requested, a
  bounded `dag_size`. A declined root costs no visits.

### 6.3 The `Local` phase

An iterative post-order over the reachable DAG of all roots, with one shared memo per phase:

1. Rebuild node *n* from its already-normal children through the builder (which canonicalizes and
   folds); if that makes a different node, normalize that node instead.
2. Look up candidates in the **dispatch net**: root operator, then per-operand operator masks
   (commutative roots in either order), giving a short candidate slice in priority order (the
   phase's group order, then source order). The net is a pure prefilter, tested as such.
3. For each candidate: the matcher (a complete backtracking search, §7.3, under a per-application
   step budget), the rule's width admission, then the guard. **A rejection moves to the next
   candidate.**
4. On acceptance, the template is instantiated through the builder, the postconditions run (§6.4),
   and the result is normalized in turn (a rewrite can create a new redex at the same node). There is
   no recursion: 10^5-deep chains are processed with an explicit stack.
5. When no candidate applies, *n* is normal. It is memoized as final only if no candidate was
   declined for lack of work (a capped fact query, an exhausted matcher step budget, no fact budget)
   and all of its operands were final; otherwise the result is kept for this call only, so a later
   call with more budget still reaches the true normal form. This holds through rewrites: a node
   rewritten by a later candidate after an earlier one was declined for lack of work is not final
   either, and neither is a node that skipped a rule quarantined for the call.

**Guards** are evaluated directly over the rule IR: pure parts from the constant parameters, fact
predicates from the context's facts (under the run's assumptions, if any). A fact query that hits
the context's per-query work cap answers "unknown", which declines the rule and marks the node as not
final.

### 6.4 Postconditions (every application, by a rule or a pass)

- The result width equals the matched width. The compiler proves it; a violation (a compiler bug or a
  malformed program) rejects the rewrite and quarantines the rule for the call.
- `Hooks::admit(cx, before, after, by)` is a deterministic host veto; `by` is `By::Rule(&Rule)`
  or `By::Pass(name)`. A rule or pass that fails a width, verification or tripwire check is
  quarantined for the call.
- `Verify { sampled_points, unproven_points, tripwire, termination }`: sampled evaluation of both
  sides at points seeded per symbol (by default 16 points for unproven rules only; a failure
  quarantines the rule; values are cached per node for the call, so verification is linear in the
  DAG), the fact tripwire (both sides' facts must meet), and, for rules, the ground termination
  order (the result must not be shown larger; a comparison undecided because tree sizes saturate is
  no evidence against the compiler's static proof and accepts). Passes are held to their own commit
  rule (§8) instead of the termination order. `Verify::strict()` turns everything on and is
  used by the engine tests. A rewrite that relied on constraints is compared only at the points
  where those constraints hold (sampled points ignore constraints, so a rewrite valid only under
  them would otherwise be rejected and its rule quarantined).

### 6.5 Termination

- Every `Local` rule satisfies, checked at compile time: (i) the variable condition, `occ_rhs(x) ≤
  occ_lhs(x)`; (ii) a strict decrease of a Knuth–Bendix order: total weight (every operator ≥ 1,
  variables and constants 1), then operator precedence (for example `Sub > Add`, `Mul > Shl`,
  `Add > Or`) to orient cost-neutral canonicalizations.
- The order is monotone and stable under substitution, so rewriting anywhere in a term strictly
  decreases the whole term: the system terminates, and a template can never rebuild an ancestor that
  is still being reduced.
- Passes commit only when the DAG gets strictly smaller (§8), so the rules' order and the passes'
  size decrease together bound every chain of changes; rounds are capped by `max_rounds`.
- Rule terms are compared as the builder stores them (closed and constant-only subterms are one
  constant, comparisons in stored form, commutative operands as a multiset; §7.3), so
  construction canonicalization of a template does not undo the decrease. This is tested: every
  application of every built-in rule on random instances strictly decreases the ground order on
  the actual nodes (`rules::order::ground_greater`), which the engine can also assert. Normal-form passes commit only on
  a strict decrease of DAG cost (§8). `max_rounds` bounds the pass/rule interplay deterministically.
- An `identity` whose authored direction does not decrease the order is not a directed rule at all; it
  is available only to the search service (§10).

### 6.6 Memo

The memo lives in the `Context`: per phase, a map from node to its completed result. Its key (the
epoch) is the engine's configuration hash (linked rule ids and proof status, strategy, verification
settings) combined with the presence of hooks and their revision, plus an exact copy of the run's
assumptions; any change
drops it. **Only final results are stored**: nothing cut by a budget, a deadline or a capped fact
query. Each stored result keeps the constraints its rewrites relied on, so a memo hit reports the
same `RootOutcome::relies_on` as the run that filled it. A repeated run over an already-simplified
DAG costs one lookup per root.

### 6.7 Telemetry and hooks

`Stats` is always collected (plain counters): visits, memo hits, candidates, matcher steps, the
decline taxonomy (no match, guard false, degraded for lack of work, applied without change), rewrites, host vetoes,
postcondition rejections and quarantines, new nodes, fact work, rounds, and the root-outcome matrix
{completed, budget-terminated} × {unchanged, changed} plus declined roots. **No-op work is a
first-class number.**

`Observer` receives per-rule events (candidate, no match, guard false, degraded, no change, applied,
vetoed, rejected); `RuleCensus` (per-rule counts) ships with the library. With no observer the cost is one
predictable branch per event.

`Hooks { admit(cx, before, after, by) -> bool, fold_known(cx, e) -> bool, revision() -> u64 }` is
deterministic host policy (`fold_known` gates every pass that turns known bits into a constant:
fact folding and the demanded-bits pass); its revision enters the memo epoch. `Event::{Applied,
Vetoed, Rejected}` carry `by` as well, and `Stats` reports `pass_work` and per-pass counters.

### 6.8 Cache validity

| Cache | Owner | Stores | Depends on | Invalidated by |
|-|-|-|-|-|
| interner, node columns | Context generation | structure (immutable) | nothing | `clear()` |
| fact cache (base) | Context | completed transfers only | provider revision | `clear()`, provider revision |
| fact overlay | Context | facts under assumptions | assumptions revision | new assumptions, `clear()` |
| rewrite memo (per phase) | Context | final results only | memo epoch (§6.6) | epoch change, `clear()` |
| analysis products | Context | exact values; bounded sizes as `AtLeast` | node only | `clear()` |
| eqsat memo | Context | completed candidates, stable declines | eqsat epoch | epoch change, `clear()` |
| MBA cache store | host (`MbaCacheStore`) | gate-accepted results, complete "no simpler" | solver, prover, trust, lowering and program versions (in the key) | never (content-addressed) |
| dispatch net, linked programs, registry | Engine / Arc | compiled tables | — | build a new engine |

No cache holds an `Expr` beyond the context generation that created it.

---

## 7. The rule language (`.bwr`)

### 7.1 Expression syntax (shared with the parser and printer)

Hacker's-Delight-style infix with explicit signedness and Rust precedence:

```text
| ^ &  << >>u >>s  + -  *  ~x -x   == != <u <=u >u >=u <s <=s >s >=s
udiv sdiv urem srem rotl rotr umulhi smulhi pdep pext popcnt clz ctz bswap bitrev
zext<N>(x) sext<N>(x) trunc<N>(x) extract<LO, N>(x) concat(h, l) select(c, a, b)   umin umax …
literals: 42  0xff  0b1010  -1  true  false        width ascription: e:W  (0xff:8, x:64)
symbols: name  #123 (integer key)  $7 (fresh key)  "any name"      shared subterms: let %0 = …; …
rule-only literals: ones  zero  one  smin_lit  smax_lit  lowmask(N)  bit(K)
extension ops: @acme.avgu(a, b)  @acme.divmod#1(a, b)
```

A bare `>>` is an error ("write `>>u` or `>>s`"); a bare `<` only opens width generics, so ordering
comparisons are always signed-explicit. There is no ternary operator (`select` keeps `:` free for width
ascription). Widths of symbols and literals are inferred by unification where possible. Parser
nesting is limited (128 levels in expression text, 64 in rule text, including width expressions)
so untrusted text cannot exhaust the stack; the printer binds
subterms with `let` well before that depth. `parse(print(e)) == e` is a tested property.

### 7.2 Rules and identities

```text
bitwright 1;                                    // language edition

group core.bitwise {
    /// Absorption. One orientation is authored; the compiler emits the others.
    #[example("(q | p) & p" => "p")]
    rule and_absorb_or<W>(x: W, y: W) { x & (x | y) => x }

    /// Unconditional identity: directed (it decreases the order) AND admissible to eqsat.
    identity add_and_or<W>(x: W, y: W) { (x & y) + (x | y) <=> x + y }

    /// Fact-guarded.
    rule and_mask_redundant<W>(x: W, c: const W) {
        x & c => x
        if zero_bits(x, ~c)
    }

    /// Proof-guarded (never an arithmetic adjacency guess that can wrap).
    rule eq_eq_distinct<W>(a: W, b: W, c: W) {
        (a == b) & (a == c) => false
        if proves(b != c)
    }
}

group core.arith {
    /// Does not decrease the order: eqsat-only (note BW0409).
    identity mul_distrib<W>(x: W, y: W, z: W) { x * (y + z) <=> x * y + x * z }

    rule mul_pow2<W>(x: W, c: const W) {
        x * c => x << k
        if is_pow2(c)
        let k: W = ctz(c)
    }
}

group core.casts {
    /// Sign extension spelled as "value | (sign word << W)". Needs U <= 2W to be exact.
    rule sext_from_sign_word<W, U>(a: W) where W < U, U <= 2 * W {
        zext<U>(a) | (zext<U>(a >>s (W - 1)) << W) => sext<U>(a)
    }
}
```

- **Parameters are declared**: `x: W` binds anything of width W; `c: const W` binds only constants;
  `sym` binds only symbols; `nonconst` binds anything else. Multiple width variables with linear
  constraints (`where W < U, U <= 2 * W`, and moduli such as `W % 8 == 0`).
- **Literals are bidirectionally typed** from context; an ambiguous literal is an error ("write
  `1:W`"). A width expression in value position (`W - 1`) becomes a literal at the inferred width.
  The compiler checks every width assignment the constraints admit: a rule that is ill-typed at any
  of them (a literal or width value that does not fit, an extract out of range) is rejected
  (BW0107, "add a `where` constraint"). Nothing is silently truncated.
- **Guards** (`if …`) combine, with `&&`, `||` and `!`:
  - *fact predicates*, answered by the fact engine and true only when proven: `zero_bits(x, m)`
    (every bit of `m` is zero in `x`), `one_bits(x, m)`, `nonzero(x)`, `disjoint(x, y)` (no bit can
    be one in both), and `proves(a OP b)` for a comparison of parameters, literals and `let`s;
  - *constant predicates* on `const` parameters: `is_pow2`, `is_lowmask`, `is_shifted_mask`;
  - *pure conditions*: comparisons and arithmetic over `const` parameters, literals and `let`s.

  Fact predicates are **monotone**: they may not appear under `!` (BW0106). A fact engine can only
  prove, never refute, so a guard must become no truer when the engine knows less. This is what lets
  the checker test a rule against exact facts and conclude it is sound for every sound, weaker fact
  engine (§7.4). Masks and `let`s are constant computations (BW0105); a `let` is evaluated once per
  application, and an application whose `let` is undefined does not fire.
- **Casts carry their target width as a type argument**; matching binds widths from node widths and
  never allocates.
- **The template's width must equal the pattern's width** (compile error otherwise). Every template
  variable must be bound.
- **`identity` vs `rule`** is explicit and checked at three levels: syntax (an identity has no `if`,
  `let`, capture kinds or extension ops, and uses `<=>`; `where` may only constrain widths); compiler
  (every variable occurs on both sides; the kind is part of the rule id); checker (identities are
  proven with no oracles and get the `unconditional` evidence tag). A `rule`, even a guard-free one, is
  never treated as an equation.

### 7.3 Compile pipeline

```text
.bwr ─lex→ tokens ─parse→ RuleIr (names resolved, sorts unified, widths linear)
     ─check→ static checks (guard monotone, purity, identity restrictions, every parameter bound)
     ─type→ every admitted width assignment well formed ─order→ KBO ─identify→ RuleId
     ─lint→ reachability through the construction canonicalizer, examples
     └─ RuleProgram (owned)   [CompileLimits bound untrusted text]
```

`RuleIr` is public and read-only (`#[non_exhaustive]` enums) so the checker, lints, SMT export and
third-party tools share one representation.

**The built-in corpus is embedded source**, compiled at run time from `include_str!`, not emitted as
generated Rust tables. Compiling it takes well under a millisecond per rule, it keeps one code path
for built-in and user rules, and there is no generated code to keep in sync. If the engine
(§6) later needs pre-built dispatch tables, they are derived from the `RuleProgram` at engine build
time. Guards are evaluated directly over `RuleIr`; a bytecode form is introduced only if the engine
measures the interpreter as a cost.

**Width validation** (BW0107) runs over a representative domain: every width for a rule with one
width variable; every width to 64 plus boundary widths up to 512 for two; every width to 16 plus
boundary widths for three. Validation is a diagnostic aid, not the safety argument: the matcher
refuses any width assignment at which the constraints fail or any part of the rule is not well
formed (the same `admitted` test the checker uses), so a width the compiler did not visit can
never produce a wrong rewrite. Validation work is bounded by `CompileLimits::max_work`, nesting
by the depth limits, width expressions by a magnitude bound, and diagnostics by
`CompileLimits::max_diagnostics`. Every width variable must be determined by the pattern (BW0102);
a `let` may use only earlier `let`s; conditions are values only under `&&`, `||` and `!`.

**Rule identity.** `RuleId` is a 128-bit hash of the normalized `RuleIr` (kind, number of width
variables, constraints, parameter kinds and widths, and every node with its sort, across pattern,
template, guard and lets), independent of name, file, position, docs and examples. The name
`group::rule` must be unique. Priority is source order within a group; there are no numeric priorities.

**Rule application** (`rules::apply`, internal) is the reference reading of a rule by the engine:
the reference matcher binds parameters and width variables (a complete backtracking search over the
operand orders of commutative nodes, with width expressions bound as soon as they have one unknown
and closed subterms such as `W - 1` compared as values once every width is bound; a step budget
bounds the search, and a search over budget is no match), the guard is answered from the
context's facts, and the template is built through the canonicalizing constructors. The engine's fast matcher (M4) is tested differentially against it.

### 7.4 Soundness gate

**Obligation.** For every width assignment satisfying the constraints and every value of the
parameters, if the guard holds then `lhs = rhs`. The checker evaluates fact predicates *exactly*
(`zero_bits(x, m)` is `x & m == 0` on the concrete value). Because fact predicates are monotone
(§7.2), any sound fact engine makes a guard true on a subset of the cases the exact reading does, so
**a rule proven this way is sound for every sound fact engine**: rule soundness and fact-engine
soundness are verified separately (§5 has its own suite).

**Evidence** (derived, never declared) is recorded per rule:

| Part | Meaning (defaults of `CheckConfig`) |
|-|-|
| exhaustive | every admitted width assignment with all widths ≤ 6 and every assignment of the parameters, when the parameters total ≤ 16 bits (`thorough()`: ≤ 8 and 24 bits; at most 40 bits are ever enumerated) |
| sampled | the widths `7, 8, 9, 12, 16, 31, 32, 33, 63, 64, 65, 96, 127, 128, 129, 192, 255, 256, 257, 384, 511, 512` (as admitted) × 64 boundary-biased points (0, 1, −1, smin, smax, powers of two, short values) from a fixed seed; half of the points are *steered* toward the guard (a `proves(y == e)` sets `y` from `e`, `zero_bits` clears the mask, `is_pow2` picks a power of two, …) |
| fired | per tier, how many checked cases satisfied the guard |
| complete | every admitted width assignment was covered exhaustively |
| SMT (feature `smtlib`) | `smtlib::rule_obligation(rule, widths)`: the negated obligation at an admitted width assignment, translated from the rule IR itself (not through the builder, whose folding would stand between the rule and the proof); `unsat` from any SMT-LIB 2.6 solver proves the rule there. Fact predicates read as the value statements they make (`zero_bits(x, m)` is `x & m = 0`). bitwright never runs a solver, so this is not recorded in the ledger; the nightly suite proves every built-in rule with z3 and with bitwuzla at up to 8 admitted assignments with widths up to 512 |

The verdict is `Sound` only when there is no counterexample, the guard held in the exhaustive
tier, and either the check is complete or the guard also held in the sampled tier; otherwise it is
`Inconclusive` with the missing tier named. This is testing, not proof: above the exhaustive
widths a rule is sampled, and a guard that only holds at values neither the boundary bias nor the
steering produces can hide a defect. Proof at wide widths is the SMT export's job. An unsound rule
yields a `Counterexample` in the expression syntax, for example
`W = 2; x = 0x0:2: lhs = 0x3:2, rhs = 0x1:2`.

The **built-in corpus** must be `Sound` with at least one guard-true case per rule, in `cargo test`.
`check::check_examples` applies each rule to its `#[example]` inputs and compares the results
(part of every `RuleCheck`, and failing `bitwright check`); every built-in example holds.
Three further tests hold every built-in rule to its engine-side reading: each `#[example]` must fire
through rule application and produce the stated result; random instances of each pattern (parameters
replaced by random subexpressions, constants biased to powers of two and masks) are rewritten and the
result is compared with the input exhaustively over its symbols; and a fixture program covers the
guard and template features the corpus does not use. The random-instance test also asserts that
every application strictly decreases the ground termination order (§6.5). These catch matcher, guard and template bugs
that the semantic obligation cannot see (each was mutation-tested with planted bugs).

**Negative fixtures.** Deliberately unsound rules (for example `sext_from_sign_word` without
`U <= 2 * W`, and a comparison merge guarded by `b <=s c - 1`, which wraps at the signed minimum)
must each be refuted with a counterexample; malformed rules must each be rejected with their code.

**The ledger.** Each built-in `.bwr` has a generated `.bwr.proof`: sorted text, one record per
`Sound` rule with its id, kind and evidence (refuted and inconclusive rules are not entered). A test recomputes it and fails on any difference, so the ledger cannot
vouch for anything that was not proven. The engine (M4) refuses to link a rule the ledger does not
vouch for, unless the builder explicitly allows unproven rules (counted in its statistics).

### 7.5 Diagnostics and lints

Diagnostics carry stable codes and byte spans, and render rustc style with `file:line:col`. Errors
are never suppressible; `#[allow(..)]` accepts only the lints marked *allowable*. `rules::explain(code)`
(and `bitwright explain`) says what each code means and how to fix it; a test fails when the
compiler emits a code without an explanation. `bitwright catalog` renders a rule file (by default
the built-in rules, `rules::builtin_sources()`) as Markdown: per group, each rule's doc comment,
text, kind (rewrite, identity directed and searchable, or search-only identity) and examples.

| Code | Level | Meaning |
|-|-|-|
| BW0001–BW0004 | error | syntax, unknown attribute, missing `bitwright 1;` header, duplicate group or rule |
| BW0100–BW0107 | error | limits, sort/width mismatch, unknown width variable, bad literal or parameter, misplaced or malformed predicate, impure mask or `let`, negated fact predicate, ill-typed at an admitted width |
| BW0302 | error | a `rule` fails the order decrease or the variable condition (it could loop) |
| BW0304 | error | an `identity` uses a guard, `let`, capture kind or extension op, or a variable on one side only |
| BW0402 | warn, allowable | unreachable: construction canonicalization rewrites every instance of the pattern (constant on the left, `ugt`, all-constant, …) |
| BW0407 | note, allowable | no `#[example]` (the built-in corpus has one for every rule) |
| BW0409 | note | an identity that does not decrease the order is eqsat-only |

Planned after 0.1: shadowing by an earlier rule, a guard never true, authored commutative
variants, width-instantiation copies, subsumption by a pass, and guard-free rules that could be
identities.

The **construction table and every normal-form pass** have their own obligation tests (exhaustive at
W ≤ 6 over generated inputs from each pass's fragment), so the gate covers every transformation the
library performs, not only rules.

---

## 8. Normal-form passes

Every pass runs in the same iterative walk as `Local` (operands first, a per-phase memo of final
results in the context), proposes a replacement for the *region* rooted at a node (the subgraph of
the pass's fragment, down to its *atoms*), and builds it through the builder.

**Commit rule: the DAG must get strictly smaller.** A candidate is committed only when the nodes it
needs (those not already in the region or atoms, counted against the structure, not against which
nodes happen to exist in the arena) are fewer than the nodes replacing the region frees. A node is
freed when every use of it comes from freed nodes, with uses counted over the live DAG of the call
(the current version of every root), kept up to date as nodes are created and replaced; the
region is bounded (the nodes nearest the root), which only under-counts what is freed. Shared
parts therefore never count as freed, so re-emitting a region that other roots still use is not a
gain. Linear, xor and bitwise candidates are costed from their form before they are built, so a
rejected candidate builds nothing. A rejection that happened only because of sharing is not final
(the sharing may disappear as other users are simplified later in the walk), so a later round
decides again; with rounds, results are idempotent. Equal-size rewrites are never made, so a pass
cannot fight the rules or another pass. Every commit then goes through the postconditions and the
host veto (§6.4). Per-node descriptions are cached for the call and derived from a node's own
structure. Work is charged to `Budget::pass_work`, fact queries to `fact_work`; `Stats::passes`
counts `{calls, noop, changed, rejected_cost, rejected, atomized}` per pass.

| Pass | Fragment and algorithm |
|-|-|
| `FactFold` | A node whose facts pin one value becomes that constant, subject to `Hooks::fold_known`. |
| `Linear` | `c + Σ kᵢ·aᵢ` over Z/2^W through `+ − neg`, `~a = −a − 1`, multiplication by a constant, left shifts by a constant, and `\|`/`^` of operands the facts prove disjoint. Coefficients are `BitVec`s, so every width to 512 works; at most 64 terms. Emitted with atoms in canonical order, positive coefficients first, power-of-two coefficients as shifts, the constant last. Cancels additive masking. |
| `Xor` | `k ⊕ ⊕ᵢ (aᵢ & mᵢ)` over GF(2)^W through `^`, `~x = x ⊕ ones`, `&`/`\|` with a constant (`x \| c = (x & ~c) ⊕ c`), and disjoint `\|`. At most 64 terms. Cancels boolean masking over any number of atoms. |
| `Bitwise` | A pure bitwise function of ≤ 3 atoms (plus 0/ones) has an 8-bit truth table, exact at every width; it is replaced by the minimum-size form from a table of all 256 functions, found by a breadth-first search over expression sizes (computed once, verified exhaustively by the tests). Variables follow the atoms' canonical order; atoms the table ignores are pruned. 4 atoms via NPN classes is a later option. |
| `Compares` | Boolean combinations of comparisons. For one operand pair: the five relations {EQ, (LTu,LTs), (LTu,GTs), (GTu,LTs), (GTu,GTs)}, each predicate a set, `& \| ^ ~` set operations, emitted when the set is one predicate, true or false (at W = 1 only three relations occur). For one operand against constants: exact unsigned interval sets (signed comparisons split at the sign boundary, at most 8 intervals), emitted as a comparison or the wrapped range check `x − lo <=u hi − lo`. Checked exhaustively at W ≤ 6. |
| `Casts` | An extract/trunc is pushed through `+ − * neg` (low bits), `& \| ^ ~` and `select` (any bits), constant shifts, extensions, `concat` and nested extracts (re-indexing, becoming 0, or extending the remaining part); the whole bounded narrowing is compared with the original region. |
| `Demanded` | An operand observed only through some bits (`& c`, `\| c`, an extract, a constant shift) is simplified under that mask: masks that keep every demanded bit are dropped, constants that settle every demanded bit replace the operand, operands whose demanded bits the facts know become constants, arithmetic demands only its low prefix, and shifts, extensions and `concat` re-index the mask. |

Added in M6 (in `Strategy::deobfuscate()`):

| Pass | Fragment and algorithm |
|-|-|
| `LinearMba` | Linear combinations of bitwise functions of ≤ 6 atoms. The operands of `& \| ^` are read as bitwise: only `& \| ^ ~`, atoms, and 0 or all-ones constants may appear there, so a linear term or a non-uniform mask under a bitwise operator is an atom, and so is a node read both ways. Atoms are ordered canonically (by structure, not node index), so the result does not depend on construction order. Every bitwise function is an integer combination of conjunctions (`AND_∅ = −1`), bit by bit and so exactly in Z/2^W, so the values at the 2^t corners where every atom is 0 or all-ones determine the expression. A Möbius transform gives the conjunction coefficients; the emission is the cheapest of the affine form (when no conjunction of two or more atoms remains), the conjunction form `c + Σ k_S·AND_S` itself (any number of atoms), and `u₀ + Σ (u₀ − uₖ)·gₖ` over the distinct corner values, `gₖ` a minimum-form bitwise function (≤ 3 atoms). Only mixed regions (linear and bitwise operators) are considered. |
| `Shuffle` | Values of ≤ 128 bits assembled from bit slices: every output bit is traced to a constant or to one bit of a source through `&` with a constant, `\|` (with constant-one bits), `^`/`+` of pieces whose traced bits do not overlap, constant shifts and rotations, extensions, `extract`, `concat` and `bswap`. A fully traced value is re-emitted as the source, a rotation, a byte swap, or a `concat` of slices and constant runs. |

Feature `deobf` keeps one planned item: a GF(2) linear-map normal form over rotations, shifts and
xors (which would also decide invertibility of maps with cyclic bit dependencies, such as
`x ^ rotl(x, a) ^ rotl(x, b)`). Mixer recognition and inversion, and the odd inverse, are in the
core (§8.1).

**Pipeline order is part of the contract:** `Strategy::deobfuscate()` is the standard pipeline with
`LinearMba` and `Shuffle` after `Bitwise`. `Strategy::standard()` is `[FactFold, Local(core), Linear,
Xor, Casts, Invert, Compares, Bitwise, Demanded, Local(core)]` for up to 4 rounds (`Invert` before
`Compares`, so comparisons it solves are combined in the same round). Measured on a 700k-node
random chain of mixed bitwise and additive steps: 2.9 s in release, linear in size; other shapes
differ, and a deep DAG can exhaust the default visit budget before the later phases run.

**Corpus.** Local rules are written fresh, carry evidence and an example, and are added only when a
measurement (a firing census on a real corpus, or a missing-simplification report) shows a need the
passes do not cover; the seed corpus is 33 rules.

### 8.1 Invertibility (`Phase::Invert`, `Query::Injective`, `Query::Bijective`)

Hash comparisons are equalities through chains of invertible maps. An expression is read as a
chain of **layers** from a subexpression (the *inner* value) up to its root; a layer is one node
that is injective in one operand when the others (its *parameters*) are fixed:

| Layer | Kind | Preimage of a constant `c` |
|-|-|-|
| `~v`, `-v`, `bswap(v)`, `bitrev(v)` | bijective | the same operator of `c` |
| `v + k`, `v - k`, `k - v`, `v ^ k`, `rotl(v, k)`, `rotr(v, k)`, any `k` | bijective | the inverse operation |
| `v * k`, `k` proved odd (constant, known bit 0, or assumed) | bijective | `c · k⁻¹` (Newton's iteration) |
| `zext(v)`, `sext(v)`, `concat(v, k)`, `concat(k, v)` | injective | the part of `c`, if `c` is an image |
| extension output declared `Invertible::{Injective, Bijective}` in an argument | as declared | `ExtOp::invert`, checked by evaluation |
| a region of nodes over a hole, recovered bit by bit (below) | injective (bijective at one width) | recovered bit by bit, checked by evaluation |

A chain of layers is injective (bijective when every layer is); nothing else is claimed. A node
whose operands both depend on the inner value is a layer only as a **region**: the nodes between it
and a *hole* (a node every varying path from it goes through), at most 256 of them, the hole at most
128 bits, over which a **pivot analysis** proves injectivity. For every bit `k` of every node it
computes `D_k`, the hole bits the bit can depend on, and its *pivots* `P_k ⊆ D_k`, the hole bits `j`
with bit `k = hole_j ⊕ φ(D_k \ {j})`: bitwise operators bit by bit (`^` keeps the pivots of each
operand that the other does not read; `&`, `|` pass an operand's bit where the other is known 1,
resp. 0), `+ − neg` from every lower bit (keeping the pivots no carry reads), a product with a
non-varying factor whose low `t` bits are known zero and bit `t` known one as the other factor's
carry chain moved up by `t`, constant shifts, rotations, casts and `concat` re-indexed, variable
shifts and rotations over every count their range allows (a rotation's counts reduced modulo the
width from their full values, never saturated) plus the count's own dependencies (no pivots), a
select by a non-varying condition keeping the pivots both arms share, everything else from every bit
of every operand; a bit the facts pin depends on nothing. The facts are computed afresh over the
region with the hole unknown (the context's facts of the hole would describe only the values it
takes in context), parameters keeping their facts. By induction over the region, two values of the
hole that agree on `D_k` give equal bit `k`, and one pivot changed alone flips it. The region is
injective when every hole bit is *recovered*: it is the only unrecovered dependency of some output
bit, and a pivot of it; equal images then force equal hole bits in recovery order, and a preimage is
recovered the same way, one evaluation of the region per level, then checked (a value that does not
check proves that no preimage exists). The criterion is monotone, so the closure finds every
recoverable bit. Candidate holes are the dominators of the varying leaves, nearest first (at most
8): one large region is not compositional (a product mixes every lower bit, so `S((x ^ k) · k)` is
proved over `(x ^ k) · k`, not over `x`). This admits the xorshift involution `h ^ ((h >>u 32) >>u
(h >>u 60))`, xorshift steps, T-functions such as `u - (((u << 1) | b) & h)`, and block-triangular
maps such as the pointer encoding `compact` (low bits a bijection of the low bits; high bits, given
those, one of the high bits), and refuses by construction `f(x) ^ x`, `f_a(x) ^ f_b(x)`, `f_a(x) |
f_b(x)` and `u - ((u | b) & h)`.

**The pass** acts only on `==` and `!=` (a bijection preserves no ordering): both sides the same
layer over different inner values with the same parameters (the same nodes; for a region, the
sides anti-unified as one function of a pair of different subterms, as deep as their structure
allows, commutative operands in either order, under a step cap, and the region taken over the
nearest dominator of that pair on side one that the analysis accepts) become a comparison of the
inner values, repeatedly; a side against a
constant is solved through every layer whose parameters are constants, down to `x op f⁻¹(c)`, or
a truth value when `c` has no preimage; `a₁ | … | aₙ == 0` and `a₁ & … & aₙ == ones` are solved
leaf by leaf and intersected (one value equal to two constants is false), and kept only when the
result is a smaller tree. Every rewrite replaces a comparison by one of proper subterms of its
operands and constants, or by a constant: like a rule it strictly decreases the termination
order, so the pass commits it whether or not the operands stay live for other users (the DAG
grows by at most the new comparison and constant), under the usual postconditions and host
veto. Facts about parameters come under the run's assumptions and fact budget, and the result
relies on the constraints they used. Analysis work is charged to `pass_work`. Measured against
the previous pipeline: +1.5 % to +2.6 % instructions on the `simplify/standard` benchmarks (one
more walk per round over DAGs with few comparisons), no change to fact benchmarks.

**Queries.** `Query::Injective { e, of }` (`Bijective`) is `True` when the chain from `e` down to
`of` is proved, reading `e` as a function of a value put in place of `of` with every value not
depending on `of` fixed; `False` when `e` does not depend on `of`, or is narrower (for
`Bijective`, of another width); `Unknown` otherwise. Under assumptions, facts about parameters are
read under them and reported as reliance.

**Facts proved elsewhere.** A finite-domain fact (say, proved by exhausting 2³² inputs) is a rule
guarded by a fact predicate that proves the domain (`if proves(x <=u 0xffffffff)`). The checker
cannot decide it (`Inconclusive`), so it is linked with `unproven_program`: the host vouches for
it, and gets sampled verification.

---

## 9. MBA (feature `mba`; cobra backend under `cobra`)

```rust
pub mod mba {
    pub struct MbaExpr { /* nodes in operand-first order over declared variables; ops Const, Var,
                            Add, Sub, Mul, Neg, And, Or, Xor, Not, Shl(k), LShr(k), Zext, Sext,
                            Trunc; per-node widths */ }
    impl MbaExpr { new, push, push_cast, eval, key /* 128-bit content hash */, shape, is_linear }
    pub struct Shape { pub vars: u32, pub nodes: u32, pub height: u32, pub mixed: bool, pub degree: u32 }
    pub fn lower(cx: &Context, e: Expr, lim: &MbaLimits) -> Result<(MbaExpr, Bindings), Error>;
    pub fn lift(cx: &mut Context, m: &MbaExpr, b: &Bindings) -> Result<Expr, Error>;

    pub trait MbaSolver: Send + Sync { fn id(&self) -> &str; fn solve(&self, p: &MbaExpr, b: &MbaBudget) -> MbaAnswer; }
    pub enum MbaAnswer { Simplified { expr: MbaExpr, claim: Claim }, NoSimpler, Unsupported(String), Exhausted }
    pub enum Claim { Unverified, Sampled, Proved, Certified }
    pub trait EquivalenceProver: Send + Sync { fn id(&self) -> &str;
        fn prove_equal(&self, a: &MbaExpr, b: &MbaExpr, b: &MbaBudget) -> Verdict; }  // Proved | Refuted | Unknown
    pub trait MbaCacheStore: Send + Sync { fn get(&self, k: &CacheKey) -> Option<CacheEntry>;
                                           fn put(&self, k: &CacheKey, e: &CacheEntry); }
    pub struct SignatureSolver;   // native, complete for linear MBA
    pub struct NormalFormSolver;  // native normal forms: linear, semi-linear, polynomial MBA, atoms
    pub struct NativeProver;      // bitwright's own certificates as an EquivalenceProver
    pub struct MemoryCache;       // bounded, oldest evicted first
    pub struct NoCache;
    pub struct MbaConfig { pub limits: MbaLimits, pub trust: MbaTrust, pub budget: MbaBudget }
    pub struct MbaTrust { pub backend_certificates: bool /* default true */, pub sampled: bool /* default false */ }
}
// EngineBuilder::mba_solver(Arc<dyn MbaSolver>), ::mba_prover(..), ::mba_cache(..); Phase::Mba(MbaConfig)
```

- **Placement.** `Phase::Mba(config)` runs in the same bottom-up walk as the passes, so innermost
  fragments are solved first and their parents are then asked over the simplified children. A
  fragment is `+ − * neg & | ^ ~`, constant shifts below the width, extensions and truncation;
  anything else is an atom (a variable of the `MbaExpr`). Only mixed fragments (arithmetic and
  bitwise) within `MbaLimits` (variables, nodes, width, a minimum size) are asked about.
- **Gate.** An answer must have the input's variables and width, agree with the input at 64
  points (a refutation check that always runs: zero, all-ones, one and the signed minimum, the
  constants of both sides with their neighbours `c ± 1`, `−c`, `~c`, points whose set bits lie
  at one position, and seeded random points), and carry exact evidence, in this order:
  bitwright's own certificates (below), a configured `EquivalenceProver`'s proof, the
  backend's `Proved` or `Certified` claim if `trust.backend_certificates` (the default), or
  agreement at the sampled points only if `trust.sampled`. The lifted result must then agree
  with the original expression at seeded symbol values (this checks lowering and lifting,
  which no proof about the lowered form can), make the DAG smaller (§8), and pass the
  postconditions and the host veto (§6.4). **Trusting backend certificates means trusting the
  backend**: an answer wrong at a point no sample reaches is caught only when bitwright's own
  evidence applies; hosts that need independence set `backend_certificates: false`. The
  gate's own evaluations (sampling and certificates, in blocks of 256 points on a compiled,
  batched evaluator) are charged to `Budget::pass_work`, so a budget or deadline can stop
  them; a certificate larger than what is left is not started, and the node stays non-final
  (more budget may prove it). An answer refuted after lifting leaves no live nodes behind.
- **Certificates** (`mba::certify`, also `NativeProver`). Each is a finite evaluation test,
  complete for its fragment, sized before it runs; the cheapest that applies is run.
  - *Signature*: linear MBA with only 0 and all-ones constants inside bitwise parts is
    determined by its 2^t corner values.
  - *Sparse points*: a **polynomial MBA** is built with `+ − · neg ~ <<k` and constants over
    bitwise functions of the variables (`& | ^ ~` of variables and constants); its syntactic
    degree `d` is the most bitwise factors in a product (a variable counts 1, a constant 0).
    Writing each variable as `Σ_j 2^j·x[j]` makes the difference of two sides an integer
    polynomial in the input bits (reduction mod 2^W is a ring homomorphism, so carries need no
    care); after `b² = b` it is multilinear and each monomial touches at most `d` bit
    positions, one per factor. Multilinear representations over a commutative ring are unique
    and Möbius inversion recovers each coefficient from points supported inside its monomial,
    so the sides are equal iff they agree wherever the set bits of all variables together lie
    in at most `d` positions: `Σ_{k≤d} C(W,k)·(2^t − 1)^k` points (99,233 for `W = 64`, three
    variables, `d = 2`). Degree 1 is the semi-linear test (`1 + W·(2^t − 1)` points).
  - *Grid*: without `& | ^`, two polynomials of degree `≤ d_i` in variable `i` are equal iff
    they agree on `Π_i {0..d_i}` (forward differences give `α!·h_α` for the falling-factorial
    coefficients, and `(x)_k` is a multiple of `k!`).
  - *Exhaustive*: when the variables total at most 20 bits.
  - *Compositional*: when a side leaves the polynomial fragment, right shifts, casts and
    arithmetic read by a bitwise operator become **atoms**. Both sides are merged into one
    hash-consed DAG (commutative operands ordered), every node is evaluated at the refutation
    sample, and atoms are put in classes of nodes proved equal: by structure, by congruence
    (`f(a) = f(b)` when `a` and `b` are), and by comparing their definitions' skeletons with a
    test above (operands first, among nodes that agree at the sample). The roots' skeletons,
    with one variable per class (the variable itself when a class contains one), are then
    compared by a direct test; an identity over independent atoms holds for any values of
    them. Skeletons that differ only prove nothing (`Unknown`); `Refuted` always comes with a
    real input where the sides differ. Every class is cross-checked against the sample; a
    disagreement would be a bug and declines.

  The degree-`d` test was derived for this design and is confirmed by exhaustive tests at
  `W ≤ 6` in both directions, with every test also run on its own; planted wrong answers
  (corner-invisible products, terms nonzero only when three different positions are set,
  point functions) are never proved at any width.
- **The normal-form solver** (`NormalFormSolver`, id `bitwright.nf.v1;…` with its options).
  One pass over the question, operands first, gives every node the normal form of the smallest
  fragment containing it; *atoms* are the variables and every subterm the fragments cannot see
  through. The first version takes one width (nodes of other widths only below casts, which are
  atoms rendered as they are).
  - *Bit classes.* The constants read by `& | ^` partition the positions: `j ~ j'` when every
    such constant has the same bit at both (0 and all-ones never split). Inside a class every
    bitwise subterm is one Boolean function, so a bitwise function of atoms is a **truth table
    per class** (at most 12 atoms each), combined bit-parallel.
  - *Masked conjunctions.* Möbius over a class's table writes the function as
    `Σ_T a_T·(AND_T & M_c)` exactly at every width (`AND_∅ & M_c = M_c`). A linear combination
    of bitwise functions is a polynomial of degree 1 over the symbols `m_{c,S} = AND_S & M_c`;
    `m_{c,S}` is a multiple of `2^τ_c` (`τ_c` the class's lowest position), so its coefficient
    matters modulo `2^(W−τ_c)`, and reduced there (signed) the form is canonical: two class
    corners per class and atom set determine it.
  - *Recognition.* A degree-≤1 form is a bitwise function exactly when, in every class, the
    constant's bits there are all 0 or all 1 (`k_c`) and `k_c + Σ_{∅≠S⊆p} γ_{c,S}` is 0 or 1
    modulo `2^(W−τ_c)` at every corner `p`; that is the table.
  - *Rendering.* Candidates are built into one builder with local interning and costed by the
    nodes their root reaches; the cheapest wins (then by an operator-weighted size, then by
    structure), and only if it is strictly smaller than the input (else `NoSimpler`). A
    degree-≤1 form renders as a bitwise function when it is one (the minimum-form table for at
    most three atoms, the algebraic normal form, `((g ^ A) | B) & ~C` over classes whose tables
    are `g`, `¬g`, all-ones and zero, or the or of masked groups), and otherwise over *groups of
    classes* whose coefficient vectors can be chosen equal (each only defined modulo its
    class's precision): per group the cheaper of the masked conjunction form and the masked
    indicator form `b·M + Σ_{v≠b} (v − b)·(g_v & M)` over the distinct corner values `v`. A mask
    covering every position disappears. Sums put positive coefficients first, powers of two as
    shifts, and choose each sign so a constant already needed is reused.
  - *Self-check.* The chosen answer is certified against the input (§ Certificates) within the
    solver's remaining budget: `Claim::Proved` when a certificate ran, `Claim::Sampled` when
    none fit but the refutation sample agrees (the gate then decides on its own evidence).
    Budget exhaustion before an answer is `Exhausted`; every decline is counted
    (`NfStats`: fragments reached, atoms, candidates, certificates, declines by reason).
  - On linear MBA it is never costlier than `SignatureSolver` (tested on random linear MBA at
    widths 1 to 128: its conjunction form is one of the candidates, emitted more tightly).
- **Caching.** Keys hash the lowered input, the solver and prover ids, the trust setting, and the
  lowering version. A solver's id must record everything that changes its answers (`CobraSolver`'s
  records its options and `max_vars`). Only results accepted by the gate under the key's trust
  setting and complete `NoSimpler` answers are stored, so an answer accepted on the backend's word
  or on sampling is never reused where that evidence is not accepted; `Exhausted` is never stored and
  leaves the node non-final (a later call with more budget asks again). bitwright performs no file
  IO; `MemoryCache` and `NoCache` ship, and persistent stores belong to hosts.
- **Budget and telemetry.** `Budget::mba_calls` bounds solver calls (`Exhausted::MbaCalls`);
  `Stats::mba` counts calls, cache hits, simplifications, no-simpler, unsupported, exhausted,
  refuted, proof-unknown and not-smaller answers, and refusals (too many variables, too large, too
  wide, too small).
- **cobra 0.4** (feature `cobra`, Apache-2.0). `CobraSolver` takes expressions of one width of at
  most 64 bits and at most `max_vars` variables (no casts), lowers `Sub` to `a + (−b)` and
  `Shl(k)` to `· 2^k`, calls `cobra::simplify_expr`, maps the result back with
  `outcome_expr_in_original_space`, and reports cobra's proof level as the `Claim`
  (`LeanCertified` → `Certified`, `SmtProved` → `Proved`, `SpotChecked` → `Sampled`). cobra's
  "unchanged" answer is a cached `NoSimpler` (cobra is deterministic for given options, which the
  id records); a panic inside cobra is caught and answered as unsupported. With cobra's default of requiring a Lean certificate, measured here: linear MBA is
  simplified and certified; a degree-2 identity comes back unchanged. cobra 0.4 exposes no
  caller-visible budget, so `ThreadedSolver<S>` (for any solver) runs each question on its own
  thread with a hard wait deadline: a late answer is abandoned as `Exhausted` (never cached, the
  node stays non-final), and new questions are refused while `max_abandoned` abandoned ones are
  still running (checked before each question starts, so concurrent callers may briefly exceed it).
  A panic in the wrapped solver is answered as unsupported and never counts as abandoned. The
  threads are the instance's own; nothing is global. The planned upstream
  change is to expose cobra's orchestrator policy in its `Options`.

---

## 10. Equality-saturation search service (feature `eqsat`, default off)

**Position.** A bounded *alternative-expression search* over immutable graphs. It is **not** a phase
and never runs inside `Engine::run`. The host decides when (output or checkpoint boundaries, never
routine maintenance), which roots, and which allowance. An extracted expression is a **candidate**
that the host's own profitability and verification gates decide to publish.

```rust
pub mod eqsat {
    pub struct Saturator { /* Arc: admitted equations as e-patterns, config, epoch */ }
    impl Saturator {
        pub fn new(programs: &[(&RuleProgram, &Ledger)], groups: &[&str], cfg: SaturateConfig)
            -> Result<(Saturator, AdmissionReport), BuildError>;
        pub fn builtin(cfg: SaturateConfig) -> (Saturator, AdmissionReport);   // eqsat.bwr, every group
        pub fn builtin_groups(groups: &[&str], cfg: SaturateConfig) -> (Saturator, AdmissionReport);
        pub fn search(&self, cx: &mut Context, batch: &[Expr], run: SearchRun<'_>) -> Result<SearchReport, Error>;
    }
    pub struct SaturateConfig { pub fragment: Fragment, pub iterations: u8 /*8*/,
        pub matches_per_rule_iter: u32 /*16*/, pub admission: Admission, pub max_root_nodes: u32,
        pub unsupported: UnsupportedPolicy /* Decline (default) | Atomize (opt-in) */ }
    // SaturateConfig::default() (conservative) and ::exploratory() (16 × 64, for larger budgets)
    pub struct SearchRun<'a> { allowance, per_call: Option<Budget> /* 2048 e-nodes, 100 000 work */, deadline }
    pub struct SearchReport { pub roots: Vec<SearchRoot>, pub publication: Publication, pub stats: EqsatStats }
    pub enum RootEnd { Saturated, IterationCap, Stopped(Exhausted), DeclinedUnsupported, DeclinedAdmission(Cap), Memo, Skipped }
    pub enum Publication { Published, Withheld { cause: RootEnd } }
}
```

**Equations** (conservative admission, once, in `Saturator::new`): proven by the program's ledger,
exactly one width variable and no width constraints, homogeneous in that width, no guard or `let`,
every operator in the fragment. `identity` items are used in both directions; guard-free `rule`s
(with only unconstrained parameters) in their authored direction only, since their right side may
drop variables: this is how cancellations such as `(x + y) − y → x` enter, which no identity can
express. Inside the e-graph nothing canonicalizes, so the built-in equations (`eqsat.bwr`, with its
own ledger) include forms the arena builder folds on its own. They come in groups a host selects
per search (`builtin_groups`): `eqsat.assoc`, `eqsat.distrib` (`*` over `+`), `eqsat.distrib_and`
(`&` over `|` and `^`), `eqsat.distrib_or` (`|` over `&`), `eqsat.negation` (De Morgan and
negation) and `eqsat.cancel`. Groups exist because publication needs saturation (below) and some
combinations never saturate: `distrib_and` with `distrib_or` rewrite each other's results without
end. For the same reason there is no MBA group: equalities such as `x ^ y = (x | y) − (x & y)`
produce, in both directions, terms the others match again, so a search over them never
saturates; linear MBA belongs to the `LinearMba` pass and the MBA service (§8, §9). The `AdmissionReport` lists every rule and why
it was or was not admitted. `Fragment::conservative()`: widths 1..=128, homogeneous per root,
operators {constant, symbol, `+ − * & | ^`, unary `−`, `~`}.

**Inputs**, per root, before import: O(1) height and tree-size caps, then a bounded fragment and
homogeneity check (at most `max_root_nodes` distinct nodes, and at most
`Admission::max_root_dag_size` when that is set). Out-of-fragment roots are
`DeclinedUnsupported`, oversized ones `DeclinedAdmission`; nothing is built for them.
`UnsupportedPolicy::Atomize` (maximal out-of-fragment subterms become opaque atoms) is sound under
total semantics but stays opt-in until validated on real workloads.

**E-graph.** In-crate, iterative, deterministic: classes in insertion order; union by lower id with
path compression; a hash-cons of canonical e-nodes (commutative operands sorted by class id; the
matcher tries both orders, so no commutativity equations exist); deferred rebuild through a
worklist with congruence repair; constant folding. **A union of two different constants is a
contract violation** (`Error::Contract`): only an unsound equation can cause it.

**Schedule.** Per iteration: e-match every equation (and direction) in program order over the
canonical classes in ascending id (backtracking; repeated variables compare `find()`), taking up
to `matches_per_rule_iter` *new* matches (matches already applied, canonicalized, do not count, or
an early redex would starve every later one), apply them in collection order (instantiate the
other side, unite), rebuild. The matcher stops enumerating as soon as it has the matches it may
look at, and an equation whose quota is spent stops being matched once saturation is ruled out.
A root is `Saturated` only when an iteration changed nothing and no equation had more new
matches than it took (matches already applied are skipped before they count, so a class with
many applied matches cannot look unsaturated forever). Every insertion, match step, union, repair and extraction cost step is
charged to the caller's allowance (`Budget::eqsat_nodes`, `eqsat_work`) before it is done, so a
search never spends past its limit or its allowance, and never refunded; every charge also counts
toward the deadline's clock reads (`Deadline::check_every`). Building the chosen candidate, its
bounded DAG-size comparison and the sampled agreement check are bounded by the admitted root size
and are not charged.

**Extraction.** Positive tree-size cost by iterative fixpoint from ∞, so cyclic classes are handled
and the selection is acyclic. Ties keep the original imported e-node, then the lowest index. A
candidate must be strictly cheaper as a tree, no larger as a DAG (bounded), and agree with the
input at 32 seeded symbol vectors (a mismatch is `Error::Contract`: an unsound equation linked with
a forged ledger is reported, never published). It is built through the owning context's builder.

**Publication is transactional per batch.** Each root is searched in its own graph (a root's result
does not depend on its batch-mates), sharing only the allowance. The batch is `Published` only if
every searched root saturated; roots declined at admission do not spoil it. Reaching the iteration
cap, a budget or a deadline yields `Withheld { cause }`: the rest of the batch is not searched (a
budget stop reports the remaining roots as stopped, the others as `Skipped`), and every candidate
of a withheld batch is `None`. The deadline is also read once before the batch, so a deadline
already passed withholds even answers the memo would give. Allocations already made stay in the append-only arena (logical
rollback only), and spent allowance stays spent. Measured over 2,000 random fragment roots
(depth 5, widths 1..=64) under the default configuration and budget: with every group, 79 %
saturate, 21 % reach the iteration cap and 1 root stops on the budget; with the groups other than
`distrib_or`, 90 % saturate; with `distrib` and `cancel`, 99.7 %. A tenfold budget changes none of
these, so the defaults match each other. `SaturateConfig::exploratory()` searches longer (16
iterations of 64 matches) for hosts with a larger allowance.

**Memo.** Per `(root, saturator epoch)` in the context: saturated searches and admission declines.
Never an incomplete search (the iteration cap, a budget or a deadline). A context holds one epoch at
a time, so alternating two saturators over one context re-searches.

**Stats.** Roots declined (unsupported, admission), saturated, iteration-capped,
budget-terminated, answered from the memo, changed; e-nodes inserted, work charged, unions,
iterations, withheld batches. Unproductive search is measured, not hidden.

The fragment grows only with its own validation, one step at a time (constant shifts as scaling, typed
casts, compares), each with new admission tests.

---

## 11. Stability

- The crate stays 0.x until the API has been used in production for a release cycle. MSRV 1.88; raising
  it is a minor-version change. `cargo-semver-checks` runs in CI.
- Every public enum and configuration struct is `#[non_exhaustive]`, and so is every record the
  library returns (outcomes, reports, diagnostics, the rule IR). The one exception is a closed
  set: `Truth` (true, false, unknown). Configuration structs have `Default` (or a constructor, as
  `Deadline::new`) and a `with_*` setter per field, so other crates build them without struct
  literals; `tests/api.rs` compiles only while that holds. Types whose invariants matter have no
  public fields.
- **Result stability** is its own contract, because users snapshot printed output: patch releases never
  change simplification results except to fix unsoundness (named in the changelog by rule id); minor
  releases may, and list them under "Behavior changes" with a corpus diff. The `OrderKey` hash and the
  printer format change only in minor releases. The rule-language edition (`bitwright 1;`) is frozen
  within a major version.
- `unstable` (feature) exposes matcher internals and the static program layout without semver.

---

## 12. Validation

1. **Reference evaluator.** Kernels (native path and limb path separately) are compared with
   `bitwright-ref` exhaustively for every operator at W ≤ 8 (unary ≤ 10; casts across widths
   included); at boundary-biased random points at 23 widths straddling every limb edge (150 samples
   per width per pull request, 20,000 nightly); and at every width 1..=512. The generator produces
   values with random significant lengths so multi-limb divisions of every shape occur. Nightly:
   random terms exported to SMT-LIB and evaluated by z3 and bitwuzla, and every built-in rule's
   obligation proved by each of them at widths up to 512 (feature `smtlib`).
2. **Construction.** Every stored node is canonical and a fixed point of the builder;
   child-before-parent holds; padding is canonical; the **construction table** (every operator over
   every operand shape — symbols, special constants, and the composites the rules look through — at
   W ≤ 3, checked on every assignment) and random trees agree with the reference; building the same
   expression in shuffled orders in two contexts prints identically. Planted canonicalization bugs
   are used to check that the suite catches them.
3. **Facts.** For random DAGs, the evaluated value lies within the facts; `prove` never contradicts a
   counterexample; transfers exhaustive at W ≤ 4 over all known-bit input states.
4. **Rule gate** (§7.4): semantic obligation, compiled check, negative fixtures, ledger verification,
   ledger freshness, examples fire, every corpus application decreases the ground order, lints clean.
5. **Passes.** Each pass's obligation test is exhaustive at W ≤ 6 over its fragment's generators; the
   comparison lattice and range emitter exhaustive at W ≤ 8; the bitwise table at W = 1 (complete).
   Invertibility: every region the analysis accepts is checked to be injective, and every
   preimage (or its absence) exact, over all values at W ≤ 6, for `v ⊙ g(v)` forms (also for
   inner values with narrow facts) and for random block maps (disjoint joins of transformed
   halves, `concat` of extracts, carries through comparisons, selects, and non-injective decoys);
   an 8-bit `compact` with symbolic parameters is proved and checked at 64 parameter values;
   every cancellation, primitive or by region, against every assignment of both inner values and
   a parameter at W ≤ 4, including near misses (`g₂` not quite `g₁` over `v₂`); every
   `Injective` answer, `True` and `False`, against every assignment. Planted analysis bugs (a
   dropped carry, a pivot kept across `^` from a read bit, an even multiplier, a factor's low
   zeros miscounted, a select by a varying condition, two open bits recovered at once, a count's
   range ignored, an unchecked preimage, facts of the hole from context, a non-dominating hole)
   are each caught.
6. **Engine properties** over random DAGs with sharing (explicit seeds, biased to MBA, casts and
   compares): value preservation against the reference; idempotence of `Completed`; determinism
   across runs and construction orders; budget safety (every budget from 0 upward: no panic, sound
   roots); memo safety (a truncated run followed by a full run equals a single full run); allowance
   accounting (per-call spends sum to the total; withheld work is not refunded); every cell of the
   outcome matrix reachable and counted.
7. **Search-service regression categories:** expansion before cancellation (`x*(y+z) − x*y → x*z` only
   through `mul_distrib`, while the directed engine provably leaves it unchanged); repeated-variable
   e-class matching; cyclic classes with acyclic extraction; width and arithmetic boundaries;
   unsupported inputs declined and never atomized by default; deep graphs (10^5-deep chains) and heavy
   sharing with no recursion and bounded work; budget exhaustion and batch rollback; stale handles and
   memo entries after `clear()`; duplicate and unsorted roots; early rejection of oversized inputs with
   no allocation proportional to the input (allocation counter); before/after against the reference.
   The same categories apply to `Engine::run` where meaningful.
8. **Fuzzing:** the expression parser, the rule compiler (text and mutated IR), SMT import, `run` on
   arbitrary byte-encoded DAGs, and the static program validator; every target asserts no panic and
   sound results.
9. **MBA:** adversarial backends (a solver that lies must never get a result through); lowering/lifting
   round trips with casts, exhaustive at small widths.
10. **Benchmarks** (criterion): construction throughput, fact queries, local-phase throughput, decline-
    memo re-simplification, each pass, growing-chain workloads whose cost must stay linear in new
    nodes, search on productive **and unproductive** workloads, solver round trips. Every benchmark
    reports declined and unsuccessful work alongside successes. Performance claims are paired
    before/after measurements from the same build.

CI: stable and MSRV `check`; feature matrix; clippy `-D warnings`; rustfmt; docs; `cargo publish
--dry-run`; the gate; fuzz smoke; `cargo deny` (MIT, Apache-2.0, BSD-style, Unicode licenses only).

---

## 13. Milestones

| M | Deliverable | Exit criterion |
|-|-|-|
| M0 | Workspace, CI, `bitwright-ref`, `Width`/`BitVec` with u64/u128/limb kernels for every operator | kernels ≡ reference, exhaustive W ≤ 8 + boundary random to 512 |
| M1 | `Context`, handles, builder, canonicalization, `OrderKey`, symbols, metadata, views, maps, eval, substitute, `dag_size`, growth counters, text parser and bounded printer | construction invariants; order independence; 10^5-deep chain; `parse(print(e)) == e` |
| M2 | Facts: KnownBits, ranges, transfers, reduced product, `prove`, `exact`, `enumerate_values`, assumptions, providers | fact soundness suite |
| M3 | Rule language: lexer, parser, typer, `RuleIr`, KBO, lints, runtime compiler, reference matcher and application, checker (evidence, ledger), seed corpus, negative fixtures | gate green; every negative fixture rejected |
| M4 | Engine: `Engine`/`Strategy`/`Run`/`Outcome`, ledger linking, dispatch net, `Local` phase, `Allowance`/`Budget`/`Deadline`, admission, memo, `Stats`, `Observer`, `Hooks`, postconditions (`Verify`) | engine properties; outcome matrix |
| M5 | Passes (§8) with obligations; `Strategy::standard`; **release 0.1.0** | pass suites; masking and comparison fixtures |
| M6 | MBA module, `LinearMba` and `Shuffle` passes, `Strategy::deobfuscate`, `CobraSolver`, `ThreadedSolver`, cache traits; release 0.2 | adversarial-backend tests; MBA-identity fixtures; public MBA identity catalog accepted with exact evidence |
| M7 | Equality-saturation service with the §12.7 categories; release 0.3 (still default-off) | category suite; unproductive-search benchmark |
| M8 | SMT-LIB import/export, `bitwright-cli`, mdBook, rule catalog, fuzzing in CI, semver baseline | docs complete; fuzz clean |

---

## 14. Risks and open questions

1. **Matcher speed.** The engine currently applies rules with the reference matcher behind the
   dispatch net. Measured on a 700k-node DAG with 33 rules: about 380 ns per node visit (release),
   linear in size, and a repeated run is a memo lookup. A specialized, allocation-free matcher,
   differentially tested against the reference one, is the lever if profiling asks for it.
2. **The order may reject useful canonicalizing rules.** Precedence orients equal-weight rules; the rest
   become passes or eqsat-only identities.
3. **Coverage.** Replacing a large rule corpus by passes and a small corpus is a bet that must be
   measured; rules are added from firing censuses and missing-simplification reports, not guessed.
4. **Total division and host expectations.** A host that forgets trap guards can lose a fault. The
   `traps` helpers, the integration guide and host-side regression tests are the mitigation.
5. **Exhaustive checking cost** (a 3-variable rule at W = 8 is 2^24 cases): W ≤ 6 on pull requests,
   W ≤ 8 nightly, parallel across rules; the ledger means users never pay this at build time.
6. **cobra's internal wall clock** until the upstream change lands (contained by pre-filtering,
   `catch_unwind` and `ThreadedSolver`).
7. **The search service may never pay for itself.** It stays default-off, provisional, boundary-only and
   measured (including no-op cost) until an end-to-end benefit on a real workload is shown.

Open questions: 4-atom `Bitwise` via NPN classes; wrapped ranges (`CRange`) instead of the plain pair;
eager (construction-time) application of a small rule tier; `no_std + alloc`; an egglog export of
`identity` items; DAG-aware extraction cost for the search service.

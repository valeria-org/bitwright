# Proposal: bitwright inside a compiler, translation and rewrites at compiler speed

Status: in progress. Steps 1 and 2 of the order of work are done, and steps 3 and 4 in part
(see there): the workload is the benchmark group `compile/*` (`cargo run --release -p
bitwright-bench -- compile`), and `Strategy::compile()` is the engine tier. The numbers below
were measured before step 2, on a shared cloud VM (Intel Xeon at 2.8 GHz, Rust 1.94), not on
the reference machine of `docs/benchmarking.md`. Use them for ratios, not as reference
numbers.

## The operating point

bitwright is tuned for a binary analyzer or deobfuscator. Such a host has a few large
expressions, wants the smallest answer, and can wait milliseconds for it. A compiler has
different needs:

- **Many small units.** It simplifies every value of every function, 10^4 to 10^7
  instructions per compilation.
- **Mostly clean input.** Most of those instructions are already simple, and the engine must
  find the few that are not without paying much for the rest.
- **A tight budget per instruction.** An instcombine-style pass has roughly 20 to 200 ns per
  instruction for everything: translating in, matching, rewriting and translating back.
- **Two-way translation.** The IR arrives as Rust data, not text, and results must go back
  into that IR.

This proposal looks at three layers: translation (IR in, IR out), rewrite actions (rules and
host-defined rewrites), and the engine tier that drives them.

## Measurements

The workload is one function of *N* SSA instructions over four 64-bit parameters. Operands
are drawn from the last eight values. The operations are add, sub, and/or/xor, shifts and
products by constants, `select` over a comparison, and a truncate-extend pair. About 1 in 6
instructions carries a peephole opportunity (`(a + c) − c`, `(a ^ b) ^ b`). The function is
built through `Context::bin` and friends, with no text. Every SSA value is a root of one
`Engine::run` call. The context is reused across functions with `Context::clear`. Costs are
per instruction:

| N | build (API) | rules only¹ | rules only, re-run² | `Strategy::standard()` | standard, re-run² |
|-|-:|-:|-:|-:|-:|
| 50 | 244 ns | 2.4 µs | 154 ns | 25.6 µs | 11.4 µs |
| 100 | 177 ns | 2.5 µs | 157 ns | 54.7 µs | 39.0 µs |
| 200 | 203 ns | 2.0 µs | 126 ns | 110 µs | 93.0 µs |
| 400 | 165 ns | 1.6 µs | 122 ns | 120 µs | 105 µs |

¹ `Strategy::new("local", vec![Local(core groups)])`, one round.
² The same roots run again in the same context, where the memo should answer.

For comparison, a bare hash-consing table over the same 16-byte node layout (hashbrown, a
two-multiply mix, commutative operands ordered, no validation and no canonicalization) builds
this workload at **35 ns per instruction**.

## Where the time goes

Callgrind on the two engine configurations:

**The standard strategy grows with function size.** The demanded-bits pass is 60 % of all
instructions and the linear pass 27 %. Two causes compound:

- **Region walks per node.** `demanded::simplify` walks up to `MAX_VISITS = 256` nodes below
  each node it visits, and its (node, mask) memo lives for one step only. Every root therefore
  walks its own cone again.
- **Non-final results.** The commit rule (`finish` → `shrinks` → `dying_in`) weighs sharing
  across the call's roots, so a pass result depends on which roots were passed. Such results
  are not stored as final. Re-running the same roots in the same context did 134 more
  rewrites and cost 45–88 % of the first run, the larger share for larger functions.

With every SSA value a root, total work is roughly quadratic in function size. A compiler
naturally passes exactly that shape, so this is the first thing to fix. It is a property of
the tier, not a bug: the same design gives smaller answers on deobfuscation inputs.

**The rules-only strategy is linear but heavy per node.** It takes about 750 ns per node
visit:

- **Rule application is about 60 % of `Engine::run`.**
  - The backtracking matcher (`matcher::solve`) is about 28 %. Every candidate allocates
    `Bindings` and a `todo` Vec, and a commutative node clones the whole `State`.
  - Guards are about 24 %, almost all of it computing facts (`operand_facts` →
    `compute_facts_cap`) for `zero_bits`, `disjoint` and similar.
  - `width_values()` builds a fresh `Vec<u16>` about 5 times per candidate.
  - Constant parameters are gathered into a `Vec<BitVec>` (72 bytes each).
- **malloc, realloc and free are about 17 % of the program.**
- **Each `run` builds a new `Runner`.** That is about ten `IdMap`s plus pass scratch resized to
  the whole arena length. Most of the 120–150 ns per root of a fully memoized re-run is this
  setup.
- **The built-in corpus is compiled from source on first use.** That is about 200 million
  instructions (lexing, parsing, width validation over the representative domain), once per
  process. It is a one-off cost, but a compiler binary pays it on every invocation.

**Construction is 5–7 times the floor.** One `cx.bin(op, a, b)` pays for:

- two handle validations;
- `const_val` probes, of which `is_ones` builds a 72-byte `BitVec`;
- an `order()` call for commutative operators;
- about four `mix64` calls;
- a hashbrown probe;
- and on a miss, two pushes and an insert.

It also returns a `Result` whose `Error` carries `String`s, and none of the public builders
is `#[inline]`. A repeated `cx.symbol(key)` pays a SipHash lookup (`symbols.rs`, std
`HashMap`), even for `SymbolKey::U64`.

## Layer 1: translation, IR in and IR out

Today the front ends (`lift::pcode`, `lift::vex`, `lift::llvm`) read text. That is right for
tools and wrong for a compiler, which already holds its IR as Rust data. Parsing costs
16 µs per 60 nodes, which is 50–100 times the whole per-instruction budget.

### 1a. A `Semantics` trait, and a derive for it

The host describes what each instruction means, once, in its own crate:

```rust
/// The meaning of a host instruction as bitwright expressions.
pub trait Semantics {
    /// The host's value handle (an SSA id), dense so the value map is a vector.
    type Value: Copy + Into<u32>;
    /// The result of this instruction, over its operands' expressions.
    fn lower(&self, lw: &mut Lowering<'_, Self::Value>) -> Result<Expr, Error>;
}

// Host code: a value defined outside the region becomes a symbol keyed by its id
// (`SymbolKey::U64`, no string); one defined inside is read from a dense map.
impl Semantics for Inst {
    type Value = ValueId;
    fn lower(&self, lw: &mut Lowering<'_, ValueId>) -> Result<Expr, Error> {
        match *self {
            Inst::Add(a, b) => { let (a, b) = (lw.get(a)?, lw.get(b)?); lw.cx().add(a, b) }
            Inst::SMin(a, b) => { /* select(a <s b, a, b) */ }
            Inst::Crc32(a, b) => { let (a, b) = (lw.get(a)?, lw.get(b)?); lw.ext1(CRC32, &[a, b]) }
            Inst::Call(..) => lw.opaque(self.result()),   // a fresh symbol
        }
    }
}
```

Most hosts will not want to write that match by hand. A derive in a separate, optional crate
(`bitwright-macros`) keeps `syn` out of the core crate, whose only dependency is
`hashbrown`:

```rust
#[derive(bitwright::Semantics)]
#[bw(value = ValueId, width = self.ty().bits())]
enum Inst {
    #[bw("a + b")]                    Add { a: ValueId, b: ValueId },
    #[bw("select(a <s b, a, b)")]     SMin { a: ValueId, b: ValueId },
    #[bw("rotr(a, k)")]              RotR { a: ValueId, k: ValueId },
    #[bw(ext = "acme.crc32")]         Crc32 { a: ValueId, b: ValueId },
    #[bw(opaque)]                     Call { .. },
}
```

The expression is the `.bwr` / text syntax (§7.1), parsed at compile time by the same parser.
That parser would move into a small `bitwright-syntax` crate so the macro can use it. The
macro emits direct builder calls with no parsing at run time. The same annotation can drive
three more things:

- **Raising.** Each variant's expression is also a pattern that turns a node back into that
  instruction (1c).
- **A contract self-test.** If the host implements `fn eval(&self, args: &[u64]) -> u64` for
  its instructions, a generated `#[test]` checks it against bitwright's semantics at a
  battery of widths and values. This is what `ext::check` does for `ExtOp`, and it catches a
  wrong `#[bw(...)]` annotation before it produces a wrong rewrite.
- **Target operations** that bitwright does not model become `ExtOp`s. That is the existing
  runtime extension mechanism, and it needs no change.

### 1b. The builder's fast path

These changes need no API change, or only additions. The measured floor says construction can
come down from about 200 ns to well under 100 ns per instruction; canonicalization stays, since
matching relies on it.

- **Keep `Result<Expr, Error>` small.** Box the cold payloads of `Error` (the `String`s and
  `SymbolKey`s) so the `Result` fits in two registers.
- **No 72-byte `BitVec` for constants of 64 bits or fewer** in the canonicalizer's probes.
  `small_const` already exists; `is_ones` and folding checks should use it too.
- **A dense or integer-hashed symbol index for `SymbolKey::U64`**, in place of SipHash on
  every call.
- **`#[inline]` on the thin public builders** (`bin` → `c_bin`), or a documented
  recommendation of LTO. Every call from the host crate is a real call today.
- **`Context::with_capacity` / `reserve`**, so a host reusing one context per function never
  reallocates.
- Optionally, **branded handles**: `cx.scope(|s| ...)` hands out `Expr<'id>` with an
  invariant lifetime, so a stale or foreign handle does not type-check. The per-call tag
  compare then disappears, with no `unsafe` needed. This is only worth it if the benchmark
  shows the compare matters after the items above.

### 1c. Raising results back into the host IR

```rust
pub trait Raise {
    type Value: Copy;
    /// A host value already computing `e` (a value that was lowered to it), if any.
    fn existing(&self, e: Expr) -> Option<Self::Value>;
    /// Emits a host instruction for `e` over operands already raised.
    fn emit(&mut self, cx: &Context, e: Expr, view: View, ops: &[Self::Value])
        -> Result<Self::Value, Error>;
}
// cx.raise(roots, &mut r): a post-order over the roots' cones that stops at `existing` hits.
```

"Equal `Expr` ⇒ equal value" is already a documented contract (§4.1), so this gives the host
value numbering for free. A simplified value that hash-conses to an existing node is replaced
by that node's host value, and only nodes that are really new are emitted. The `Semantics`
derive can generate `emit` from the same patterns, as a match over `View` built at compile
time.

## Layer 2: rewrite actions

There are three ways to define rewrites, and they cover different needs. The first two share
one middle end.

### 2a. Rules compiled to Rust at build time (recommended)

Proposed: a `bitwright-rulegen` crate, called from the host's `build.rs`:

```rust
// build.rs
bitwright_rulegen::Rules::new("rules/peephole.bwr")
    .ledger("rules/peephole.bwr.proof")   // an unproven rule fails the build, as linking does today
    .emit(Path::new(&out_dir).join("peephole.rs"))?;

// src/lib.rs
bitwright::include_rules!(Peephole, concat!(env!("OUT_DIR"), "/peephole.rs"));
let engine = Engine::builder().rules(Peephole).strategy(Strategy::compile()).build()?;
```

The generator compiles the program exactly as `RuleProgram::compile` does: same checks,
lints, KBO orientation and `RuleId`s. It then lowers every rule of a group into one **decision
tree** over opcodes, as Cranelift's ISLE and LLVM's GlobalISel combiner do:

- **Matching.** A `match` on the root opcode, then on operand opcodes, with commutative orders
  expanded at generation time rather than searched at run time.
- **Widths.** Width variables are bound by field reads.
- **Guards** become direct calls (`site.zero_bits(x, !c)`).
- **`let`s and constant parameters** become `u64` arithmetic when the width is at most 64,
  with a `BitVec` fallback.
- **Templates** become direct builder calls.

No allocation happens anywhere. The generated code implements a public trait that the engine
links like a program:

```rust
pub trait RuleSet: Send + Sync + 'static {
    /// Content hash of the program and the generator version; enters the configuration hash
    /// and so the memo epoch.
    fn id(&self) -> u128;
    /// Name, `RuleId` and group of each rule, for observers, ledgers and quarantine.
    fn rules(&self) -> &'static [RuleMeta];
    /// The first rule that rewrites `n`, and its result.
    fn rewrite(&self, site: &mut Site<'_>, n: Expr) -> Option<(u32, Expr)>;
}
```

`Site` is the whole capability surface: node views, fact queries under the run's budget and
assumptions, and construction. Through it the engine keeps charging budgets, recording
reliance and running postconditions and hooks exactly as for interpreted rules. A generated
rule set is just a faster reading of a proved program; nothing about soundness changes.

The built-in corpus would be precompiled the same way, into a checked-in file with a test that
fails when regenerating it changes a byte. That removes the startup compile. It reverses the
decision in design §7.3 (embedded source, no generated code to keep in sync). The staleness
test is the usual answer to that concern, and §7.3 itself anticipates "pre-built dispatch
tables … if the engine needs them".

Testing: the decision tree is checked differentially against the reference matcher on random
DAGs, as a fuzz target and in the heavy suites. This is the "fast matcher (M4), tested
differentially" that §7.3 already describes.

### 2b. A faster interpreter for rules loaded at run time

Tools that accept user `.bwr` files at run time (the CLI, the Python and C bindings) cannot
generate code. They would interpret the same decision tree, flattened to bytecode, with its
scratch in the runner so it allocates nothing per candidate. Codegen and bytecode are then two
back ends of one middle end (`RuleProgram` → decision tree), with one semantics and one
differential test. This alone should remove most of the matcher's 28 % and the allocator's
share.

### 2c. Native rewrites in Rust

For what `.bwr` cannot say, such as target legality, cost models or rewrites that consult the
host's own analyses:

```rust
pub trait Rewrite: Send + Sync + 'static {
    fn name(&self) -> &str;
    fn revision(&self) -> u32 { 1 }          // enters the memo epoch, as `ExtOp::revision` does
    fn rewrite(&self, site: &mut Site<'_>, n: Expr) -> Option<Expr>;
}
```

Arbitrary Rust cannot be proved by the rule checker, so a native rewrite links as **unproven**,
like `EngineBuilder::unproven_program`. It gets sampled verification at every application by
default, which costs about 16 evaluations of both sides per rewrite and suits development but
not the hot path. To trust it in release builds, a project runs
`bitwright::check::rewrite(&r, config)` in its own test suite. That drives the rewrite over
generated DAGs, exhaustively at small widths and sampled up to 512, the way `ext::check`
self-tests an `ExtOp`. Then it links it with `allow_unproven`. The recommendation to hosts is
`.bwr` wherever it can express the rewrite (proved at every width) and native code only where
it cannot.

## Layer 3: an engine tier for compilers

This is the largest gain: it removes the growth with function size, not just a constant factor.

- **A compiler strategy, `Strategy::compile()`.** It runs `FactFold`, `Local(core)` and the
  passes whose work per node is bounded by a small constant, for one round. The region-walking
  passes are left out, or capped far lower than 256 visits (demanded bits at, say, 16). Commit
  decisions are made per node, from tree-local cost, so every result is final and the memo
  holds it.
- **Use counts from the host.** The compiler knows each value's real use count from its IR;
  bitwright infers it from the roots of one call. Taking it from the host (a slice, or a
  `Uses` trait) makes the sharing-aware commit rule cheap and makes results independent of
  which roots were passed. They then become memoizable in the standard strategy too.
- **A session that keeps its scratch.** `engine.session(&mut cx)` holds the runner's maps,
  stacks and pass marks across calls, and grows the marks with the arena instead of resizing
  them on each `run`.
- **An incremental entry point, `session.simplify_node(e)`**, for a host that visits each
  instruction once, in order, with its operands already normal. That is one dispatch, with no
  stack walk and no rounds.
- **Facts from the host.** Guards spent 24 % of the rules-only run computing facts. A compiler
  often already has known bits for its values. Assumptions can seed them today, but
  assumptions enter the memo key as an exact copy on every run. A `FactSource` keyed by symbol,
  with a revision number, is cheaper. Design §5 folded "providers" into assumptions for 0.x;
  this operating point is the case for bringing them back.

## What does not change

- **Proofs.** Every rewrite that is not explicitly unproven is proved. Generated rule sets link
  against the same ledgers.
- **Postconditions.** Passes keep their commit rule, and postconditions and hooks run on every
  application.
- **Budgets and determinism.** Budgets stay deterministic. Results stay independent of hash
  seeds and thread counts.
- **Existing configurations** (`Strategy::standard()`, `deobfuscate()`) keep their results.
  The compiler tier is new policy beside them.

## Order of work

Each step is measured with the benchmark from step 1 and lands alone.

1. **Done: the compiler-shaped workload in `bitwright-bench`** (`compile/*`): every SSA value
   a root, 50 and 200 instructions, rules only and standard, and memoized re-runs. The note
   under each row gives the DAG size before and after, visits, memo hits and rewrites, so a
   faster row that simplifies less shows it. The standard re-run at 200 instructions makes
   *more* rewrites than the first run (578 against 402), so the second run does not merely
   confirm the first.
2. **Done: the engine tier.** Three changes:
   - **`Strategy::sharing`.** `Sharing::Ignored` makes the commit rule count only the uses
     inside the region below the node, so every pass result is final and memoized.
   - **`Strategy::max_region`** caps the region the rule examines and the demanded-bits walk.
   - **`Strategy::compile()`**: the standard phases without demanded bits, one round,
     `Sharing::Ignored`, `max_region` 64.

   The defaults keep every existing strategy's results and engine ids. On `compile/*` (same
   VM), a 200-instruction function costs 1.4 ms against 18.6 ms for the standard strategy,
   about 7 µs per instruction instead of 93 µs. Its result is 179 nodes against 213 on the
   row's seed, and on 100 functions 14,118 against 14,447. Cost per instruction no longer
   grows with the function: 11.6, 8.2 and 2.8 µs at 50, 200 and 1,000 instructions. A second
   call over the same values visits nothing.

   Measured on the way:
   - **Demanded bits, decided node by node,** made results larger (15,064 with it) and cost a
     quarter of the time, so `compile()` leaves it out.
   - **A second round** cost 35 % more and found nothing.
   - **The region cap** did not matter on this workload; 64 bounds the work per node on deep
     chains.

   New tests check that results under `Sharing::Ignored` are equal to their inputs, pass
   strict verification and are final. They also check that a value's result is the same alone
   as with the rest of its function.

   Two smaller changes to the engine's walk:
   - A phase whose memo already holds the root returns without setting up a walk.
   - The walk's stack is reused.

   Together they bring a fully memoized single-value call from 980 to about 470 ns.

   Not done, and next for this tier:
   - **The passes' caches outlive only one call.** Those caches are the linear and xor forms,
     truth tables, comparison descriptions and residues. Calling once per instruction as it is
     created therefore costs about 50 % more than one call per function (10 against 6.5 µs
     per instruction). Keeping them in the context's memo, keyed like it (engine, hooks,
     assumptions), would remove that. Their entries record finality and reliance, which
     depend on budgets and assumptions, so this needs care.
   - **Use counts from the host.** They would let the commit rule weigh real sharing and stay
     final.
   - **Host-supplied facts** (`FactSource`).
3. **Done, in part: builder fast paths (1b).**
   - **Constants of 64 bits or fewer** are interned from a word (`mk_const_u64`), with the same
     node and structural hash as from a `BitVec`. A test checks this at every width, whichever
     path comes first.
   - **The canonicalizer's constant checks** read words: `is_ones`, shift counts,
     subtraction of a constant, and the fold test. The fold test no longer builds either
     operand's value unless both are constants.
   - **`Context::reserve`** makes room for a function's nodes.

   Building the `compile/*` workload went from 1,248 to 958 instructions per built instruction
   (callgrind, 400,000 instructions: −23 %), about 145 ns on the VM.

   Left as they were:
   - **The symbol index keeps SipHash.** Its keys can be strings from untrusted input (the
     bindings take names), and a compiler that keeps its own dense value map calls `symbol`
     once per value.
   - **`Error` keeps its variants.** Boxing its payloads changes a public type, for a gain not
     yet measured.
   - **The structural hash stays as it is.** Most of what remains is interning: a Merkle hash
     of four mixes per binary node, a table probe, and the height and tree-size columns. The
     hash fixes canonical operand order, so it is part of the output-stability contract.
     Changing it changes results, and belongs in a release that says so.
4. **The rule middle end: measured first, and re-planned.** On `compile/*` the dispatch net
   already leaves 0.4 candidate rules per node visit (rules alone) and 0.1 (`compile()`).
   About half of those fail to match and half fail their guard. So a decision tree would save
   little on candidate selection. The cost was per candidate: about 3,900 instructions of
   matching for under four matcher steps, spent in two places:
   - `is_closed` walked the pattern with a fresh stack at every step;
   - every attempt allocated its bindings and work lists, and a commutative node cloned
     them all.

   Done:
   - Closedness is a table computed when a rule compiles.
   - The matcher's bindings, work lists and width values are small inline vectors, which
     allocate only beyond their capacity.

   The matcher's semantics are unchanged, and so are the results. Matching went from 78.7 to
   37.0 million instructions (−53 %). The whole run went from 263 to 214 million with the
   rules alone (−19 %), and from 755 to 695 million under `compile()` (−8 %).

   Guards are most of what rule application costs now, and that is fact computation: an
   operand's facts, computed once per node and shared with the passes.

   Under `compile()` the matcher is now 6 % of the time:
   - the passes are 46 % (linear forms 14 %, xor and truth tables 6 % each);
   - fact transfers are 23 %;
   - rule application is 18 %.

   Generated Rust (2a) would cut into the matcher's 6 % only, and is postponed. What pays
   next is facts: a compiler's own known bits (the `FactSource` of step 2's list), or a
   lighter fact tier for `compile()` (known bits without the ranges). A lighter tier changes
   results, so it needs measuring like the demanded-bits decision was. After that come the
   passes' per-node costs.

   **Done: declared known bits** (`Context::declare_known`). A compiler states its known
   bits of symbols (parameters, loads, calls, values from other blocks), and they become the
   symbols' base facts.

   Measured on `compile/*`, with two parameters declared (one zero-extended from 32 bits, one
   an 8-byte-aligned pointer):
   - **Time is unchanged** (within noise).
   - **Results are slightly smaller** (14,118 → 14,070 nodes). The random workload rarely
     uses those bits; code with alignment checks, masks and extensions does (the book's
     example folds both checks, and `p + 8 & -8` to `p + 8`).

   So declarations add precision and knowledge bitwright cannot derive. They do not cut the
   facts' cost, which is the transfers of every interior node. That cost needs the lighter
   fact tier (known bits without ranges, for `compile()`), measured for how results change.
5. **`Semantics` and `Raise`**, then the derive (1a, 1c).
6. **Native `Rewrite` and `check::rewrite`** (2c).

Rough targets for a compiler-shaped run with the rules-only tier: construction under 100 ns
per instruction, and translation plus simplification under 500 ns per instruction, down from
2–2.5 µs. With the compiler strategy, the cost per instruction should stay flat as functions
grow. These are targets, not measurements.

## Open questions

- **Generated code for the built-in corpus.** Is a staleness test acceptable against §7.3's
  "no generated code to keep in sync"?
- **Can the decision tree keep source-order priority exactly?** First the rule, then the
  operand order of a commutative match. It must, or results change; the differential test
  decides.
- **Which passes belong in `Strategy::compile()`?** And at what caps? This needs measuring on
  real compiler IR, not only the synthetic workload: LLVM IR through `lift::llvm` is the
  obvious corpus.
- **Should a `Rewrite` see facts under assumptions?** If it does, it relies on constraints,
  and its reliance must be reported like a rule's.

## Appendix: the benchmark

`workload::ssa_function(cx, seed, n)` in `bitwright-bench` creates four 64-bit symbols
(`U64` keys). It then appends *n* values, each from two of the last eight values and a
constant in `1..=64`, with the operation chosen uniformly from:

- `a + b`, `a − b`, `a & c`, `a | b`, `a ^ b`, `a << c`, `a · c`, `a + c`;
- `select(a <u b, a, b)`;
- `zext(trunc32(a))`;
- `(a + c) − c`;
- `(a ^ b) ^ b`.

It returns the *n* values as roots. The `compile/*` rows cycle through eight seeds in one
reused context (`clear` between functions); `Engine::run` alone is measured, and a `-rerun`
row's first run happens in the unmeasured setup. The table above was measured before the
workload moved into the suite, with a scratch copy of the same generator (a different random
generator, so the functions differ) at 50 to 400 instructions: 100,000 / *N* functions per
configuration, timed with `Instant`. The floor is the same generator over a bare
`hashbrown::HashTable<u32>` of 16-byte nodes. Profiles are callgrind at *N* = 100 (standard)
and *N* = 200 (rules only).

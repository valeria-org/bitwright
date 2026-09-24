# bitwright-compare

Compares bitwright with other symbolic engines on public mixed Boolean-arithmetic (MBA)
datasets: how much of each expression they simplify, how fast, and with how much memory; and,
with [`versus-smt`](#versus-smt-the-smt-solvers-simplifiers), with the simplifiers of z3 and
Bitwuzla on random bit-vector expressions and on identities of bit-vector algebra. It is its
own Cargo workspace (the other engines are its dependencies, not the main workspace's) and not
run in CI.

| Tool | What runs |
|-|-|
| `bw-standard` | bitwright, `Strategy::standard()` |
| `bw-deobf` | bitwright, `Strategy::deobfuscate()` (linear MBA and shuffle passes) |
| `bw-mba` | bitwright, deobfuscate with the MBA service and the native `SignatureSolver` |
| `bw-nf` | bitwright, deobfuscate with the MBA service, the native `NormalFormSolver` and bitwright's own evidence only |
| `bw-eqsat` | bitwright's equality saturation, every built-in equation group (`eqsat.bwr`) |
| `egg-bw` | [egg](https://github.com/egraphs-good/egg) 0.11 with the same equations, plus commutativity (bitwright's e-graph sorts operands; egg needs rules) |
| `egg-mba` | egg with those, the usual MBA identities and constant folding |
| `cobra-cpp` | [CoBRA](https://github.com/trailofbits/CoBRA), the upstream C++ tool: `cobra-cli`'s pipeline, run by `cobra-batch/` |
| `cobra` | CoBRA's Rust port (`cobra-mba` 0.4), in process, spot-checked answers like upstream |
| `cobra-cert` | the same with the port's defaults: only answers with a Lean certificate |
| `z3`, `bitwuzla`, `cvc5` | the SMT solvers' simplifiers (`simplify`, `simplify_term`, `Solver::simplify`) |
| `claripy` | angr's `claripy.simplify` |
| `miasm` | Miasm's `expr_simp` |
| `triton-llvm` | Triton's `simplify(…, llvm=True)`: the expression through LLVM's optimizer |
| `triton-synth` | Triton's `synthesize` (oracle-based synthesis of subexpressions and constants) |

## Running

The datasets are CoBRA's collection (about 76,000 expressions from SiMBA, GAMBA, NeuReduce,
MBA-Obfuscator, MBA-Solver, QSynth, Loki, OSES and others, all at 64 bits). They are mostly
GPL-3.0, so they are fetched, not copied here:

```sh
git clone --depth 1 https://github.com/trailofbits/CoBRA /path/to/CoBRA
cargo run --release -- /path/to/CoBRA/test/datasets --skip oses_all   # oses_all = fast + slow
```

A `work/` directory here is git-ignored, for a local CoBRA checkout, builds and the Python
engines' packages. `--only TEXT` and `--skip TEXT` select files by path, `--limit N` takes the
first N cases of each, `--tools a,b` picks tools (`--list` lists them), and `--csv FILE` writes
one row per case and tool. The table goes to standard output, one block per file as each
finishes, then the totals. With `BW_FAILURES=FILE` in the environment, every scored case a
bitwright tool leaves larger than the ground truth is appended to `FILE` (tool, line, input,
ground truth and answer, tab-separated).

**C++ CoBRA.** Build its dependencies and the driver against the checkout (CMake 3.20+, a C++23
compiler; LLVM is not needed), then pass `--cobra-cpp`:

```sh
cmake -S /path/to/CoBRA/dependencies -B /path/to/CoBRA/build-deps -DCMAKE_BUILD_TYPE=Release
cmake --build /path/to/CoBRA/build-deps
cmake -S cobra-batch -B cobra-batch/build -DCMAKE_BUILD_TYPE=Release \
  -DCOBRA_SOURCE=/path/to/CoBRA -DCMAKE_PREFIX_PATH=/path/to/CoBRA/build-deps/install
cmake --build cobra-batch/build
cargo run --release -- /path/to/CoBRA/test/datasets --cobra-cpp cobra-batch/build/cobra-batch
```

`cobra-batch` runs `tools/cobra-cli/main.cpp`'s pipeline step for step (parse, constant folding,
signature, `Simplify` with spot checks, the full-width check) on every line of a file in one
process; its answers match `cobra-cli`'s line for line. It is compiled with CoBRA's own flags.

**The Python-driven engines** (`solvers.py`) need `z3-solver`, `bitwuzla`, `cvc5`, `claripy`,
`triton-library` (its wheel includes LLVM), and a Miasm source checkout with the `future`
package. `--python` names the interpreter; it is called as `PYTHON solvers.py ENGINE ...`, so it
can be a wrapper that picks each engine's environment (claripy pins its own z3). Engines whose
package does not import are skipped.

## What is measured

Every tool starts from the same text and gets each case alone (bitwright and egg in a fresh
context or e-graph each). Every answer is read into a bitwright context and measured there, the
same way for every tool. A line bitwright's parser declines is read in the datasets' own syntax
(`src/read.rs`: Python's operators and precedence, `**` with a constant exponent, literals of
any size modulo 2^64, `X[0]` names, a trailing note in words, a leading label, a ground truth
written `(constant N)`). Cases are 64-bit, except that bitwright's tools measure a line whose
ground truth disagrees with its input at 64 bits and agrees at 32, 16 or 8 at the widest such
width (some OSES lines are 8-bit arithmetic; the note says so); the other tools get it at 64
bits, where it counts as a dataset error.

- **wrong**: the answer disagrees with the input at one of 64 points (the boundary values 0, all
  ones, 1 and the sign bit, then random values): an unsound answer.
- **failed**: the tool reported an error or timed out, or its answer could not be read back.
- **solved**: the answer is correct at every point and no larger than the dataset's ground truth
  (DAG nodes in bitwright's canonical form, sharing counted once). Rounded down, so 100.0 means
  every scored line.
- **exact**: the answer is the ground truth itself (the same canonical node).
- **no truth**: lines that are checked but not scored: without a ground truth (`-`), or with
  one that disagrees with the input at every width (a dataset error, also reported on standard
  error). **reduced**: those among them answered smaller than the input.
- **size/truth**: the median ratio of the answer's size to the ground truth's.
- **µs**: from the text to the answer, parsing included, for bitwright (whose parser builds the
  canonical, hash-consed form), egg (parse, saturation, extraction) and both CoBRAs. For the
  Python-driven engines only the simplification call is timed: building their terms goes through
  Python, one call per node, which would measure the interpreter (and an engine such as Bitwuzla
  already rewrites while building). Each of their cases runs under a 5 s timeout
  (`SOLVERS_TIMEOUT`), counted as failed; egg runs with its default limits (10,000 e-nodes,
  30 iterations, 5 s).
- **heap KB**: the most heap in use above the start of the call (requested bytes, counted by a
  replaced allocator in Rust and a replaced `operator new` in C++); none for the Python tools.

A ground truth that disagrees with its input is reported on standard error. How a tool trusts
its answers differs (bitwright commits only rewrites it can justify, CoBRA checks at sampled
points, `cobra-cert` requires a Lean certificate, the others rewrite by construction); the
`wrong` column checks every answer independently.

## `versus-smt`: the SMT solvers' simplifiers

`versus-smt` compares bitwright's simplifier (`Engine::standard()`) with z3's `simplify` and
Bitwuzla's `simplify_term`, called in process through their C APIs with default settings. The
inputs are random DAGs shaped like `bitwright-bench`'s (4 symbols; 40 or 400 operator nodes; 8
or 64 bits), built only from operators SMT-LIB's QF_BV has natively: arithmetic, bitwise
operations, shifts, comparisons under `ite`, truncations extended back, and in one corpus
division, remainder and shifts by variable amounts. So no tool reads a lowered form of an
operator another tool has as one node (bitwright exports rotations, population counts or
byte swaps as several SMT-LIB operations). Two more corpora are floating point, in binary32 and
binary64: random DAGs of 40 operations over 6 float atoms and a few constants, written in
SMT-LIB's FloatingPoint theory (not as bitwright's encodings), with only what SMT-LIB
specifies (sums, differences, products, quotients, fused multiply-adds, roots, remainders,
rounding to an integral value, negations, absolute values, round trips through another format,
choices on comparisons and tests; not `fp.min`, `fp.max` or conversions to integers, which it
leaves open on some inputs); their answers are compared as SMT-LIB values (every NaN one
value).

Every tool starts from the same SMT-LIB script, bitwright's export of the DAG, and is timed from
that text to its answer, parsing included, in a context made before the clock starts; a case's
time is the fastest of five runs. Answers are read back into bitwright, sized in DAG nodes of
its canonical form like the MBA harness does, and checked against the input at 64 points (all
zeros, all ones, one, the sign bit, then random values). z3 prints division by a divisor it has
shown or guarded to be nonzero as `bvudiv_i` and the like; those are read as the plain operators
(the points, zero included, would catch a difference).

It links against the releases the nightly CI tests with (z3 5.1.0, Bitwuzla 0.9.1), unpacked
anywhere, for example under `work/`:

```sh
curl -sSfLO https://github.com/Z3Prover/z3/releases/download/z3-5.1.0/z3-5.1.0-x64-glibc-2.39.zip
curl -sSfLO https://github.com/bitwuzla/bitwuzla/releases/download/0.9.1/Bitwuzla-Linux-x86_64-static.zip
unzip -q -d work z3-5.1.0-x64-glibc-2.39.zip && unzip -q -d work Bitwuzla-Linux-x86_64-static.zip
Z3_DIR=$PWD/work/z3-5.1.0-x64-glibc-2.39 BITWUZLA_DIR=$PWD/work/Bitwuzla-Linux-x86_64-static \
  cargo run --release --features native-smt --bin versus-smt -- 200
```

Bitwuzla's static libraries need GMP and MPFR (`libgmp.so.10`, `libmpfr.so.6`) and the C++
runtime. The argument is the number of DAGs per corpus (200 by default). It prints one markdown
row per corpus and tool: the nodes before and after (summed), how many answers are smaller than
their input and how many are the smallest of the three (ties count for each), wrong and failed
answers, and the median and 95th-percentile time. With `VERSUS_SMT_DUMP=DIR`, every case's
script, each solver's answer as printed and each answer as bitwright reads it are written to
`DIR`.

**Identities.** `versus-smt --facts` runs the fact sets of [`facts/`](facts) instead: 580
bit-vector identities and 71 floating-point ones, written from textbook mathematics and IEEE
754, without mixed boolean-arithmetic ones.
[`bitvector.txt`](facts/bitvector.txt) (377, in 15 groups: Boolean algebra, ring arithmetic,
two's complement, shifts, rotations, extraction and extension, division, comparisons,
if-then-else, known bits; its header gives the format) is the algebra;
[`number-theory.txt`](facts/number-theory.txt) (parity, powers of two, odd numbers and their
inverses, squares, polynomial identities, divisibility), [`order.txt`](facts/order.txt) (order
laws, bounds, minimum and maximum, monotone operations), [`slices.txt`](facts/slices.txt)
(extraction through operations, concatenation, repetition, fields),
[`bit-tricks.txt`](facts/bit-tricks.txt) (lowest set bit, bit tests, sign extension, rotations
from slices, selection through masks) and [`canonical.txt`](facts/canonical.txt) (reordered
operands, gathered constants) add one area each. Each identity runs at 8 and 64 bits, over the
atoms `x`, `y`, `z` and over compound terms (`x = a·b`, `y = c | d`, `z = e − f`), with `p` a
comparison: 2,320 cases. [`float.txt`](facts/float.txt) (71, from IEEE 754: sign operations,
classification, comparisons, arithmetic, rounding, conversions) runs in binary32 and binary64
(the 8- and 64-bit runs), over float atoms and over compound floats (`x = a·b`, `y = c + d`,
`z = √e`), in SMT-LIB's FloatingPoint theory: 284 cases; answers are compared as SMT-LIB values
(every NaN one value). Its last group holds only on values (a NaN operand's payload changes the
bits), so bitwright, which keeps bit patterns, leaves it; the others hold bit for bit. `--set
NAME` runs one set. Every
tool starts from the unsimplified side as SMT-LIB text, so none gets a head start from another's
reading of it. A case is solved when the answer is no larger than the simpler side, and exact
when it is that side (both in bitwright's canonical form). The two sides of every case are
checked equal at the 64 points first; a case that fails is reported and left out. It prints one
row per set and one per group, and the cases a tool leaves unsolved go to standard error as
`unsolved TOOL SET.CASE`.

`--deobfuscate` runs bitwright as `bitwright simplify` does, for either input: the
deobfuscation strategy with the MBA service and `NormalFormSolver` on bitwright's own evidence,
instead of `Engine::standard()`.

`--proofs DIR` times nothing: it writes, per case, bitwright's answer against its input as
`CASE.smt2`, and with `--facts` the identity itself as `CASE.fact.smt2`, for any SMT solver to
prove (`unsat`). The obligation reads the input from the original text, so it checks the whole
path from the text to the answer, bitwright's reading of the text included.

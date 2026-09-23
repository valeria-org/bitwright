# bitwright-compare

Compares bitwright with other symbolic engines on public mixed Boolean-arithmetic (MBA)
datasets: how much of each expression they simplify, how fast, and with how much memory. It is
not part of the main workspace (it enables the `cobra` feature, which the workspace's own builds
should not pick up) and not run in CI.

| Tool | What runs |
|-|-|
| `bw-standard` | bitwright, `Strategy::standard()` |
| `bw-deobf` | bitwright, `Strategy::deobfuscate()` (linear MBA and shuffle passes) |
| `bw-mba` | bitwright, deobfuscate with the MBA service and the native `SignatureSolver` |
| `bw-cobra` | bitwright, deobfuscate with the MBA service and the `CobraSolver` backend |
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
finishes, then the totals.

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
same way for every tool:

- **wrong**: the answer disagrees with the input at one of 64 points (the boundary values 0, all
  ones, 1 and the sign bit, then random values): an unsound answer.
- **failed**: the tool reported an error or timed out, or its answer could not be read back.
- **solved**: the answer is correct at every point and no larger than the dataset's ground truth
  (DAG nodes in bitwright's canonical form, sharing counted once).
- **exact**: the answer is the ground truth itself (the same canonical node).
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

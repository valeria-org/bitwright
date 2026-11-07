# bitwright Workbench

A viewer of the engine's runs: every step, where in the run it happened, why it was allowed, and
what the engine tried and dropped on the way. It reads traces (JSON Lines, as
`bitwright::engine::Trace` writes them) and runs the engine live through the WebAssembly module.
Plain HTML, CSS and JavaScript modules: no build step, no dependencies.

## Run it

Serve the repository's root over HTTP (the page loads ES modules, which browsers refuse from
`file://`), then open `/workbench/`:

```sh
python3 -m http.server 8000      # from the repository's root
# then http://localhost:8000/workbench/
```

It opens on `samples/corpus.bwt`. For live runs, build the WebAssembly module first; the page
finds it in `target/`:

```sh
cargo build --release -p bitwright-wasm --target wasm32-unknown-unknown
```

Other traces: **Open…**, drop a file on the window, or `?trace=<url>` in the address. **Save**
writes the open trace back out (a live run's, say). The place you are looking at is in the
address, so it can be bookmarked or sent: `#trace?run=2&step=3`, `#whynot?run=2&node=14`.

Keys: `j` / `k` (or the arrows) step through a run, `n` / `p` move between the runs of a file,
`Esc` closes the node popover. The button at the top right switches the theme (system, light,
dark). Click any subterm, in the expression text or a tree row, for its node: its known bits,
what was tried at it, the step that made it and the steps that rewrote it, with links into the
other views.

## Write a trace

```sh
bitwright simplify --width 32 --trace run.bwt -- '(x ^ y) + 2 * (x & y)'
bitwright simplify --width 32 --assume 'x <u 16' --trace run.bwt -- '(x & 0xf0) + x'
bitwright simplify --width 32 --file exprs.txt --trace corpus.bwt      # one run per line
```

From Rust, `Trace` is a run's observer:

```rust
let mut trace = Trace::new(&engine).with_explanations(true).with_facts(true);
trace.with_assumptions(&mut cx, &assumptions)?;
let out = engine.run(&mut cx, &[e], Run::default().with_assumptions(&assumptions).with_observer(&mut trace))?;
std::fs::write("run.bwt", trace.to_jsonl(&mut cx, &[e], &out)?)?;
```

From JavaScript, `bw.trace(text, width, { deobfuscate, assume })` (`bitwright-wasm/js`).
Several traces concatenated are one file of several runs: the Corpus view lists them.

## Views

- **Trace**: the steps of a run, grouped by round and phase. For each one, the whole
  expression before and after with the rewritten subterm marked, the tree it matched in, the
  size after each step, and the inspector. A rule shows its text, doc, examples and the
  evidence of its proof ledger. A pass shows its reasoning: a linear or xor form, a truth table,
  a relation set or intervals, corner values, bit sources, a demanded mask, the layers it
  undid, a divisor, the MBA answer's evidence. A step also shows the step it builds on (its
  pattern matched a node an earlier step made) and the assumptions it relies on. Constructor
  folds are steps of their own. The tree folds the subtrees the step did not touch; **Show
  everything** opens them, or click one. The strip at the bottom is phases × rounds: work,
  rewrites, and candidates dropped as not smaller.
- **Stages**: each phase of each round, with its work, its rewrites, the candidates it dropped,
  and the root it left.
- **Why not**: every node something was tried at, and what came of each attempt. No match, a
  failed guard with its predicate and the operands' known bits, a candidate that was not
  smaller with its size, or applied.
- **Facts**: the run's assumptions and the steps that relied on each, and the known bits and
  intervals of every node the trace names, with and without the assumptions.
- **Corpus**: one row per run, sortable by any column and filtered by text; a rule census over
  all of them (rules tried often and rarely applied are dispatch work); and the passes' totals.
- **Compare**: two runs phase by phase, aligned by name. Use another run of the file, a second
  trace (another strategy, budget or engine version), or the same input run live with the
  other engine.

## Files

- `js/model.js`: parses traces, and derives steps, phases, attempts, provenance, the whole
  expression after each step, sizes and the census. No DOM, so it runs under Node too.
- `js/print.js`: prints expressions as bitwright's printer does.
- `js/trace-view.js`, `js/panels.js`, `js/cards.js`: the views; `js/popover.js`: the node
  popover.
- `js/main.js`: loading, routing, live runs.
- `samples/`: the bundled trace and the inputs it is made from (`make.sh` writes it again).
- `test/`: the model's tests (`node --test workbench/test/*.test.mjs`). `cargo test -p
  bitwright-cli` also runs them on traces the command line writes, so the viewer and the
  format stay in step.

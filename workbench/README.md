# bitwright Workbench

A playground for the engine, and a viewer of its runs. Type an expression and it is simplified
as you type; the rewrites appear as a story you open step by step, each with the whole
expression before and after and the one card that explains it: the rule as written and proved,
or the pass's reasoning. Change the width, the engine, an assumption or a single phase and look
again; give the symbols values and watch every step keep the value. Plain HTML, CSS and
JavaScript modules: no build step, no dependencies.

## Run it

Serve the repository's root over HTTP (the page loads ES modules, which browsers refuse from
`file://`), build the WebAssembly module once, then open `/workbench/`:

```sh
cargo build --release -p bitwright-wasm --target wasm32-unknown-unknown
python3 -m http.server 8000      # from the repository's root
# then http://localhost:8000/workbench/
```

The playground's state is in the address (`?e=…&w=32&assume=…&phases=…`), so a link reproduces
what you see. **Examples** loads a curated input with a line on what to watch for; **Rules**
browses the built-in corpus (search by name, text or doc, click an example to load it);
**Inspect** opens the current run in the six-view inspector below. `Esc` closes the node
popover; the button at the top right switches the theme.

**Phases.** The engine's strategy is a list of phases run in order, repeated until a round
changes nothing. The toggles turn any phase off (or on): the result, the story and the
inspector then show what that phase was doing. The two presets are the command line's
`deobfuscate + MBA` and the library's `standard`.

**At a point.** Give every symbol a value (decimal, hex, or `random`): the input and the
expression after each step are evaluated at that point, and must agree. They always do; the
display is the check.

## The inspector (`inspect.html`)

Every view of a run, for the forensic case. It opens a trace file (**Open**, drop a file on the
window, or `?trace=<url>`), the bundled sample `samples/corpus.bwt`, or the playground's run.
**Save** writes the open trace back out. Its place is in the address (`#trace?run=2&step=3`,
`#whynot?run=2&node=14`). Keys: `j` / `k` step through a run, `n` / `p` move between runs.

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

## The inspector's views

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
- `js/playground.js`: the playground; `js/main.js`: the inspector's loading, routing and live runs.
- `samples/`: the bundled trace and the inputs it is made from (`make.sh` writes it again).
- `test/`: the model's tests (`node --test workbench/test/*.test.mjs`). `cargo test -p
  bitwright-cli` also runs them on traces the command line writes, so the viewer and the
  format stay in step.

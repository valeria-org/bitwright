// node --test workbench/test/*.test.mjs (BWT=<trace.bwt>: another trace than the bundled sample).
// The trace model and the printer, on a real trace.
import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { parseTrace, provenance, census, corpusRows, alignPhases, phaseTable, symbolWidth } from "../js/model.js";
import { print } from "../js/print.js";

const path = process.env.BWT ?? fileURLToPath(new URL("../samples/corpus.bwt", import.meta.url));
const runs = parseTrace(readFileSync(path, "utf8"));
const norm = (s) => s.replace(/\s+/g, " ").trim();
// The kinds of explanation each pass gives.
const KINDS = {
  fact_fold: ["fold"],
  linear: ["linear"],
  xor: ["xor"],
  bitwise: ["bitwise"],
  compares: ["relations", "intervals"],
  casts: ["casts"],
  demanded: ["demanded"],
  linear_mba: ["linear_mba"],
  shuffle: ["shuffle"],
  invert: ["invert"],
  division: ["division"],
  carries: ["carries"],
  mba: ["mba"],
};

test("every run has a header, phases, a result and counters", () => {
  assert.ok(runs.length > 0);
  for (const run of runs) {
    assert.equal(run.header.trace, "bitwright");
    assert.equal(run.header.format, 1);
    assert.ok(run.phases.length > 0);
    assert.ok(run.result, "a result line");
    assert.ok(run.stats, "a stats line");
    assert.equal(run.steps.filter((s) => s.kind !== "fold" && s.kind !== "stage").length, run.stats.rewrites);
  }
});

test("the printer writes what the engine's printer wrote", () => {
  let checked = 0;
  for (const run of runs) {
    for (const [id, n] of run.nodes) {
      if (n.text === undefined) continue;
      assert.equal(norm(print(run, id)), norm(n.text), `node ${id}`);
      checked += 1;
    }
  }
  assert.ok(checked > 20);
});

test("every rewrite is placed in the whole expression, which ends at the result", () => {
  for (const run of runs) {
    for (const s of run.steps) {
      assert.ok(s.whole.exact, `run ${run.index + 1} step ${s.index} (${s.name})`);
    }
    const last = run.steps[run.steps.length - 1];
    if (!last || !run.result) continue;
    // After the last rewrite, the root is the result (up to the constructors' order).
    const end = run.phaseRuns.filter((p) => p.steps.length).at(-1)?.after;
    assert.equal(run.sizes.key(end), run.sizes.key(run.result.expr));
  }
});

test("phases, attempts and explanations hang together", () => {
  for (const run of runs) {
    const rows = phaseTable(run);
    assert.equal(rows.length, run.phases.length);
    for (const pr of run.phaseRuns) assert.ok(pr.round < run.rounds);
    for (const s of run.steps) {
      if (!s.explain) continue;
      assert.ok((KINDS[s.name] ?? []).includes(s.explain.kind), `${s.name} explained as ${s.explain.kind}`);
    }
    const prov = provenance(run);
    for (const [later, earlier] of prov) assert.ok(earlier.index < later.index);
  }
});

test("a census counts every rule attempt once", () => {
  const c = census(runs);
  let candidates = 0;
  for (const run of runs) for (const ev of run.events) if (ev.ev === "candidate") candidates += 1;
  assert.equal(c.rules.reduce((a, r) => a + r.candidates, 0), candidates);
  const rows = corpusRows(runs);
  assert.equal(rows.length, runs.length);
  for (const r of rows) assert.ok(r.sizeOut <= r.sizeIn, `${r.input}: ${r.sizeIn} -> ${r.sizeOut}`);
});

test("phases align by name", () => {
  assert.deepEqual(alignPhases(["a", "b", "c"], ["a", "c"]), [[0, 0], [1, null], [2, 1]]);
  assert.deepEqual(alignPhases(["a"], ["x", "a"]), [[null, 0], [0, 1]]);
});

test("the symbols' width is the run's width", () => {
  for (const run of runs) {
    if (!run.result) continue;
    const w = symbolWidth(run, run.result.input);
    assert.ok([8, 16, 32, 64].includes(w) || w > 0);
  }
});

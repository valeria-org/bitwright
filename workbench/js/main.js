// The Workbench: loads traces (a file, a dropped file, `?trace=<url>`, the bundled sample, or a
// live run through the WebAssembly module) and shows one view of the current run. The view, the
// run and the step or node in it live in the URL's hash (`#trace?run=2&step=3`), so a place in a
// trace can be bookmarked and sent.

import { parseTrace, symbolWidth } from "./model.js";
import { renderTrace } from "./trace-view.js";
import { renderStages, renderWhyNot, renderFacts, renderCorpus, renderCompare } from "./panels.js";
import { print } from "./print.js";
import { h, fill } from "./dom.js";
import * as popover from "./popover.js";

const $ = (id) => document.getElementById(id);
const main = $("main");
const TABS = ["trace", "stages", "whynot", "facts", "corpus", "compare"];
const HINTS = {
  trace: "j / k or ↑ ↓: steps · n / p: runs · click any subterm to inspect it · Esc closes",
  stages: "click a phase to open its first rewrite",
  whynot: "every node something was tried at; a failed guard shows the predicate and the operands' known bits",
  facts: "the assumptions and what relied on each; known bits with and without them",
  corpus: "click a column to sort, a row to open its run",
  compare: "phases aligned by name; a phase only one strategy has is hatched",
};

const app = {
  runs: [],
  run: null,
  text: "",
  source: "",
  step: null,
  tab: "trace",
  whyNode: null,
  factNode: null,
  compareRun: null,
  otherRuns: [],
  live: null,
  onStep: null,
  treeFocus: true,
  sort: { key: "index", dir: 1 },
  filter: "",

  /// Selects step `i` of the current run (and switches to `tab` when given).
  select(i, tab) {
    this.step = i;
    if (tab && tab !== this.tab) {
      this.go(tab, { step: i + 1 });
      return;
    }
    writeHash();
    if (this.tab === "trace" && this.onStep) {
      this.onStep();
      const b = main.querySelector(`.step[data-i="${i}"]`);
      if (b) b.scrollIntoView({ block: "nearest" });
    } else this.render();
  },

  /// Opens `tab` with `extra`: `{ step }` (1-based) or `{ node }`.
  go(tab, extra = {}) {
    if (extra.step !== undefined) this.step = extra.step - 1;
    if (extra.node !== undefined) {
      if (tab === "whynot") this.whyNode = extra.node;
      if (tab === "facts") this.factNode = extra.node;
    }
    this.tab = TABS.includes(tab) ? tab : "trace";
    writeHash();
    this.render();
  },

  /// Writes the current place into the URL without rendering.
  sync() {
    writeHash();
  },

  /// Opens the Why not view at node `id`.
  whyNot(id) {
    this.go("whynot", { node: id });
  },

  /// Makes run `i` of the file current.
  openRun(i, tab) {
    if (!this.runs[i]) return;
    this.run = this.runs[i];
    this.step = null;
    this.whyNode = null;
    this.factNode = null;
    if (this.compareRun === this.run) this.compareRun = null;
    renderRunbar();
    syncLiveForm();
    if (tab) this.tab = tab;
    writeHash();
    this.render();
  },

  render() {
    popover.hide();
    const q = this.run ? `?run=${this.runs.indexOf(this.run) + 1}` : "";
    for (const a of document.querySelectorAll("#tabs a")) {
      a.classList.toggle("on", a.dataset.tab === this.tab);
      a.href = `#${a.dataset.tab}${q}`;
    }
    $("hint").textContent = this.run ? HINTS[this.tab] ?? "" : "";
    this.onStep = null;
    if (!this.run) {
      renderEmpty();
      return;
    }
    const views = { trace: renderTrace, stages: renderStages, whynot: renderWhyNot, facts: renderFacts, corpus: renderCorpus, compare: renderCompare };
    try {
      views[this.tab](this, main);
    } catch (e) {
      fill(main, h("div", { class: "empty" }, h("h2", {}, "This view failed"), h("pre", {}, String(e.stack ?? e))));
      console.error(e);
    }
  },

  /// Opens a trace file's text.
  loadText(text, source) {
    const runs = parseTrace(text);
    this.runs = runs;
    this.text = text;
    this.source = source;
    this.compareRun = null;
    this.otherRuns = [];
    $("saveBtn").disabled = false;
    this.openRun(0);
    const events = runs.reduce((n, r) => n + r.events.length, 0);
    say(`${source} · ${runs.length} run${runs.length > 1 ? "s" : ""} · ${events} events · bitwright ${runs[0].header.version}`);
    document.title = `${print(runs[0], runs[0].result?.input ?? 0, { lets: false }).slice(0, 40)} · bitwright Workbench`;
  },

  /// Loads a second trace to compare with.
  async loadOther(file) {
    if (!file) return;
    try {
      const runs = parseTrace(await file.text());
      this.otherRuns.push(...runs);
      this.compareRun = runs[0];
      this.render();
      say(`${file.name}: loaded for comparison`);
    } catch (e) {
      say(`${file.name}: ${e.message}`, true);
    }
  },

  /// Runs the current input again with the other engine, and compares.
  liveCompare() {
    const r = this.run;
    if (!this.live || !r?.result) return;
    const input = print(r, r.result.input, { lets: false });
    const width = symbolWidth(r, r.result.input);
    const deobfuscate = r.header.strategy === "standard";
    try {
      const assume = r.assumptions.filter(Boolean).map((a) => print(r, a.expr, { lets: false }));
      const [other] = parseTrace(this.live.trace(input, width, { deobfuscate, assume }));
      this.otherRuns.push(other);
      this.compareRun = other;
      this.render();
    } catch (e) {
      say(e.message, true);
    }
  },
};

function say(text, err = false) {
  const s = $("status");
  s.textContent = text;
  s.classList.toggle("err", err);
}

// ----- the run bar ----------------------------------------------------------------------------

function renderRunbar() {
  const bar = $("runbar");
  const r = app.run;
  if (!r) {
    fill(bar);
    return;
  }
  const i = app.runs.indexOf(r);
  const nav = h("div", { class: "runnav" });
  if (app.runs.length > 1) {
    const sel = h("select", { "aria-label": "Run", onchange: (e) => app.openRun(Number(e.target.value)) });
    app.runs.forEach((x, k) => sel.append(h("option", { value: k, selected: k === i }, `run ${k + 1} of ${app.runs.length} · ${print(x, x.result?.input ?? 0, { lets: false }).slice(0, 44)}`)));
    nav.append(
      h("button", { title: "Previous run (p)", disabled: i === 0, onclick: () => app.openRun(i - 1) }, "‹"),
      sel,
      h("button", { title: "Next run (n)", disabled: i === app.runs.length - 1, onclick: () => app.openRun(i + 1) }, "›"),
    );
  } else {
    nav.append(h("span", { class: "muted" }, app.source === "live run" ? "live run" : "1 run"));
  }
  const res = r.result;
  const output = res ? print(r, res.expr) : "";
  const rewrites = r.steps.filter((s) => s.kind !== "fold").length;
  const meta = [
    `${res ? `${r.sizes.size(res.input)} → ${r.sizes.size(res.expr)}` : ""} nodes`,
    `${rewrites} rewrite${rewrites === 1 ? "" : "s"}`,
    `${r.rounds} round${r.rounds === 1 ? "" : "s"}`,
    `${(r.stats?.node_visits ?? 0).toLocaleString()} visits`,
    r.header.strategy,
  ];
  const warn = [];
  if (res && res.end !== "completed") warn.push(`${res.end.replace("_", " ")}${res.stopped ? `: ${res.stopped}` : ""}`);
  if (res && res.relies_on?.length) warn.push(`relies on ${res.relies_on.map((c) => `#${c}`).join(", ")}`);
  fill(
    bar,
    nav,
    h("div", { class: "result-line" }, h("span", { class: "arrow" }, "⇒"), h("span", { class: `expr${res?.changed === false ? " same" : ""}`, title: output }, res?.changed === false ? `${output}  (unchanged)` : output)),
    h("div", { class: "runmeta" }, meta.map((m) => h("span", {}, m)), warn.map((m) => h("span", { class: m.startsWith("relies") ? "" : "warn" }, m))),
  );
}

function syncLiveForm() {
  const r = app.run;
  if (!r?.result) return;
  $("liveExpr").value = print(r, r.result.input, { lets: false });
  const w = String(symbolWidth(r, r.result.input));
  if ([...$("liveWidth").options].some((o) => o.value === w)) $("liveWidth").value = w;
  $("liveEngine").value = r.header.strategy === "standard" ? "standard" : "deobfuscate";
  $("liveAssume").value = r.assumptions.filter(Boolean).map((a) => print(r, a.expr, { lets: false })).join("; ");
}

function renderEmpty() {
  fill(
    main,
    h(
      "div",
      { class: "empty" },
      h("h2", {}, "Open a trace"),
      h("p", {}, "Open a .bwt file, drop one on the window, or run an expression above (when the WebAssembly module is built). Write a trace with the command line:"),
      h("pre", {}, "bitwright simplify --width 32 --trace run.bwt -- '(x ^ y) + 2 * (x & y)'\nbitwright simplify --width 32 --file exprs.txt --trace corpus.bwt"),
      h("p", {}, "or from Rust, with bitwright::engine::Trace as the run's observer."),
    ),
  );
}

// ----- routing ----------------------------------------------------------------------------------

function readHash() {
  const raw = location.hash.slice(1);
  const [tab, query] = raw.split("?");
  const q = new URLSearchParams(query ?? "");
  return {
    tab: TABS.includes(tab) ? tab : "trace",
    run: Number(q.get("run")) || null,
    step: Number(q.get("step")) || null,
    node: q.has("node") ? Number(q.get("node")) : null,
  };
}

function writeHash() {
  if (!app.run) return;
  const q = new URLSearchParams();
  q.set("run", String(app.runs.indexOf(app.run) + 1));
  if (app.tab === "trace" && app.step !== null) q.set("step", String(app.step + 1));
  if (app.tab === "whynot" && app.whyNode !== null) q.set("node", String(app.whyNode));
  if (app.tab === "facts" && app.factNode !== null) q.set("node", String(app.factNode));
  const hash = `#${app.tab}?${q}`;
  if (location.hash !== hash) history.replaceState(null, "", hash);
}

/// Takes the place the URL names: the run, and the step or node in it.
function takePlace(p) {
  app.tab = p.tab;
  if (p.run !== null && app.runs[p.run - 1] && app.runs[p.run - 1] !== app.run) {
    app.run = app.runs[p.run - 1];
    app.step = null;
    app.whyNode = null;
    app.factNode = null;
    renderRunbar();
    syncLiveForm();
  }
  if (p.step !== null) app.step = p.step - 1;
  if (p.node !== null && p.tab === "whynot") app.whyNode = p.node;
  if (p.node !== null && p.tab === "facts") app.factNode = p.node;
}

window.addEventListener("hashchange", () => {
  takePlace(readHash());
  writeHash();
  app.render();
});

// ----- keys, theme, files ---------------------------------------------------------------------

document.addEventListener("keydown", (e) => {
  if (!app.run) return;
  if (e.target instanceof HTMLInputElement || e.target instanceof HTMLSelectElement || e.target instanceof HTMLTextAreaElement) return;
  if (e.ctrlKey || e.metaKey || e.altKey) return;
  const i = app.runs.indexOf(app.run);
  if (e.key === "n" && i + 1 < app.runs.length) {
    app.openRun(i + 1);
    e.preventDefault();
    return;
  }
  if (e.key === "p" && i > 0) {
    app.openRun(i - 1);
    e.preventDefault();
    return;
  }
  if (app.tab !== "trace") return;
  const n = app.run.steps.length;
  if (n === 0) return;
  if (e.key === "j" || e.key === "ArrowDown") {
    app.select(Math.min(n - 1, (app.step ?? -1) + 1));
    e.preventDefault();
  } else if (e.key === "k" || e.key === "ArrowUp") {
    app.select(Math.max(0, (app.step ?? 1) - 1));
    e.preventDefault();
  }
});

const THEMES = ["system", "light", "dark"];
let theme = "system";
function applyTheme(t) {
  theme = t;
  if (t === "light" || t === "dark") document.documentElement.dataset.theme = t;
  else delete document.documentElement.dataset.theme;
  $("themeBtn").title = `Theme: ${t} (click to change)`;
  $("themeBtn").textContent = t === "light" ? "☀" : t === "dark" ? "☾" : "◐";
  try {
    localStorage.setItem("wb-theme", t);
  } catch {
    // no storage: the choice lasts the page
  }
}
$("themeBtn").addEventListener("click", () => applyTheme(THEMES[(THEMES.indexOf(theme) + 1) % THEMES.length]));
try {
  applyTheme(localStorage.getItem("wb-theme") ?? "system");
} catch {
  applyTheme("system");
}

async function openFile(file) {
  try {
    app.loadText(await file.text(), file.name);
  } catch (e) {
    say(`${file.name}: ${e.message}`, true);
  }
}
$("fileInput").addEventListener("change", (e) => {
  if (e.target.files[0]) openFile(e.target.files[0]);
  e.target.value = "";
});
$("saveBtn").addEventListener("click", () => {
  if (!app.text) return;
  const blob = new Blob([app.text], { type: "application/x-ndjson" });
  const name = app.source.endsWith(".bwt") ? app.source.split("/").pop() : "run.bwt";
  const a = h("a", { href: URL.createObjectURL(blob), download: name });
  document.body.append(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(a.href), 1000);
});
$("saveBtn").disabled = true;
let dragDepth = 0;
window.addEventListener("dragenter", (e) => {
  if (![...(e.dataTransfer?.types ?? [])].includes("Files")) return;
  dragDepth += 1;
  $("drop").hidden = false;
});
window.addEventListener("dragleave", () => {
  dragDepth = Math.max(0, dragDepth - 1);
  if (dragDepth === 0) $("drop").hidden = true;
});
window.addEventListener("dragover", (e) => e.preventDefault());
window.addEventListener("drop", (e) => {
  e.preventDefault();
  dragDepth = 0;
  $("drop").hidden = true;
  const f = e.dataTransfer?.files?.[0];
  if (f) openFile(f);
});
popover.install();
popover.wire(app, main);

// ----- live runs ------------------------------------------------------------------------------

async function loadWasm() {
  let mod;
  try {
    mod = await import("../../bitwright-wasm/js/bitwright.mjs");
  } catch {
    return null;
  }
  for (const path of ["../target/wasm32-unknown-unknown/release/bitwright_wasm.wasm", "bitwright_wasm.wasm"]) {
    try {
      const res = await fetch(path);
      if (!res.ok) continue;
      return await mod.instantiate(await res.arrayBuffer());
    } catch {
      // the next place
    }
  }
  return null;
}

$("live").addEventListener("submit", (e) => {
  e.preventDefault();
  if (!app.live) return;
  const expr = $("liveExpr").value.trim();
  if (!expr) return;
  const width = Number($("liveWidth").value);
  const deobfuscate = $("liveEngine").value === "deobfuscate";
  const assume = $("liveAssume").value.split(";").map((s) => s.trim()).filter(Boolean);
  try {
    const t0 = performance.now();
    const text = app.live.trace(expr, width, { deobfuscate, assume });
    app.loadText(text, "live run");
    if (app.run.steps.length) app.go("trace", { step: 1 });
    else app.go("trace");
    say(`live run · ${(performance.now() - t0).toFixed(1)} ms · ${app.run.events.length} events`);
  } catch (err) {
    say(String(err.message ?? err), true);
  }
});

async function start() {
  renderRunbar();
  const wasm = loadWasm().then((bw) => {
    app.live = bw;
    $("liveRun").disabled = !bw;
    const hint = "Build the WebAssembly module for live runs: cargo build --release -p bitwright-wasm --target wasm32-unknown-unknown";
    for (const id of ["liveExpr", "liveAssume", "liveRun"]) $(id).title = bw ? (id === "liveRun" ? "Run the engine on this expression (Enter)" : "") : hint;
    if (!bw) $("live").classList.add("off");
    if (!bw && !app.run) say(hint);
    return bw;
  });
  $("liveRun").disabled = true;
  const wanted = readHash();
  const param = new URLSearchParams(location.search).get("trace");
  const url = param ?? "samples/corpus.bwt";
  try {
    const res = await fetch(url);
    if (res.ok) {
      app.loadText(await res.text(), param ? url : `sample ${url}`);
      takePlace(wanted);
      writeHash();
      app.render();
    } else {
      if (param) say(`${url}: ${res.status} ${res.statusText}`, true);
      app.render();
    }
  } catch (e) {
    if (param) say(`${url}: ${e.message}`, true);
    app.render();
  }
  await wasm;
}
start();

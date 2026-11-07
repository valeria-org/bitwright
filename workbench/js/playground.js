// The playground: an expression that runs as you type, its result, and the rewrites as a story
// that opens in place; a width, an engine, assumptions and the phases to change one thing and
// look again; a point to evaluate every step at; examples to load and the rules to browse. The
// six-tab inspector (inspect.html) opens on the same run.

import { parseTrace, provenance, symbolWidth } from "./model.js";
import { print, short, latex, highlight, smtScript } from "./print.js";
import { h, fill, chip, kindClass } from "./dom.js";
import { stepBody } from "./trace-view.js";
import * as popover from "./popover.js";

const $ = (id) => document.getElementById(id);
const main = $("main");

const PHASES = [
  ["fact_fold", "fold", "Nodes whose facts pin one value become that constant."],
  ["local", "rules", "The built-in rules, bottom-up to a fixpoint."],
  ["linear", "linear", "Linear sums c + Σ kᵢ·aᵢ collected and written back canonically: cancels additive masking."],
  ["xor", "xor", "Xor sums k ⊕ ⊕ (aᵢ & mᵢ) collected and written back: cancels boolean masking."],
  ["casts", "casts", "Extracts and truncations pushed through arithmetic and bitwise operations."],
  ["division", "division", "Divisions by a constant recovered from multiplications by a magic number."],
  ["invert", "invert", "Equalities through invertible maps: f(x) == f(y) becomes x == y, f(x) == c becomes x == f⁻¹(c)."],
  ["compares", "compares", "Boolean combinations of comparisons become one comparison, a range check, or a constant."],
  ["bitwise", "bitwise", "Bitwise functions of a few atoms become the minimum form of their truth table."],
  ["carries", "carries", "Carry and borrow networks written out as & | ^ ~ become the sum they compute (proved)."],
  ["linear_mba", "linear MBA", "Linear combinations of bitwise functions, read off their values at the corners."],
  ["shuffle", "shuffle", "Values assembled from bit slices become the source, a rotation, a byte swap or a concat."],
  ["demanded", "demanded", "Operands observed only through some bits are simplified under those bits."],
  ["mba", "MBA", "The MBA service: fragments lowered, solved, proved by certificate, and lifted back."],
];
const STRATEGIES = {
  deobfuscate: ["fact_fold", "local", "linear", "xor", "casts", "division", "invert", "compares", "bitwise", "carries", "linear_mba", "shuffle", "demanded", "mba", "local"],
  standard: ["fact_fold", "local", "linear", "xor", "casts", "invert", "compares", "bitwise", "demanded", "local"],
};

const EXAMPLES = [
  [
    "A tour of the syntax",
    `let k = 0xd3220fb78e33751f;
let lo = trunc<32>(x);
let hi = extract<32, 32>(x);
let m = (x ^ k) * k;
let mixed = (m ^ ((m >>u 32) >>u (m >>u 60))) * k;
let swapped = concat(bswap(lo), rotl(hi, 8));
let q = umulhi(y, 0xcccccccccccccccd) >>u 3;
let flag = (lo <u hi) & (lo != hi);
select(flag, swapped, x) + (q - udiv(y, 10)) + zext<64>(mixed == 0) + ((z & 0xff) + 0x100) - (z & 0xff)`,
    64,
    "let bindings, hex and decimal constants, casts and slices, concat and select, rotations and byte swaps, signed and unsigned operators spelled out. Several parts simplify independently: watch which passes take which.",
  ],
  ["A linear MBA", "(((x ^ y) + 2*(x & y)) * 3 + ((x | y) - (x & y))) ^ (~z & z)", 32, "Four rules clear the easy parts, then the MBA service proves the rest is 2·((x | y) + x + y). Watch the fold the constructors make after step 1."],
  ["Masking that cancels", "((x ^ 0x5a) + 3 - 3) ^ 0x5a", 32, "No rule fires: the linear pass cancels + 3 − 3, the xor pass cancels the two ^ 0x5a. Turn either phase off and see what stays."],
  ["A keyed hash compared with 0", "let m = (x ^ 0xd3220fb78e33751f) * 0xd3220fb78e33751f; (m ^ ((m >>u 32) >>u (m >>u 60))) * 0xd3220fb78e33751f == 0", 64, "The invert pass undoes four injective layers in one step, the xorshift region included, and recovers the key."],
  ["A division by a magic number", "umulhi(x, 0xcccccccccccccccd) >>u 3", 64, "A compiler's strength reduction undone: the division pass proves the quotient exact for every x. Only the deobfuscate strategy runs it."],
  ["A flags idiom", "((a - b) >>u 31) ^ (((a ^ b) & (a ^ (a - b))) >>u 31)", 32, "SF ≠ OF written out as shifts and xors becomes a signed comparison, by two rules in a row."],
  ["A cast through an add", "trunc<8>(zext<32>(c:8) + 256)", 32, "The guard of add_disjoint is decided by known bits (bit 8 is the only set bit of 256), then the casts pass pushes the truncation through."],
  ["Two comparisons, one range", "(x <u 10) & (3 <u x)", 32, "The compares pass intersects two interval sets into one range check, x − 4 <=u 5."],
  ["Comparisons of a pair", "(x <=u y) & (x != y) & (x <s y)", 32, "Every predicate on a pair is a set of five relations; & intersects them. Open the step to see the sets."],
  ["A byte shuffle", "((x >>u 8) & 0xff) | ((x & 0xff) << 8) | (x & 0xffff0000)", 32, "The shuffle pass traces every bit to its source and writes the swap as a concat of slices."],
  ["Under assumptions", "((rsp + 32) & 15) + zext<64>(idx <=u n)", 64, "With rsp & 15 == 0 and idx <u n assumed, both parts fold to constants, and the result says which assumptions it relied on.", ["rsp & 15 == 0", "idx <u n"]],
  ["And plus or", "(x & y) + (x | y)", 32, "One identity. Open it to read the rule as written and how it was proved."],
  ["Nothing to do", "x + y", 32, "Already normal: see the work the engine spends finding that out, and what the rules tried."],
];

const app = {
  bw: null,
  text: "",
  width: 32,
  engine: "deobfuscate",
  phases: null,
  assumes: [],
  run: null,
  trace: "",
  open: new Set(),
  treeFocus: true,
  point: {},
  rules: null,
  myRules: { src: "", use: false, trusted: false },

  /// Expands step `i` (0-based) and scrolls to it: the trace view's "select".
  select(i) {
    this.open.add(i);
    renderStory();
    const row = $("story").querySelector(`[data-i="${i}"]`);
    if (row) row.scrollIntoView({ block: "center", behavior: "smooth" });
  },

  /// The inspector's views, for what the playground does not show.
  go(tab, extra = {}) {
    saveForInspect();
    const q = new URLSearchParams({ run: "1" });
    if (extra.step !== undefined) q.set("step", String(extra.step));
    if (extra.node !== undefined) q.set("node", String(extra.node));
    window.open(`inspect.html?from=playground#${tab}?${q}`, "_blank");
  },

  whyNot(id) {
    this.go("whynot", { node: id });
  },
};

// ----- running ------------------------------------------------------------------------------

let timer = null;
function schedule() {
  clearTimeout(timer);
  timer = setTimeout(runNow, 160);
}

function phaseList() {
  if (this_engine() === "custom") return app.phases ?? [];
  return STRATEGIES[app.engine];
}
function this_engine() {
  return app.engine;
}

function runNow() {
  writeUrl();
  const text = app.text.trim();
  const err = $("err");
  if (!text) {
    app.run = null;
    err.hidden = true;
    $("result").hidden = true;
    $("point").hidden = true;
    fill($("story"));
    $("inspectLink").href = "inspect.html";
    return;
  }
  if (!app.bw) return;
  try {
    const t0 = performance.now();
    const opts = { assume: app.assumes };
    if (app.engine === "custom") opts.phases = app.phases ?? [];
    else opts.deobfuscate = app.engine === "deobfuscate";
    if (app.myRules.use && app.myRules.src.trim()) {
      opts.rules = app.myRules.src;
      opts.trusted = app.myRules.trusted;
    }
    app.trace = app.bw.trace(text, app.width, opts);
    [app.run] = parseTrace(app.trace);
    err.hidden = true;
    app.open = new Set(app.run.steps.length === 1 ? [0] : []);
    $("status").textContent = `${(performance.now() - t0).toFixed(1)} ms · ${app.run.events.length} events`;
    $("inspectLink").href = "inspect.html?from=playground#trace?run=1";
    saveForInspect();
  } catch (e) {
    err.textContent = String(e.message ?? e);
    err.hidden = false;
    return;
  }
  renderResult();
  renderStory();
  renderPoint();
}

function saveForInspect() {
  try {
    sessionStorage.setItem("wb-trace", app.trace);
  } catch {
    // no storage: Inspect opens on the sample instead
  }
}

// ----- the editor's controls -----------------------------------------------------------------

function renderControls() {
  const widths = $("widths");
  fill(widths, [8, 16, 32, 64].map((w) => h("button", { type: "button", role: "radio", "aria-checked": String(w === app.width), class: w === app.width ? "on" : "", onclick: () => { app.width = w; renderControls(); schedule(); } }, `${w}-bit`)));
  const engines = $("engines");
  const names = { deobfuscate: "deobfuscate + MBA", standard: "standard", custom: "custom" };
  const list = ["deobfuscate", "standard", ...(app.engine === "custom" ? ["custom"] : [])];
  fill(engines, list.map((e) => h("button", { type: "button", role: "radio", "aria-checked": String(e === app.engine), class: e === app.engine ? "on" : "", onclick: () => { app.engine = e; if (e !== "custom") app.phases = null; renderControls(); schedule(); } }, names[e])));
  const pills = $("assumePills");
  const used = new Set(app.run?.result?.relies_on ?? []);
  fill(pills, app.assumes.map((a, i) => h("span", { class: `pill${used.has(i) ? " used" : ""}`, title: used.has(i) ? "The result relies on this" : "" }, `#${i} ${a}`, h("button", { type: "button", "aria-label": `Remove ${a}`, onclick: () => { app.assumes.splice(i, 1); renderControls(); schedule(); } }, "×"))));
  const on = new Set(app.engine === "custom" ? app.phases ?? [] : STRATEGIES[app.engine]);
  const toggles = $("phases");
  fill(
    toggles,
    PHASES.map(([name, label, tip]) => {
      const kind = name === "local" ? "rule" : name === "mba" ? "solver" : "pass";
      return h("button", { type: "button", class: `toggle ${kindClass(kind)}${on.has(name) ? " on" : ""}`, "aria-pressed": String(on.has(name)), title: tip, onclick: () => togglePhase(name) }, label);
    }),
    h("div", { class: "tip" }, "The phases of a round, in this order; rounds repeat until one changes nothing. Turn one off to see what it was doing. The rules run again at the end of each round."),
  );
  $("phasesNote").textContent = app.engine === "custom" ? `custom · ${new Set(app.phases ?? []).size} of ${PHASES.length}` : `${app.engine === "deobfuscate" ? "deobfuscate + MBA" : "standard"} · ${new Set(STRATEGIES[app.engine]).size} of ${PHASES.length}`;
}

function togglePhase(name) {
  const current = app.engine === "custom" ? (app.phases ?? []).filter((p, i, a) => a.indexOf(p) === i) : [...new Set(STRATEGIES[app.engine])];
  const next = current.includes(name) ? current.filter((p) => p !== name) : [...current, name];
  // In the strategies' order, with the rules again at the end when they are on.
  const order = PHASES.map(([n]) => n);
  const ordered = order.filter((p) => next.includes(p));
  if (ordered.includes("local") && ordered.length > 1) ordered.push("local");
  app.engine = "custom";
  app.phases = ordered;
  renderControls();
  schedule();
}

function grow() {
  const ta = $("expr");
  ta.style.height = "auto";
  ta.style.height = `${Math.min(ta.scrollHeight + 2, window.innerHeight * 0.6)}px`;
  const hl = $("exprHl");
  hl.innerHTML = `${highlight(ta.value)}\n`;
  hl.style.height = ta.style.height;
  hl.scrollTop = ta.scrollTop;
}
$("expr").addEventListener("scroll", () => { $("exprHl").scrollTop = $("expr").scrollTop; });
$("expr").addEventListener("input", (e) => {
  app.text = e.target.value;
  grow();
  schedule();
});
$("bigBtn").addEventListener("click", () => {
  const on = $("editor").classList.toggle("big");
  main.classList.toggle("big", on);
  $("bigBtn").textContent = on ? "Normal editor" : "Large editor";
  grow();
  $("expr").focus();
});

// ----- import and export ------------------------------------------------------------------------

function panel(title, note, body, right = []) {
  const io = $("io");
  fill(io, h("div", { class: "io-head" }, h("span", { class: "t" }, title), note ? h("span", { class: "muted" }, note) : null, h("span", { class: "right" }, right, h("button", { type: "button", class: "quiet", onclick: () => { io.hidden = true; } }, "Close"))), body);
  io.hidden = false;
}

function copyButton(text) {
  return h("button", { type: "button", class: "quiet", onclick: (e) => { navigator.clipboard?.writeText(typeof text === "function" ? text() : text).then(() => { e.target.textContent = "Copied"; setTimeout(() => (e.target.textContent = "Copy"), 1200); }).catch(() => {}); } }, "Copy");
}

function downloadButton(name, text, type = "text/plain") {
  return h("button", { type: "button", class: "quiet", onclick: () => { const a = h("a", { href: URL.createObjectURL(new Blob([typeof text === "function" ? text() : text], { type })), download: name }); document.body.append(a); a.click(); a.remove(); } }, "Download");
}

$("importBtn").addEventListener("click", () => {
  const ta = h("textarea", { spellcheck: "false", placeholder: "(declare-const x (_ BitVec 32))\n(define-fun f () (_ BitVec 32) (bvadd x #x00000001))" });
  const note = h("div", { class: "note" }, "A QF_BV script: its last definition, or its assertions conjoined, becomes the expression; the symbols keep their declared widths.");
  const run = () => {
    if (!app.bw) return;
    try {
      const text = app.bw.fromSmtlib(ta.value);
      load(text, app.width, app.assumes, app.engine);
      $("io").hidden = true;
    } catch (e) {
      note.textContent = e.message;
      note.classList.add("warn");
    }
  };
  panel("Import SMT-LIB", null, [ta, note], [h("button", { type: "button", class: "primary", onclick: run }, "Import")]);
  ta.focus();
});

for (const b of document.querySelectorAll("[data-export]")) {
  b.addEventListener("click", () => exportAs(b.dataset.export));
}

function exportAs(kind) {
  const run = app.run;
  if (!run?.result || !app.bw) return;
  const input = print(run, run.result.input, { lets: false });
  const output = print(run, run.result.expr, { lets: false });
  try {
    if (kind === "smtlib") {
      const modes = [
        ["both", "input and result, asserted different: unsat means they agree everywhere (z3 -in, bitwuzla)"],
        ["input", "the input as a definition"],
        ["result", "the result as a definition"],
      ];
      let mode = "both";
      const pre = h("pre");
      const note = h("div", { class: "note" });
      const text = () => {
        try {
          if (mode === "input") return smtScript(run, [["input", run.result.input]], false);
          if (mode === "result") return smtScript(run, [["result", run.result.expr]], false);
          return smtScript(run, [["input", run.result.input], ["result", run.result.expr]], true);
        } catch (e) {
          // An operator QF_BV lacks: the library's form, one definition per node.
          note.textContent = `Flat form impossible (${e.message}); this is the library's own export, one definition per node.`;
          return mode === "both" ? app.bw.equivalenceQuery(input, output, app.width) : app.bw.toSmtlib(mode === "input" ? input : output, app.width);
        }
      };
      const seg = h("div", { class: "seg" }, modes.map(([m, tip]) => h("button", { type: "button", class: m === mode ? "on" : "", title: tip, onclick: (e) => { mode = m; for (const b of seg.children) b.classList.toggle("on", b === e.target); note.textContent = modes.find(([x]) => x === m)[1]; pre.textContent = text(); } }, m)));
      note.textContent = modes[0][1];
      pre.textContent = text();
      panel("SMT-LIB", null, [seg, pre, note], [copyButton(text), downloadButton("bitwright.smt2", text)]);
    } else if (kind === "lean") {
      const text = app.bw.toLean(input, output, app.width);
      panel("Lean 4", "an example bv_decide checks; needs Std's BVDecide", h("pre", {}, text), [copyButton(text), downloadButton("Equation.lean", text)]);
    } else if (kind === "latex") {
      const steps = run.steps.filter((s) => s.kind !== "fold");
      const lines = [`${latex(run, run.result.input)}`, ...steps.map((s) => `  &= ${latex(run, s.whole.after)} && \\text{${s.kind === "rule" ? s.name.split("::").pop().replace(/_/g, "\\_") : s.name}}`)];
      const text = ["\\begin{align*}", lines.join(" \\\\\n"), "\\end{align*}"].join("\n");
      const short = `${latex(run, run.result.input)} = ${latex(run, run.result.expr)}`;
      panel("LaTeX", "the input and every step as an aligned derivation; the short form is the input and the result alone", [h("pre", {}, text), h("div", { class: "note" }, "Short form:"), h("pre", {}, short)], [copyButton(text), downloadButton("derivation.tex", text)]);
    }
  } catch (e) {
    const why = kind === "lean" ? `Not stated: Lean's core BitVec has no counterpart for ${e.message}.` : e.message;
    panel(kind === "lean" ? "Lean 4" : kind, null, h("div", { class: "note warn" }, why));
  }
}

$("proveBtn").addEventListener("click", () => {
  const run = app.run;
  if (!run?.result || !app.bw) return;
  const input = print(run, run.result.input, { lets: false });
  const output = print(run, run.result.expr, { lets: false });
  const t0 = performance.now();
  let verdict;
  try {
    verdict = app.bw.equivalent(input, output, app.width);
  } catch (e) {
    verdict = `error: ${e.message}`;
  }
  const ms = (performance.now() - t0).toFixed(1);
  const ok = verdict === "equivalent";
  panel(
    "Proved here",
    `bitwright's own prover (bit-blasting and its SAT solver), in this browser, ${ms} ms`,
    [
      h("div", { class: ok ? "note" : "note warn", style: { fontSize: "13.5px", color: ok ? "var(--pass)" : "" } }, ok ? "Input and result are equal at every point: the engine's rewrites were right." : verdict === "undecided" ? "Not decided within the prover's default budget." : verdict),
      h("div", { class: "note" }, "This decides the whole run at once, independently of the rules' and passes' own proofs. For a certificate another checker can verify, export Lean (bv_decide) or SMT-LIB (z3, Bitwuzla)."),
    ],
  );
});

// ----- rules of your own ---------------------------------------------------------------------

const RULES_SKELETON = `bitwright 1;

group mine {
    /// Counting the trailing zeros of the reversed bits counts the leading zeros.
    #[example("ctz(bitrev(p:8))" => "clz(p)")]
    rule ctz_bitrev<W>(x: W) { ctz(bitrev(x)) => clz(x) }

    /// A guard from the facts: only where x is known to fit in four bits.
    #[allow(BW0407)]
    rule low_nibble<W>(x: W) where W >= 5 { x & 0xf => x if proves(x <u 16) }
}
`;

function saveRules() {
  try {
    localStorage.setItem("wb-rules", JSON.stringify(app.myRules));
  } catch {
    // the page keeps them
  }
}

function loadRules() {
  try {
    const saved = JSON.parse(localStorage.getItem("wb-rules") ?? "null");
    if (saved && typeof saved.src === "string") app.myRules = { src: saved.src, use: !!saved.use, trusted: !!saved.trusted };
  } catch {
    // none saved
  }
  if (!app.myRules.src) app.myRules.src = RULES_SKELETON;
  $("rulesSrc").value = app.myRules.src;
  $("useRules").checked = app.myRules.use;
  $("trustRules").checked = app.myRules.trusted;
}

$("rulesBtn").addEventListener("click", () => {
  const box = $("myrules");
  box.hidden = !box.hidden;
  if (!box.hidden) $("rulesSrc").focus();
});
$("rulesSrc").addEventListener("input", (e) => {
  app.myRules.src = e.target.value;
  saveRules();
  if (app.myRules.use) schedule();
});
$("useRules").addEventListener("change", (e) => {
  app.myRules.use = e.target.checked;
  saveRules();
  $("rulesBtn").textContent = app.myRules.use ? "My rules · on" : "My rules";
  schedule();
});
$("trustRules").addEventListener("change", (e) => {
  app.myRules.trusted = e.target.checked;
  saveRules();
  if (app.myRules.use) schedule();
});
$("checkRules").addEventListener("click", () => {
  if (!app.bw) return;
  const out = $("verdicts");
  fill(out, h("div", { class: "muted" }, "Checking…"));
  setTimeout(() => {
    let r;
    const t0 = performance.now();
    try {
      r = app.bw.checkRules(app.myRules.src);
    } catch (e) {
      fill(out, h("div", { class: "verdict error" }, h("span", { class: "v" }, "error"), h("span", { class: "nm" }, e.message)));
      return;
    }
    const items = [];
    for (const d of r.diagnostics) {
      const line = app.myRules.src.slice(0, d.start).split("\n").length;
      items.push(h("div", { class: `verdict ${d.level}` }, h("span", { class: "v" }, d.level), h("span", { class: "nm" }, `${d.code} · line ${line}`), h("span", { class: "d" }, d.message)));
    }
    for (const c of r.rules) {
      const detail = c.verdict === "sound" ? ledgerText(c.evidence) : c.verdict === "unsound" ? `counterexample: ${c.detail}` : `not enough evidence: ${c.detail}. A fixed width the checker cannot enumerate, or a guard the samples rarely meet; link trusted when a proof elsewhere vouches for it.`;
      items.push(h("div", { class: `verdict ${c.verdict}` }, h("span", { class: "v" }, c.verdict), h("span", { class: "nm" }, `${c.name} `, h("span", { class: "muted" }, c.kind)), h("span", { class: "d" }, detail, c.failedExamples ? ` · ${c.failedExamples} example${c.failedExamples > 1 ? "s" : ""} did not hold` : "")));
    }
    if (items.length === 0) items.push(h("div", { class: "muted" }, "No rules."));
    items.push(h("div", { class: "muted", style: { fontSize: "12px" } }, `${(performance.now() - t0).toFixed(0)} ms. Sound rules link with the checker's ledger; trusted links them without it, every application sampled.`));
    fill(out, items);
  }, 20);
});
$("leanBtn").addEventListener("click", () => {
  const ta = h("textarea", { spellcheck: "false", placeholder: "theorem and_or {w : Nat} (x y : BitVec w) : (x &&& y) + (x ||| y) = x + y := by\n  bv_decide\n\ntheorem masked (x : BitVec 32) (h : x.ult 16#32) : x &&& 0xff#32 = x := by\n  bv_decide" });
  const note = h("div", { class: "note" }, "Theorems proved in Lean become rules: binders are the parameters, hypotheses become proves(…) guards, the equation is the rewrite. The result lands in My rules, where you can read, edit and check it. Lean already proved them, so you may link them trusted; where the checker can enumerate, it should agree.");
  const go = (replace) => {
    if (!app.bw) return;
    const bwr = app.bw.leanToRules(ta.value);
    if (replace || !app.myRules.src.trim() || app.myRules.src === RULES_SKELETON) {
      app.myRules.src = bwr;
    } else {
      const body = bwr.split("group lean {")[1]?.replace(/}\s*$/, "") ?? "";
      const notes = bwr.split("\n").filter((l) => l.startsWith("//")).join("\n");
      app.myRules.src = `${app.myRules.src.trimEnd()}\n\n${notes ? `${notes}\n` : ""}group lean {${body}}\n`;
    }
    $("rulesSrc").value = app.myRules.src;
    saveRules();
    $("myrules").hidden = false;
    $("io").hidden = true;
    $("checkRules").click();
    if (app.myRules.use) schedule();
  };
  panel("Import Lean theorems", null, [ta, note], [h("button", { type: "button", class: "quiet", onclick: () => go(false) }, "Append"), h("button", { type: "button", class: "primary", onclick: () => go(true) }, "Replace my rules")]);
  ta.focus();
});

$("shareBtn").addEventListener("click", (e) => {
  writeUrl();
  navigator.clipboard?.writeText(location.href).then(() => { e.target.textContent = "Link copied"; setTimeout(() => (e.target.textContent = "Copy link"), 1200); }).catch(() => {});
});
$("assumeInput").addEventListener("keydown", (e) => {
  if (e.key !== "Enter") return;
  e.preventDefault();
  const v = e.target.value.trim();
  if (!v) return;
  app.assumes.push(v);
  e.target.value = "";
  renderControls();
  schedule();
});

// ----- the result and the story ---------------------------------------------------------------

function renderResult() {
  const run = app.run;
  const el = $("result");
  const r = run.result;
  if (!r) {
    el.hidden = true;
    return;
  }
  el.hidden = false;
  const rewrites = run.steps.filter((s) => s.kind !== "fold").length;
  const meta = [`${run.sizes.size(r.input)} → ${run.sizes.size(r.expr)} nodes`, `${rewrites} rewrite${rewrites === 1 ? "" : "s"}`, `${run.rounds} round${run.rounds === 1 ? "" : "s"}`, `${(run.stats?.node_visits ?? 0).toLocaleString()} node visits`];
  const warn = [];
  if (r.end !== "completed") warn.push(`${r.end.replace("_", " ")}${r.stopped ? `: ${r.stopped}` : ""}`);
  if (r.relies_on?.length) warn.push(`relies on ${r.relies_on.map((c) => `#${c}`).join(", ")}`);
  fill(
    el,
    h("span", { class: "arrow" }, "⇒"),
    h("div", { class: `code out${r.changed ? "" : " same"}`, html: print(run, r.expr, { html: true, spans: true }) + (r.changed ? "" : '<span class="muted">  (unchanged)</span>') }),
    h("div", { class: "meta" }, meta.map((m) => h("span", {}, m)), warn.map((m) => h("span", { class: m.startsWith("relies") ? "" : "warn" }, m))),
  );
  renderControls();
}

function renderStory() {
  const run = app.run;
  const el = $("story");
  if (!run) {
    fill(el);
    return;
  }
  const prov = provenance(run);
  const parts = [];
  let round = null;
  for (const s of run.steps) {
    if (s.round !== round) {
      round = s.round;
      const prs = run.phaseRuns.filter((p) => p.round === round);
      const active = prs.filter((p) => p.applied > 0).map((p) => p.name === "local" ? "rules" : p.name.replace("_", " "));
      const visits = prs.reduce((a, p) => a + (p.spent.node_visits ?? 0), 0);
      parts.push(h("div", { class: "round" }, `Round ${round + 1}`, h("span", { class: "n" }, `${[...new Set(active)].join(", ")} · ${visits} node visits`)));
    }
    const i = s.index - 1;
    const sb = run.sizes.size(s.whole.before);
    const sa = run.sizes.size(s.whole.after);
    const isOpen = app.open.has(i);
    const row = h("div", { class: `srow ${kindClass(s.kind)}${isOpen ? " open" : ""}${s.kind === "fold" ? " fold" : ""}`, "data-i": i });
    const by = s.kind === "rule" ? s.name.split("::")[1] : s.kind === "fold" ? "constructors" : s.name;
    const byKind = s.kind === "rule" ? (s.by.rule?.kind === "identity" ? "identity" : "rule") : s.kind === "solver" ? "MBA" : s.kind === "fold" ? "fold" : "pass";
    row.append(
      h(
        "button",
        { type: "button", class: "head", "aria-expanded": String(isOpen), onclick: () => { if (app.open.has(i)) app.open.delete(i); else app.open.add(i); renderStory(); } },
        h("span", { class: "i" }, String(s.index)),
        h("span", { class: "dot" }),
        h("span", { class: "what", title: `${print(run, s.before)}  ⇒  ${print(run, s.after)}` }, h("span", { html: highlight(short(run, s.before, 90)) }), h("span", { class: "arr" }, "→"), h("span", { class: "to", html: highlight(short(run, s.after, 70)) })),
        h("span", { class: "by" }, by, h("small", {}, byKind)),
        h("span", { class: `delta${sa < sb ? " down" : ""}`, title: `${sb} → ${sa} nodes` }, sa < sb ? `−${sb - sa}` : sa > sb ? `+${sa - sb}` : "="),
      ),
    );
    if (isOpen) row.append(h("div", { class: "body" }, stepBody(app, run, s, prov)));
    parts.push(row);
  }
  for (let r = 0; r < run.rounds; r++) {
    if (!run.steps.some((s) => s.round === r && s.kind !== "stage")) {
      const prs = run.phaseRuns.filter((p) => p.round === r);
      const visits = prs.reduce((a, p) => a + (p.spent.node_visits ?? 0), 0);
      parts.push(h("div", { class: "round" }, `Round ${r + 1}`, h("span", { class: "n" }, `${visits} node visits`)), h("div", { class: "quiet" }, run.steps.length ? "Nothing more to rewrite: the fixpoint." : "Nothing to rewrite: the expression is already in normal form. Inspect shows what the rules tried."));
    }
  }
  fill(el, parts);
}

// ----- a point to evaluate at -----------------------------------------------------------------

function symbols(run) {
  const out = new Map();
  for (const n of run.nodes.values()) if (n.op === "sym" && n.name) out.set(n.name, n.w);
  return [...out];
}

function renderPoint() {
  const run = app.run;
  const el = $("point");
  const syms = symbols(run);
  if (!run.result || syms.length === 0 || !app.bw) {
    el.hidden = true;
    return;
  }
  el.hidden = false;
  const inputs = syms.map(([name, w]) => h("label", { class: "sym" }, `${name}`, h("input", { spellcheck: "false", value: app.point[name] ?? "", placeholder: `${w}-bit`, oninput: (e) => { app.point[name] = e.target.value; evaluatePoint(); } })));
  fill(el, h("span", { class: "label" }, "at a point"), inputs, h("button", { type: "button", class: "quiet", onclick: () => { for (const [name, w] of syms) app.point[name] = randomValue(w); renderPoint(); evaluatePoint(); } }, "random"), h("div", { class: "vals", id: "vals" }, h("span", { class: "muted" }, "Give every symbol a value to see each step's value stay equal.")));
}

function randomValue(w) {
  let v = 0n;
  for (let i = 0; i < w; i += 16) v = (v << 16n) | BigInt(Math.floor(Math.random() * 65536));
  return `0x${(v & ((1n << BigInt(w)) - 1n)).toString(16)}`;
}

function evaluatePoint() {
  const run = app.run;
  const vals = $("vals");
  if (!run?.result) return;
  const syms = symbols(run);
  if (syms.some(([n]) => !(app.point[n] ?? "").trim())) {
    fill(vals, h("span", { class: "muted" }, "Give every symbol a value to see each step's value stay equal."));
    return;
  }
  const env = Object.fromEntries(syms.map(([n]) => [n, app.point[n].trim()]));
  const at = (t) => {
    try {
      return app.bw.evaluate(print(run, t, { lets: false }), app.width, env);
    } catch (e) {
      return `error: ${e.message}`;
    }
  };
  const v0 = at(run.result.input);
  const items = [h("span", {}, "input ", h("b", {}, v0))];
  let same = true;
  for (const s of run.steps) {
    const v = at(s.whole.after);
    const ok = v === v0;
    same &&= ok;
    items.push(h("span", { class: ok ? "" : "bad" }, `after ${s.index} `, h("b", {}, v)));
  }
  items.push(same ? h("span", { class: "ok" }, "every step keeps the value") : h("span", { class: "bad" }, "a value changed"));
  fill(vals, items);
}

// ----- examples and rules ---------------------------------------------------------------------

function renderExamples() {
  fill(
    $("examples"),
    h("h2", {}, "Examples"),
    h("p", {}, "Each one shows a different part of the engine at work. Click to load it; then change the width, the engine or a phase and see what differs."),
    h(
      "div",
      { class: "cards" },
      EXAMPLES.map(([title, expr, w, desc, assume]) => h("button", { type: "button", class: "card", onclick: () => load(expr, w, assume ?? []) }, h("span", { class: "t" }, title), h("span", { class: "e", title: expr }, expr), h("span", { class: "d" }, desc))),
    ),
  );
}

function load(expr, w, assume = [], engine = "deobfuscate") {
  app.text = expr;
  app.width = w;
  app.assumes = [...assume];
  app.engine = engine;
  app.phases = null;
  app.point = {};
  $("expr").value = expr;
  grow();
  renderControls();
  runNow();
  main.scrollTo({ top: 0, behavior: "smooth" });
}

function renderRules() {
  const el = $("rules");
  if (!app.bw) {
    fill(el, h("h2", {}, "Rules"), h("p", { class: "muted" }, "The rule catalog needs the WebAssembly module."));
    return;
  }
  if (!app.rules) app.rules = app.bw.rules();
  const search = h("input", { type: "search", placeholder: "Find a rule by name, text or doc (e.g. disjoint, rotl, sign)", "aria-label": "Find a rule" });
  const count = h("span", { class: "count" });
  const list = h("div");
  const draw = () => {
    const q = search.value.trim().toLowerCase();
    const hits = q ? app.rules.filter((r) => `${r.name} ${r.doc} ${r.source}`.toLowerCase().includes(q)) : app.rules;
    count.textContent = `${hits.length} of ${app.rules.length}`;
    fill(
      list,
      hits.slice(0, 30).map((r) =>
        h(
          "div",
          { class: "rule" },
          h("div", { class: "rh" }, chip("rule", r.kind), h("span", { class: "nm" }, r.name)),
          r.doc ? h("div", { class: "doc" }, r.doc) : null,
          h("pre", {}, r.source),
          r.examples.length ? h("div", { class: "exs" }, h("span", { class: "label" }, "try"), r.examples.map(([a]) => h("button", { type: "button", title: "Load this example", onclick: () => load(a, app.width) }, a))) : null,
          r.ledger ? h("div", { class: "ledger" }, ledgerText(r.ledger)) : null,
        ),
      ),
      hits.length > 30 ? h("p", { class: "muted" }, `${hits.length - 30} more; narrow the search.`) : null,
    );
  };
  search.addEventListener("input", draw);
  fill(el, h("h2", {}, "Rules"), h("p", {}, "The built-in corpus: each rule as written, with its doc, examples you can load, and the evidence of its proof ledger."), h("div", { class: "find" }, search, count), list);
  draw();
}

function ledgerText(text) {
  const parts = [];
  for (const m of text.matchAll(/(\w+)\(([^)]*)\)/g)) {
    const f = Object.fromEntries(m[2].split(",").map((p) => p.split("=")));
    if (m[1] === "exhaustive") parts.push(`proved exhaustively at widths 1–${f.maxw}: ${Number(f.cases).toLocaleString()} cases${f.fired !== f.cases ? `, guard held in ${Number(f.fired).toLocaleString()}` : ""}`);
    else if (m[1] === "sampled") parts.push(`sampled to 512 bits: ${f.inst} instances, ${Number(f.cases).toLocaleString()} cases`);
  }
  return parts.join(" · ") || text;
}

// ----- URL state, theme, start -----------------------------------------------------------------

function readUrl() {
  const q = new URLSearchParams(location.search);
  if (q.has("e")) app.text = q.get("e");
  if (q.has("w") && [8, 16, 32, 64].includes(Number(q.get("w")))) app.width = Number(q.get("w"));
  if (q.has("assume")) app.assumes = q.get("assume").split(";").map((s) => s.trim()).filter(Boolean);
  if (q.has("phases")) {
    app.engine = "custom";
    app.phases = q.get("phases").split(",").map((s) => s.trim()).filter(Boolean);
  } else if (q.get("engine") === "standard") app.engine = "standard";
}

function writeUrl() {
  const q = new URLSearchParams();
  if (app.text.trim()) q.set("e", app.text.trim());
  if (app.width !== 32) q.set("w", String(app.width));
  if (app.assumes.length) q.set("assume", app.assumes.join("; "));
  if (app.engine === "custom") q.set("phases", (app.phases ?? []).join(","));
  else if (app.engine === "standard") q.set("engine", "standard");
  const url = `${location.pathname}${q.size ? `?${q}` : ""}${location.hash}`;
  if (`${location.pathname}${location.search}${location.hash}` !== url) history.replaceState(null, "", url);
}

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
    // the choice lasts the page
  }
}
$("themeBtn").addEventListener("click", () => applyTheme(THEMES[(THEMES.indexOf(theme) + 1) % THEMES.length]));
try {
  applyTheme(localStorage.getItem("wb-theme") ?? "system");
} catch {
  applyTheme("system");
}
for (const [id, target] of [["navExamples", "examples"], ["navRules", "rules"]]) {
  $(id).addEventListener("click", (e) => {
    e.preventDefault();
    $(target).scrollIntoView({ behavior: "smooth", block: "start" });
  });
}
$("inspectLink").addEventListener("click", () => saveForInspect());

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

async function start() {
  popover.install();
  popover.wire(app, main);
  readUrl();
  loadRules();
  $("rulesBtn").textContent = app.myRules.use ? "My rules · on" : "My rules";
  $("expr").value = app.text;
  grow();
  renderControls();
  renderExamples();
  app.bw = await loadWasm();
  if (!app.bw) {
    fill($("err"), h("div", { class: "notice" }, "Live runs need the WebAssembly module. Build it once: ", h("code", {}, "cargo build --release -p bitwright-wasm --target wasm32-unknown-unknown"), ", then reload. The ", h("a", { href: "inspect.html" }, "inspector"), " opens trace files without it."));
    $("err").hidden = false;
    $("status").textContent = "no WebAssembly module";
    return;
  }
  if (!app.text.trim()) load(EXAMPLES[0][1], EXAMPLES[0][2]);
  else runNow();
  renderRules();
}
start();

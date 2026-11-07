// The Trace view: the steps of one run down the side; for the chosen step, the whole expression
// before and after it, then the one card that explains it (the rule as written and proved, or
// the pass's reasoning), then, folded away, the tree it matched in and the sizes; and under it
// all a ribbon of the phases, round by round.

import { h, fill, chip, kv, kindClass } from "./dom.js";
import { print, opLabel, short } from "./print.js";
import { children, provenance } from "./model.js";
import { ruleCard, explainCard } from "./cards.js";

const cut = (s, n) => (s.length > n ? `${s.slice(0, n - 1)}…` : s);
const PHASE_LABEL = { local: "rules", fact_fold: "fold", linear_mba: "linear MBA" };

export function renderTrace(app, el) {
  const run = app.run;
  const steps = run.steps;
  if (app.step === null || app.step >= steps.length) app.step = steps.length ? 0 : null;
  const prov = provenance(run);
  const grid = h("div", { class: "pane-grid trace-grid" });
  const list = h("div", { class: "col steps", role: "listbox", "aria-label": "Steps" });
  const center = h("div", { class: "col center" });
  const ribbon = h("div", { class: "ribbon" });
  grid.append(list, center, ribbon);
  fill(el, grid);

  // Steps, grouped by root, round and phase.
  let key = null;
  const groupOf = (s) => (s.kind === "stage" ? `${s.root?.index ?? 0}:stage` : `${s.root?.index ?? 0}:${s.round}:${s.phase}`);
  const buttons = [];
  steps.forEach((s, i) => {
    const g = groupOf(s);
    if (g !== key) {
      key = g;
      const pname = s.phase === null ? "" : phaseLabel(run.phases[s.phase]?.name);
      const label = s.kind === "stage" ? "Before the rounds" : `Round ${s.round + 1} · ${pname}`;
      list.append(h("div", { class: "grp" }, (run.results.length > 1 ? `Root ${(s.root?.index ?? 0) + 1} · ` : "") + label));
    }
    const sb = run.sizes.size(s.whole.before);
    const sa = run.sizes.size(s.whole.after);
    const name = s.kind === "rule" ? s.name.split("::")[1] ?? s.name : s.kind === "fold" ? "fold" : s.name;
    const b = h(
      "button",
      { class: `step ${kindClass(s.kind)}${s.kind === "fold" ? " fold" : ""}`, role: "option", "data-i": i, title: s.kind === "rule" ? s.name : s.kind === "fold" ? "A fold by the constructors" : `${s.name} pass`, onclick: () => app.select(i) },
      h("span", { class: "i" }, String(s.index)),
      h("span", { class: "dot" }),
      h("span", { class: "nm" }, name),
      h("span", { class: `sz${sa < sb ? " down" : ""}`, title: `${sb} → ${sa} DAG nodes` }, sa < sb ? `−${sb - sa}` : sa > sb ? `+${sa - sb}` : "="),
    );
    buttons.push(b);
    list.append(b);
  });
  for (let r = 0; r < run.rounds; r++) {
    if (!steps.some((s) => s.round === r && s.kind !== "stage")) {
      list.append(h("div", { class: "grp" }, `Round ${r + 1}`), h("div", { class: "note-row" }, "nothing rewritten: a fixpoint"));
    }
  }
  if (steps.length === 0) list.append(h("div", { class: "note-row" }, "The run rewrote nothing."));

  const show = () => {
    buttons.forEach((b, i) => {
      b.classList.toggle("on", i === app.step);
      b.setAttribute("aria-selected", i === app.step ? "true" : "false");
    });
    const s = app.step === null ? null : steps[app.step];
    renderCenter(app, center, s, prov);
    renderRibbon(app, ribbon, s);
    center.scrollTop = 0;
  };
  app.onStep = show;
  show();
  const on = buttons[app.step];
  if (on) on.scrollIntoView({ block: "nearest" });
}

function phaseLabel(name) {
  return PHASE_LABEL[name] ?? (name ?? "").replace("_", " ");
}

function renderCenter(app, el, s, prov) {
  const run = app.run;
  const inner = h("div", { class: "center-inner" });
  fill(el, inner);
  if (!s) {
    const r = run.result;
    inner.append(
      h("div", { class: "step-head" }, h("h1", {}, "Nothing to rewrite")),
      h("p", { class: "step-sub" }, "The run changed nothing. The ribbon below shows the work it spent finding that out."),
      r ? h("div", { class: "xp" }, h("div", { class: "xp-row" }, h("span", { class: "label" }, "input"), h("div", { class: "code", html: print(run, r.input, { html: true, spans: true }) }))) : null,
    );
    return;
  }
  const n = run.steps.length;
  const sb = run.sizes.size(s.whole.before);
  const sa = run.sizes.size(s.whole.after);
  const where = s.kind === "stage" ? "before the rounds" : `round ${s.round + 1} · phase ${s.phase + 1} of ${run.phases.length}, ${phaseLabel(run.phases[s.phase]?.name)}`;
  const kindWord = { rule: s.by.rule?.kind === "identity" ? "identity" : "rule", pass: "pass", solver: "MBA service", fold: "constructor fold", stage: "stage" }[s.kind] ?? s.kind;
  inner.append(
    h(
      "div",
      { class: "step-head" },
      h("h1", {}, `Step ${s.index} of ${n}`),
      h(
        "span",
        { class: "nav" },
        h("button", { type: "button", title: "Previous step (k)", disabled: s.index === 1, onclick: () => app.select(s.index - 2) }, "‹"),
        h("button", { type: "button", title: "Next step (j)", disabled: s.index === n, onclick: () => app.select(s.index) }, "›"),
      ),
    ),
    h(
      "p",
      { class: "step-sub" },
      chip(s.kind, kindWord),
      h("span", { class: "name" }, s.kind === "fold" ? "the constructors folded a rebuilt node" : s.name),
      h("span", {}, `· ${where}`),
      h("span", {}, `· ${sb} → ${sa} nodes`),
    ),
  );
  inner.append(stepBody(app, run, s, prov));
}

/// The body of a step: the whole expression before and after it, the one card that explains
/// it, and, folded away, the tree it matched in and the sizes. Shared with the playground.
export function stepBody(app, run, s, prov) {
  const out = h("div", { class: "step-body" });
  const sb = run.sizes.size(s.whole.before);
  const k = kindClass(s.kind);
  const hl = s.whole.paths;
  out.append(
    h(
      "div",
      { class: `xp ${k}` },
      h("div", { class: "xp-row before" }, h("span", { class: "label" }, "before"), h("div", { class: "code", html: print(run, s.whole.before, { html: true, spans: true, highlight: hl }) })),
      h("div", { class: "xp-row" }, h("span", { class: "label" }, "after"), h("div", { class: "code", html: print(run, s.whole.after, { html: true, spans: true, highlight: hl }) })),
    ),
  );
  if (!s.whole.exact) out.append(h("p", { class: "xp-note warn" }, `This step could not be placed in the whole expression (the constructors reordered it). The subterm itself: ${cut(print(run, s.before), 160)} ⇒ ${cut(print(run, s.after), 160)}`));
  else if (hl.length > 1) out.append(h("p", { class: "xp-note" }, `The subterm occurs ${hl.length} times; every occurrence is rewritten.`));
  if (s.whole.phaseAfter !== undefined && run.sizes.key(s.whole.phaseAfter) !== run.sizes.key(s.whole.after)) {
    out.append(h("p", { class: "xp-note" }, `After this phase's last rewrite the engine's root reads ${cut(print(run, s.whole.phaseAfter), 160)}.`));
  }

  // The one card that explains the step.
  const why = h("div", { class: "why" });
  if (s.kind === "rule") {
    why.append(ruleCard(s.by.rule));
  } else if (s.kind === "fold") {
    why.append(
      h("div", { class: "why-head" }, h("h2", {}, "Folded by the constructors")),
      h("p", { class: "lead" }, "After a rewrite below it, this node was rebuilt over its operands' results, and the canonicalizing constructors turned it into something other than the same operator over them."),
      h("p", {}, "No rule or pass made this change: it is what building the node again gives. Nodes are hash-consed, so the result is whatever the constructors return for the new operands."),
    );
  } else if (s.kind === "stage") {
    why.append(h("div", { class: "why-head" }, chip("stage", "stage"), h("h2", {}, s.name)), h("p", { class: "lead" }, STAGE_TEXT[s.name] ?? "A rewrite of the whole root outside the phases."));
  } else {
    why.append(h("div", { class: "why-head" }, chip(s.kind, s.kind === "solver" ? "MBA service" : "pass"), h("h2", {}, s.name)), explainCard(run, s));
  }
  const links = [];
  const before = prov.get(s);
  if (before) links.push(["enabled by", h("span", { class: "sans" }, h("button", { class: "link", onclick: () => app.select(before.index - 1) }, `step ${before.index}`), ` (${before.name.split("::").pop()}): its pattern matched a node that step made`)]);
  const enables = [...prov].filter(([, e]) => e === s).map(([x]) => x);
  if (enables.length) links.push(["enables", h("span", {}, enables.map((x, i) => [i ? ", " : "", h("button", { class: "link", onclick: () => app.select(x.index - 1) }, `step ${x.index}`)]))]);
  if (s.relied && s.relied.length) links.push(["relies on", h("span", {}, s.relied.map((c) => [chip("assume", `#${c} ${assumeText(run, c)}`, true), " "]))]);
  if (s.folds && s.folds.length) links.push(["then", h("span", { class: "sans" }, `${s.folds.length} constructor fold${s.folds.length > 1 ? "s" : ""} above it`)]);
  if (s.kind === "rule") {
    const others = (run.attempts.get(s.before) ?? []).filter((a) => a.outcome !== "applied" && a.outcome !== "candidate");
    if (others.length) links.push(["also tried", h("span", { class: "sans" }, `${others.length} other rule${others.length > 1 ? "s" : ""} at this node: `, h("button", { class: "link", onclick: () => app.whyNot(s.before) }, "why not"))]);
  }
  if (links.length) {
    why.append(h("div", { class: "sep" }), kv(links.map(([a, b]) => [a, b])));
    for (const dd of why.querySelectorAll("dd")) if (dd.querySelector(".sans")) dd.classList.add("sans");
  }
  out.append(why);

  // Folded away: the tree and the sizes.
  const treeBody = h("div", { class: "body" });
  const drawTree = () => {
    const tree = h("div", { class: "tree" });
    const rows = renderTree(run, tree, s.whole.before, hl, s, app.treeFocus);
    const toggle = rows.total > 12 ? h("button", { type: "button", onclick: () => { app.treeFocus = !app.treeFocus; drawTree(); } }, app.treeFocus ? "Show everything" : "Fold what the step did not touch") : null;
    fill(treeBody, h("div", { class: "treehead" }, h("span", { class: "muted" }, rows.collapsed ? `${rows.collapsed === 1 ? "One subtree the step did not touch is" : `${rows.collapsed} subtrees the step did not touch are`} folded; click to open.` : "Every node; click one for its details."), toggle), tree);
    const first = tree.querySelector(".tr.hl");
    if (first) first.scrollIntoView({ block: "nearest" });
  };
  const treeDisc = h("details", { class: "disc", ontoggle: (e) => { if (e.target.open) drawTree(); } }, h("summary", {}, "Tree the step matched in ", h("span", { class: "n" }, `· ${sb} nodes before`)), treeBody);
  const chartDisc = h("details", { class: "disc" }, h("summary", {}, "Size after each step ", h("span", { class: "n" }, `· ${run.sizes.size(run.steps[0]?.whole.before ?? run.result?.input ?? 0)} → ${run.sizes.size(run.steps.at(-1)?.whole.after ?? 0)} nodes`)), h("div", { class: "body two-up" }, h("div", { class: "chart" }, sizeChart(app, s)), h("p", { class: "muted", style: { fontSize: "12px", margin: "0" } }, "Distinct DAG nodes after each step; shared subterms count once. A rule has to decrease the termination order, not the size, so a step may keep it.")));
  out.append(h("div", { class: "more" }, treeDisc, chartDisc));
  return out;
}

/// An indented tree of `t`, the subterms at `paths` marked with what replaced them. With
/// `focus`, subtrees off the marked paths fold into one row each (click to open). Returns the
/// row count and how many subtrees folded.
function renderTree(run, el, t, paths, s, focus) {
  const marks = new Set(paths.map((p) => p.join(".")));
  const onMarkPath = (p) => [...marks].some((m) => m === "" || p === m || p.startsWith(m + ".") || m.startsWith(p + "."));
  const seen = new Map();
  const opened = new Set();
  const out = { total: 0, collapsed: 0 };
  const draw = () => {
    el.replaceChildren();
    seen.clear();
    out.total = 0;
    out.collapsed = 0;
    let rows = 0;
    const walk = (x, path, depth) => {
      if (rows > 600) return;
      rows += 1;
      out.total += 1;
      const n = typeof x === "number" ? run.nodes.get(x) : x;
      const kids = children(run.nodes, x);
      const k = run.sizes.key(x);
      const p = path.join(".");
      const inMark = onMarkPath(p);
      const id = run.sizes.idOf(x);
      const row = h("div", { class: `tr ${kindClass(s.kind)}${inMark ? " hl" : ""}`, "data-n": id ?? undefined });
      row.style.setProperty("--d", String(depth));
      const size = kids.length ? run.sizes.size(x) : 1;
      if (focus && !inMark && depth > 0 && size > 2 && !opened.has(p)) {
        out.collapsed += 1;
        row.append(h("span", { class: "g" }), h("span", { class: "fold-row" }, `${short(run, x, 60)} · ${size} nodes`));
        row.title = "Open this subtree";
        row.removeAttribute("data-n");
        row.addEventListener("click", (e) => {
          e.stopPropagation();
          opened.add(p);
          draw();
        });
        el.append(row);
        return;
      }
      row.append(h("span", { class: "g" }), h("span", { class: kids.length ? "" : "leaf" }, opLabel(n)));
      if (marks.has(p)) row.append(h("span", { class: "to" }, `→ ${short(run, s.after, 50)}`));
      const again = seen.get(k);
      if (kids.length && again !== undefined) {
        row.append(h("span", { class: "tag", title: "Shared: shown once, above" }, "shared, as above"));
        el.append(row);
        return;
      }
      if (kids.length) seen.set(k, p);
      el.append(row);
      kids.forEach((c, i) => walk(c, [...path, i], depth + 1));
    };
    walk(t, [], 0);
    if (rows > 600) el.append(h("div", { class: "note-row" }, "Cut at 600 rows."));
  };
  draw();
  return out;
}

function sizeChart(app, s) {
  const run = app.run;
  const steps = run.steps;
  const sizes = [run.sizes.size(steps[0]?.whole.before ?? run.result?.input ?? 0), ...steps.map((x) => run.sizes.size(x.whole.after))];
  const max = Math.max(...sizes, 1);
  const W = 520;
  const H = 150;
  const L = 30;
  const R = 12;
  const T = 16;
  const B = 24;
  const x = (j) => L + (sizes.length === 1 ? 0 : (j * (W - L - R)) / (sizes.length - 1));
  const y = (v) => T + ((max - v) * (H - T - B)) / max;
  const ns = "http://www.w3.org/2000/svg";
  const svg = document.createElementNS(ns, "svg");
  svg.setAttribute("viewBox", `0 0 ${W} ${H}`);
  svg.setAttribute("role", "img");
  svg.setAttribute("aria-label", `DAG nodes per step: ${sizes.join(", ")}`);
  const add = (tag, attrs, text) => {
    const e = document.createElementNS(ns, tag);
    for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
    if (text !== undefined) e.textContent = text;
    svg.append(e);
    return e;
  };
  for (const v of [0, Math.round(max / 2), max]) {
    add("line", { x1: L, x2: W - R, y1: y(v), y2: y(v), stroke: "var(--line)" });
    add("text", { x: L - 7, y: y(v) + 3.5, "text-anchor": "end" }, String(v));
  }
  let d = `M${x(0)},${y(sizes[0])}`;
  for (let j = 1; j < sizes.length; j++) d += ` H${x(j)} V${y(sizes[j])}`;
  add("path", { d, fill: "none", stroke: "var(--ink-3)", "stroke-width": "1.5" });
  const cur = s ? s.index : 0;
  const colours = { rule: "var(--rule)", pass: "var(--pass)", solver: "var(--solver)", fold: "var(--stage)", stage: "var(--stage)", rewrite: "var(--stage)" };
  sizes.forEach((v, j) => {
    const col = j === 0 ? "var(--ink-3)" : colours[steps[j - 1].kind] ?? "var(--ink-3)";
    const on = j === cur;
    const c = add("circle", { cx: x(j), cy: y(v), r: on ? 5.5 : 3.5, fill: on ? col : "var(--surface)", stroke: col, "stroke-width": "1.5" });
    c.style.cursor = j > 0 ? "pointer" : "default";
    if (j > 0) {
      c.addEventListener("click", () => app.select(j - 1));
      c.append(Object.assign(document.createElementNS(ns, "title"), { textContent: `step ${j}: ${steps[j - 1].name} · ${v} nodes` }));
    }
    if (on) add("text", { x: x(j), y: y(v) - 10, "text-anchor": "middle", style: "fill:var(--ink);font-weight:600" }, String(v));
  });
  if (sizes.length <= 40) sizes.forEach((_, j) => add("text", { x: x(j), y: H - 7, "text-anchor": "middle" }, String(j)));
  return svg;
}

const STAGE_TEXT = {
  context: "What the root's conditions fix was put into the operands they guard (MBA noise forms).",
  sweep: "The opaque-constant sweep: fragments that take one value at every point were proved constant and replaced, before the first round.",
  cases: "Pieces that depend only on a few conditions were written as tables of their values (MBA noise forms, before every round).",
};

export function assumeText(run, c) {
  const a = run.assumptions[c];
  return a ? short(run, a.expr, 40) : "";
}

/// The phases of every round as a row of words; the ones that rewrote something stand out,
/// with a dot per rewrite and a red tick per candidate dropped; the current step's phase is
/// outlined.
function renderRibbon(app, el, s) {
  const run = app.run;
  const rows = [];
  for (let r = 0; r < run.rounds; r++) {
    const prs = run.phaseRuns.filter((p) => p.round === r);
    const row = h("div", { class: "rib-row" }, h("span", { class: "rib-r", title: `Round ${r + 1}` }, `R${r + 1}`));
    for (const pr of prs) {
      const first = run.steps.findIndex((x) => x.round === r && x.phase === pr.phase && x.kind !== "fold");
      const active = pr.applied > 0;
      const cur = s && s.round === r && s.phase === pr.phase;
      const work = pr.name === "local" ? `${pr.candidates} rule candidates` : `${pr.spent.node_visits ?? 0} node visits`;
      const tip = `${phaseLabel(pr.name)}, round ${r + 1}: ${work}, ${pr.applied} rewrite${pr.applied === 1 ? "" : "s"}${pr.notSmaller ? `, ${pr.notSmaller} candidate${pr.notSmaller > 1 ? "s" : ""} dropped as not smaller` : ""}${pr.folded ? `, ${pr.folded} fold${pr.folded > 1 ? "s" : ""}` : ""}${pr.stopped ? `; stopped: ${pr.stopped}` : ""}`;
      const kind = pr.name === "local" ? "rule" : pr.name === "mba" ? "solver" : "pass";
      const quiet = !active && !pr.notSmaller && !pr.stopped;
      const cell = h(
        first >= 0 ? "button" : "span",
        { class: `rib-ph ${kindClass(kind)}${active ? " act" : ""}${cur ? " cur" : ""}${quiet ? " quiet" : ""}${pr.stopped ? " stop" : ""}`, title: tip, "aria-label": tip, type: first >= 0 ? "button" : undefined, onclick: first >= 0 ? () => app.select(first) : null },
        h("span", {}, phaseLabel(pr.name)),
      );
      const dots = h("span", { class: "rib-dots" });
      for (let i = 0; i < Math.min(pr.applied, 6); i++) dots.append(h("i"));
      if (pr.applied > 6) dots.append(h("span", { class: "more" }, `+${pr.applied - 6}`));
      for (let i = 0; i < Math.min(pr.notSmaller, 4); i++) dots.append(h("b"));
      cell.append(dots);
      row.append(cell);
    }
    rows.push(row);
  }
  fill(
    el,
    rows,
    h(
      "div",
      { class: "rib-legend" },
      h("span", {}, "Each round's phases, in order. "),
      h("span", {}, h("span", { class: "dot k k-rule", style: { width: "5px", height: "5px" } }), " a rule rewrite  "),
      h("span", {}, h("span", { class: "dot k k-pass", style: { width: "5px", height: "5px" } }), " a pass rewrite  "),
      h("span", {}, h("span", { class: "dot k k-solver", style: { width: "5px", height: "5px" } }), " an MBA rewrite  "),
      h("span", {}, h("span", { class: "dot k k-miss", style: { width: "2px", height: "5px", borderRadius: "1px" } }), " a candidate dropped as not smaller"),
    ),
  );
}

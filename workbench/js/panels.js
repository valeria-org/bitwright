// The Stages, Why not, Facts, Corpus and Compare views.

import { h, fill, chip, kv, kindClass } from "./dom.js";
import { print, short } from "./print.js";
import { attemptList, census, corpusRows, alignPhases } from "./model.js";
import { factsBlock, valueText } from "./cards.js";
import { assumeText } from "./trace-view.js";

const cut = (s, n) => (s.length > n ? `${s.slice(0, n - 1)}…` : s);
const nodes = (n) => `${n} new node${n === 1 ? "" : "s"}`;

// ----- Stages ---------------------------------------------------------------------------------

/// The run as a filmstrip: each phase of each round, its work, and the root it left.
export function renderStages(app, el) {
  const run = app.run;
  const table = h("table", { class: "grid" });
  table.append(
    h(
      "thead",
      {},
      h(
        "tr",
        {},
        h("th", {}, "#"),
        h("th", {}, "Phase"),
        h("th", { class: "num" }, "Work"),
        h("th", { class: "num" }, "Rewrites"),
        h("th", { class: "num" }, "Not smaller"),
        h("th", {}, "Root the phase left"),
      ),
    ),
  );
  const body = h("tbody");
  let max = 1;
  for (const pr of run.phaseRuns) max = Math.max(max, pr.name === "local" ? pr.candidates : pr.spent.node_visits ?? 0);
  let round = null;
  for (const pr of run.phaseRuns) {
    if (pr.round !== round) {
      round = pr.round;
      const prs = run.phaseRuns.filter((p) => p.round === round);
      const rewrites = prs.reduce((a, p) => a + p.applied, 0);
      const visits = prs.reduce((a, p) => a + (p.spent.node_visits ?? 0), 0);
      const summary = `Round ${round + 1}: ${prs.length} phases, ${visits} node visits, ${rewrites} rewrite${rewrites === 1 ? "" : "s"}${rewrites === 0 ? ", fixpoint" : ""}`;
      body.append(h("tr", { class: "round" }, h("td", { colspan: "6" }, summary)));
    }
    const changed = run.sizes.key(pr.before) !== run.sizes.key(pr.after);
    const kind = pr.name === "local" ? "rule" : pr.name === "mba" ? "solver" : "pass";
    const work = pr.name === "local" ? pr.candidates : pr.spent.node_visits ?? 0;
    const first = run.steps.findIndex((s) => s.round === pr.round && s.phase === pr.phase && s.kind !== "fold");
    const row = h(
      "tr",
      { class: `${changed ? "chg " : ""}${first >= 0 ? "click " : ""}${kindClass(kind)}`, onclick: first >= 0 ? () => app.select(first, "trace") : null, title: first >= 0 ? "Open its first rewrite" : "" },
      h("td", { class: "num muted" }, String(pr.phase + 1)),
      h("td", {}, chip(kind, pr.name)),
      h(
        "td",
        { class: "num", title: Object.entries(pr.spent).map(([k, v]) => `${k} ${v}`).join(", ") },
        h("span", { class: "bar" }, h("i", { style: { width: `${(work / max) * 100}%` } })),
        ` ${work} ${pr.name === "local" ? "cand." : "visits"}`,
      ),
      h("td", { class: "num" }, String(pr.applied || "")),
      h("td", { class: "num", style: { color: pr.notSmaller ? "var(--miss)" : "" } }, String(pr.notSmaller || "")),
      h(
        "td",
        { class: "e", title: changed ? print(run, pr.after) : "" },
        changed ? `${cut(print(run, pr.after), 120)}  · ${run.sizes.size(pr.before)} → ${run.sizes.size(pr.after)}` : h("span", { class: "muted" }, pr.stopped ? `stopped: ${pr.stopped}` : "unchanged"),
      ),
    );
    body.append(row);
  }
  table.append(body);
  const r = run.result;
  fill(
    el,
    h(
      "div",
      { class: "sheet" },
      h("h2", {}, "Stages"),
      h("p", {}, "Each phase of each round, in the order the engine ran them: the work it spent, what it rewrote, the candidates it built and dropped, and the root it left. Rounds repeat until one changes nothing, so the last round is the fixpoint check."),
      r ? kv([["input", print(run, r.input)], ["result", print(run, r.expr)], ["ended", r.end + (r.stopped ? ` (${r.stopped})` : "")]]) : null,
      h("div", { class: "scroll" }, table),
    ),
  );
}

// ----- Why not --------------------------------------------------------------------------------

const OUTCOME = {
  applied: "applied",
  no_match: "no match",
  guard_false: "guard false",
  degraded: "out of work",
  no_change: "no change",
  not_smaller: "not smaller",
  rejected: "rejected",
  vetoed: "vetoed",
  candidate: "tried",
};

/// Every node the engine tried something at, and what each attempt came to.
export function renderWhyNot(app, el) {
  const run = app.run;
  const all = attemptList(run);
  const side = h("div", { class: "col nodes", role: "listbox", "aria-label": "Nodes" });
  const detail = h("div", { class: "col pad" });
  const search = h("input", { type: "search", placeholder: "Filter by text or rule", "aria-label": "Filter" });
  const missesOnly = h("input", { type: "checkbox", id: "missesOnly" });
  side.append(h("div", { class: "filter" }, search, h("label", { for: "missesOnly", class: "muted", style: { whiteSpace: "nowrap" } }, missesOnly, " misses")));
  const listEl = h("div");
  side.append(listEl);
  if (app.whyNode === null || !all.some((a) => a.id === app.whyNode)) {
    const firstMiss = all.find((a) => a.list.some((x) => x.outcome !== "applied"));
    app.whyNode = (firstMiss ?? all[0])?.id ?? null;
    app.sync();
  }
  const draw = () => {
    const q = search.value.trim().toLowerCase();
    listEl.replaceChildren();
    for (const { id, list } of all) {
      const misses = list.filter((a) => a.outcome !== "applied").length;
      if (missesOnly.checked && misses === 0) continue;
      const text = short(run, id, 70);
      const names = list.map((a) => (a.type === "rule" ? run.rules[a.rule]?.name ?? "" : a.pass)).join(" ");
      if (q && !text.toLowerCase().includes(q) && !names.toLowerCase().includes(q)) continue;
      const applied = list.length - misses;
      listEl.append(
        h(
          "button",
          {
            class: `n${id === app.whyNode ? " on" : ""}`,
            role: "option",
            "aria-selected": id === app.whyNode ? "true" : "false",
            onclick: () => {
              app.whyNode = id;
              app.sync();
              draw();
            },
          },
          text,
          h("small", {}, `${list.length} attempt${list.length > 1 ? "s" : ""}${applied ? ` · ${applied} applied` : ""}${misses ? ` · ${misses} not` : ""}`),
        ),
      );
    }
    drawDetail();
  };
  const drawDetail = () => {
    const entry = all.find((a) => a.id === app.whyNode);
    if (!entry) {
      fill(detail, h("p", { class: "muted" }, "No attempts recorded in this run."));
      return;
    }
    const rows = entry.list.map((a) => attemptRow(app, a));
    fill(
      detail,
      h("div", { class: "label" }, "Node"),
      h("div", { class: "code block", style: { margin: "6px 0 14px" }, html: print(run, entry.id, { html: true, spans: true }) }),
      factsBlock(run, entry.id, "its known bits"),
      rows,
    );
  };
  search.addEventListener("input", draw);
  missesOnly.addEventListener("change", draw);
  fill(el, h("div", { class: "pane-grid side-grid" }, side, detail));
  draw();
}

function attemptRow(app, a) {
  const run = app.run;
  const where = a.round === null || a.round === undefined ? "" : `round ${a.round + 1} · ${run.phases[a.phase]?.name ?? ""}`;
  if (a.type === "rule") {
    const rule = run.rules[a.rule];
    const ex = [];
    if (a.outcome === "guard_false") {
      ex.push(h("div", {}, "The guard did not hold: ", h("code", {}, `${a.pred ?? "?"}(${(a.args ?? []).filter((x) => x !== null).map((x) => short(run, x, 30)).join(", ")})`), " was not proved."));
      for (const x of a.args ?? []) {
        if (x === null) continue;
        const f = factsBlock(run, x, short(run, x, 24));
        if (f) ex.push(f);
      }
    } else if (a.outcome === "no_match") {
      ex.push(h("div", {}, "The dispatch net offered the rule, but its pattern does not match this node."));
    } else if (a.outcome === "degraded") {
      ex.push(h("div", {}, "Declined for lack of work or facts: the node may not be normal."));
    } else if (a.outcome === "no_change") {
      ex.push(h("div", {}, "Applied, and produced the node itself."));
    } else if (a.outcome === "applied" && a.step) {
      ex.push(h("div", {}, "Applied: ", h("button", { class: "link", onclick: () => app.select(a.step.index - 1, "trace") }, `step ${a.step.index}`)));
    } else if (a.reason) {
      ex.push(h("div", {}, `Rejected by a postcondition: ${a.reason}.`));
    }
    return h(
      "div",
      { class: "att" },
      h("span", { class: `o ${a.outcome}` }, OUTCOME[a.outcome] ?? a.outcome),
      h("span", { class: "who" }, rule ? rule.name : `rule ${a.rule}`, h("span", { class: "muted", style: { fontWeight: "400" } }, `  ${where}`)),
      h("div", { class: "ex" }, ex),
      rule?.source ? h("pre", {}, rule.source) : null,
    );
  }
  const ex = [];
  if (a.outcome === "not_smaller") {
    ex.push(
      h(
        "div",
        {},
        a.candidate === null || a.candidate === undefined
          ? `Its candidate would need up to ${nodes(a.added)}, and replacing the node frees ${a.freed}: not built.`
          : `Its candidate needs ${nodes(a.added)}, and replacing the node frees ${a.freed}.`,
        a.shared ? " Only sharing with another root kept it back; a later round decides again." : "",
      ),
    );
    if (a.candidate !== null && a.candidate !== undefined) ex.push(h("div", { class: "code small", style: { marginTop: "6px" }, html: print(run, a.candidate, { html: true, spans: true }) }));
  } else if (a.outcome === "applied" && a.step) {
    ex.push(h("div", {}, "Applied: ", h("button", { class: "link", onclick: () => app.select(a.step.index - 1, "trace") }, `step ${a.step.index}`)));
  } else if (a.reason) {
    ex.push(h("div", {}, `Rejected by a postcondition: ${a.reason}.`));
  }
  return h(
    "div",
    { class: "att" },
    h("span", { class: `o ${a.outcome}` }, OUTCOME[a.outcome] ?? a.outcome),
    h("span", { class: "who" }, chip(a.pass === "mba" ? "solver" : "pass", a.pass), h("span", { class: "muted", style: { fontWeight: "400" } }, `  ${where}`)),
    h("div", { class: "ex" }, ex),
  );
}

// ----- Facts ----------------------------------------------------------------------------------

/// The run's assumptions, what relied on each, and the facts of the nodes the trace names.
export function renderFacts(app, el) {
  const run = app.run;
  const withFacts = [...run.nodes.values()].filter((n) => n.facts);
  const side = h("div", { class: "col nodes" });
  const detail = h("div", { class: "col pad" });
  const uses = new Map();
  for (const s of run.steps) for (const c of s.relied ?? []) uses.set(c, [...(uses.get(c) ?? []), s]);
  side.append(h("div", { class: "grp" }, "Assumptions"));
  if (run.assumptions.length === 0) side.append(h("div", { class: "note-row" }, "This run had none."));
  run.assumptions.forEach((a, c) => {
    if (!a) return;
    const used = uses.get(c) ?? [];
    side.append(
      h(
        "div",
        { style: { padding: "6px 12px", borderBottom: "1px solid var(--line)" } },
        chip("assume", `#${c}`, true),
        " ",
        h("code", {}, print(run, a.expr)),
        h("div", { class: "muted", style: { fontSize: "11.5px", marginTop: "3px" } }, used.length ? ["used by ", used.map((s, i) => [i ? ", " : "", h("button", { class: "link", onclick: () => app.select(s.index - 1, "trace") }, `step ${s.index}`)])] : "not relied on"),
      ),
    );
  });
  const r = run.result;
  if (r && run.assumptions.length) {
    side.append(h("div", { class: "note-row" }, `The result relies on ${r.relies_on.length ? r.relies_on.map((c) => `#${c}`).join(", ") : "nothing"}.`));
  }
  const search = h("input", { type: "search", placeholder: "Filter nodes", "aria-label": "Filter nodes" });
  side.append(h("div", { class: "grp" }, "Nodes with facts"), h("div", { class: "filter" }, search));
  const listEl = h("div");
  side.append(listEl);
  if (withFacts.length === 0) {
    listEl.append(h("div", { class: "note-row" }, "The trace has no facts (written without Trace::with_facts)."));
  }
  if (app.factNode === null || !run.nodes.get(app.factNode)?.facts) {
    app.factNode = withFacts.find((n) => n.assumed)?.node ?? withFacts[0]?.node ?? null;
    app.sync();
  }
  const drawDetail = () => {
    for (const b of listEl.querySelectorAll("button.n")) b.classList.toggle("on", Number(b.dataset.id) === app.factNode);
    const n = run.nodes.get(app.factNode);
    if (!n) {
      fill(detail, h("p", { class: "muted" }, "Pick a node."));
      return;
    }
    const f = n.facts;
    const range = (x) => [
      ["unsigned", `[${valueText(x.u[0], n.w)}, ${valueText(x.u[1], n.w)}]${x.stride > 1 ? `, step ${x.stride}` : ""}`],
      ["signed", `[${x.s[0]}, ${x.s[1]}] as bit patterns`],
    ];
    fill(
      detail,
      h("div", { class: "label" }, `Node, ${n.w} bits`),
      h("div", { class: "code block", style: { margin: "6px 0 14px" }, html: print(run, n.node, { html: true, spans: true }) }),
      factsBlock(run, n.node, "known bits"),
      h("div", { class: "sep" }),
      h("div", { class: "label" }, "Without assumptions"),
      kv(range(f)),
      n.assumed ? [h("div", { class: "label", style: { color: "var(--assume)" } }, `Under the assumptions (relies on ${(n.assumed.relies ?? []).map((c) => `#${c} ${assumeText(run, c)}`).join(", ") || "nothing"})`), kv(range(n.assumed))] : null,
    );
  };
  const drawList = () => {
    const q = search.value.trim().toLowerCase();
    listEl.replaceChildren();
    for (const n of withFacts) {
      const text = short(run, n.node, 60);
      if (q && !text.toLowerCase().includes(q)) continue;
      listEl.append(
        h(
          "button",
          {
            class: `n${n.node === app.factNode ? " on" : ""}`,
            "data-id": n.node,
            onclick: () => {
              app.factNode = n.node;
              app.sync();
              drawDetail();
            },
          },
          text,
          h("small", {}, `${n.w} bits${n.assumed ? " · tighter under assumptions" : ""}`),
        ),
      );
    }
    drawDetail();
  };
  search.addEventListener("input", drawList);
  fill(el, h("div", { class: "pane-grid side-grid" }, side, detail));
  drawList();
}

// ----- Corpus ---------------------------------------------------------------------------------

const COLUMNS = [
  { key: "index", label: "#", num: true },
  { key: "input", label: "Input" },
  { key: "output", label: "Result" },
  { key: "width", label: "Bits", num: true, title: "Width of the symbols" },
  { key: "saved", label: "Nodes", num: true, title: "DAG nodes, before → after; sorted by nodes saved" },
  { key: "steps", label: "Steps", num: true },
  { key: "by", label: "By" },
  { key: "guardFalse", label: "Guard false", num: true },
  { key: "visits", label: "Visits", num: true },
  { key: "end", label: "End" },
];

/// One row per run of the file, a rule census over all of them, and the passes' totals.
export function renderCorpus(app, el) {
  const runs = app.runs;
  const all = corpusRows(runs).map((r, i) => ({ ...r, index: i + 1, saved: r.sizeIn - r.sizeOut, by: Object.keys(r.kinds).join(" ") }));
  const maxSize = Math.max(1, ...all.map((r) => r.sizeIn));
  const q = app.filter.trim().toLowerCase();
  let rows = q ? all.filter((r) => `${r.input} ${r.output} ${r.by}`.toLowerCase().includes(q)) : all;
  const { key, dir } = app.sort;
  rows = [...rows].sort((a, b) => {
    const x = a[key];
    const y = b[key];
    const c = typeof x === "number" && typeof y === "number" ? x - y : String(x ?? "").localeCompare(String(y ?? ""));
    return c * dir || a.index - b.index;
  });
  const search = h("input", {
    type: "search",
    placeholder: "Filter by input, result or rule",
    "aria-label": "Filter runs",
    value: app.filter,
    oninput: (e) => {
      app.filter = e.target.value;
      renderCorpus(app, el);
      const again = el.querySelector("input[type=search]");
      if (again) {
        again.focus();
        again.setSelectionRange(again.value.length, again.value.length);
      }
    },
  });
  const head = h(
    "tr",
    {},
    COLUMNS.map((c) =>
      h(
        "th",
        {
          class: `sortable${c.num ? " num" : ""}${key === c.key ? ` sorted${dir > 0 ? " asc" : ""}` : ""}`,
          title: c.title ?? `Sort by ${c.label.toLowerCase()}`,
          onclick: () => {
            app.sort = key === c.key ? { key, dir: -dir } : { key: c.key, dir: c.num ? -1 : 1 };
            renderCorpus(app, el);
          },
        },
        c.label,
      ),
    ),
  );
  const table = h(
    "table",
    { class: "grid" },
    h("thead", {}, head),
    h(
      "tbody",
      {},
      rows.map((r) =>
        h(
          "tr",
          { class: `click${r.run === app.run ? " sel" : ""}`, onclick: () => app.openRun(r.index - 1, "trace"), title: "Open its trace" },
          h("td", { class: "num muted" }, String(r.index)),
          h("td", { class: "e", title: r.input }, r.input),
          h("td", { class: "e", title: r.output }, r.output),
          h("td", { class: "num" }, String(r.width ?? "")),
          h("td", { class: "num" }, h("span", { class: "bar k k-pass" }, h("i", { style: { width: `${(r.sizeIn / maxSize) * 100}%` } }), h("b", { style: { width: `${(r.sizeOut / maxSize) * 100}%` } })), ` ${r.sizeIn} → ${r.sizeOut}`),
          h("td", { class: "num" }, String(r.steps)),
          h("td", { class: "by", title: Object.entries(r.kinds).map(([name, n]) => `${name}${n > 1 ? ` ×${n}` : ""}`).join(", ") }, Object.entries(r.kinds).slice(0, 2).map(([name, n]) => [chip(name.includes("::") ? "rule" : name === "mba" ? "solver" : "pass", `${name.includes("::") ? name.split("::")[1] : name}${n > 1 ? ` ×${n}` : ""}`), " "]), Object.keys(r.kinds).length > 2 ? h("span", { class: "muted" }, `+${Object.keys(r.kinds).length - 2}`) : null),
          h("td", { class: "num" }, String(r.guardFalse)),
          h("td", { class: "num" }, r.visits.toLocaleString()),
          h("td", { class: `end${r.end === "completed" ? " muted" : " warn"}` }, r.end === "completed" ? "ok" : `${r.end}${r.stopped ? `: ${r.stopped}` : ""}`, r.reliesOn.length ? h("span", { class: "muted" }, ` · relies ${r.reliesOn.map((c) => `#${c}`).join(",")}`) : null),
        ),
      ),
    ),
  );
  const cen = census(runs);
  const max = Math.max(1, ...cen.rules.map((c) => c.candidates));
  const ruleRows = cen.rules.slice(0, 40).map((c) =>
    h(
      "div",
      { class: "cen", title: Object.entries(c.preds).map(([p, n]) => `${p}: ${n}`).join(", ") },
      h("span", { style: { overflow: "hidden", textOverflow: "ellipsis", whiteSpace: "nowrap" } }, c.name),
      h(
        "span",
        { class: "b", style: { width: `${(c.candidates / max) * 100}%` } },
        c.applied ? h("i", { class: "a", style: { width: `${(c.applied / c.candidates) * 100}%` } }) : null,
        c.guard_false ? h("i", { class: "g", style: { width: `${(c.guard_false / c.candidates) * 100}%` } }) : null,
        c.no_match + c.degraded + c.no_change ? h("i", { class: "m", style: { width: `${((c.no_match + c.degraded + c.no_change) / c.candidates) * 100}%` } }) : null,
      ),
      h("span", { class: "c" }, `${c.applied} / ${c.candidates}`),
    ),
  );
  const passRows = h(
    "table",
    { class: "mini" },
    h("thead", {}, h("tr", {}, h("th", {}, "pass"), h("th", {}, "applied"), h("th", {}, "not smaller"), h("th", {}, "rejected"))),
    h("tbody", {}, cen.passes.map((p) => h("tr", {}, h("td", {}, p.name), h("td", {}, String(p.applied)), h("td", {}, String(p.not_smaller)), h("td", {}, String(p.rejected))))),
  );
  fill(
    el,
    h(
      "div",
      { class: "sheet" },
      h("h2", {}, runs.length > 1 ? `Corpus: ${runs.length} runs` : "One run"),
      h("p", {}, "Write one with bitwright simplify --file exprs.txt --trace corpus.bwt: each line runs alone, and its trace follows the one before. Click a row to open its trace, a column to sort."),
      h("div", { class: "toolbar" }, search, h("span", { class: "count" }, q ? `${rows.length} of ${all.length} runs` : `${all.length} runs`)),
      h("div", { class: "scroll" }, table),
      h(
        "div",
        { class: "two" },
        h(
          "div",
          {},
          h("h2", {}, "Rule census"),
          h("p", { class: "muted" }, "Applied / candidates, over every run. Blue applied, red guard false, grey no match. A rule tried often and rarely applied is dispatch work a narrower pattern would save."),
          ruleRows.length ? ruleRows : h("p", { class: "muted" }, "No rule was tried."),
        ),
        h("div", {}, h("h2", {}, "Passes"), h("p", { class: "muted" }, "Rewrites, and candidates dropped as not smaller, over every run."), passRows),
      ),
    ),
  );
}

// ----- Compare --------------------------------------------------------------------------------

/// Two runs side by side, phase by phase (aligned by name), round by round.
export function renderCompare(app, el) {
  const a = app.run;
  if (app.compareRun === null && a.result) {
    const text = print(a, a.result.input);
    app.compareRun = app.runs.find((r) => r !== a && r.result && print(r, r.result.input) === text) ?? null;
  }
  const b = app.compareRun;
  const bar = h("div", { class: "toolbar" });
  const pick = h("select", { "aria-label": "Run to compare with" });
  pick.append(h("option", { value: "" }, "Compare with…"));
  app.runs.forEach((r, i) => {
    if (r !== a) pick.append(h("option", { value: `run:${i}`, selected: b === r }, `run ${i + 1}: ${short(r, r.result?.input ?? 0, 50)} (${r.header.strategy})`));
  });
  (app.otherRuns ?? []).forEach((r, i) => pick.append(h("option", { value: `other:${i}`, selected: b === r }, `loaded: ${short(r, r.result?.input ?? 0, 50)} (${r.header.strategy})`)));
  pick.addEventListener("change", () => {
    const [kind, i] = pick.value.split(":");
    app.compareRun = kind === "run" ? app.runs[Number(i)] : kind === "other" ? app.otherRuns[Number(i)] : null;
    app.render();
  });
  const load = h("label", { class: "button" }, "Load another trace…", h("input", { type: "file", hidden: true, accept: ".bwt,.jsonl,.txt", onchange: (e) => app.loadOther(e.target.files[0]) }));
  bar.append(pick, load);
  if (app.live) {
    bar.append(
      h(
        "button",
        {
          onclick: () => app.liveCompare(),
          title: "Runs this input again with the other engine",
        },
        `Run with ${a.header.strategy === "standard" ? "deobfuscate + MBA" : "standard"}`,
      ),
    );
  }
  if (!b) {
    fill(el, h("div", { class: "sheet" }, h("h2", {}, "Compare"), h("p", {}, "Pick another run of this file, load a second trace (another strategy, budget, or engine version), or run the same input with the other engine."), bar));
    return;
  }
  const grid = h("div", { class: "cmp" });
  grid.append(h("div", { class: "h" }, "phase"), h("div", { class: "h" }, `A · ${a.header.strategy} ${a.header.version}`), h("div", { class: "h" }, `B · ${b.header.strategy} ${b.header.version}`));
  const rounds = Math.max(a.rounds, b.rounds);
  const cell = (run, pr) => {
    if (!pr) return h("div", { class: "na" }, "—");
    const changed = run.sizes.key(pr.before) !== run.sizes.key(pr.after);
    const kind = pr.name === "local" ? "rule" : pr.name === "mba" ? "solver" : "pass";
    return h(
      "div",
      { class: changed ? `ch ${kindClass(kind)}` : "muted", title: changed ? print(run, pr.after) : "" },
      changed ? `${short(run, pr.after, 70)} · ${run.sizes.size(pr.before)} → ${run.sizes.size(pr.after)} (${pr.applied})` : "unchanged",
    );
  };
  for (let r = 0; r < rounds; r++) {
    grid.append(h("div", { class: "rh" }, `Round ${r + 1}`));
    const pa = a.phaseRuns.filter((p) => p.round === r);
    const pb = b.phaseRuns.filter((p) => p.round === r);
    for (const [i, j] of alignPhases(pa.map((p) => p.name), pb.map((p) => p.name))) {
      const name = i !== null ? pa[i].name : pb[j].name;
      grid.append(h("div", {}, name), cell(a, i === null ? null : pa[i]), cell(b, j === null ? null : pb[j]));
    }
  }
  const res = (run) => (run.result ? `${short(run, run.result.expr, 80)} · ${run.sizes.size(run.result.input)} → ${run.sizes.size(run.result.expr)} nodes · ${run.stats?.node_visits ?? "?"} visits` : "");
  grid.append(h("div", { class: "rh" }, "Result"), h("div", {}, ""), h("div", {}, res(a)), h("div", {}, res(b)));
  const same = a.result && b.result && print(a, a.result.input) === print(b, b.result.input);
  fill(
    el,
    h(
      "div",
      { class: "sheet" },
      h("h2", {}, "Compare"),
      h("p", {}, "Phases aligned by name, round by round. A phase only one strategy has is hatched; a phase that changed the root shows the root it left and its rewrites."),
      bar,
      same ? null : h("p", { class: "warn" }, "The two runs have different inputs."),
      grid,
    ),
  );
}

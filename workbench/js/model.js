// The trace model: a `.bwt` file (JSON Lines, see `bitwright::engine::Trace`) parsed into runs,
// and everything the views derive from a run: steps, phases, attempts per node, snapshots of the
// whole expression after each step, sizes, and a census over many runs.
//
// No DOM here: the model runs under Node too (see `workbench/test`).

/// Splits a trace file into runs (each begins with its header line) and parses each.
export function parseTrace(text) {
  const runs = [];
  let cur = null;
  let lineNo = 0;
  for (const raw of text.split("\n")) {
    lineNo += 1;
    const line = raw.trim();
    if (line === "") continue;
    let obj;
    try {
      obj = JSON.parse(line);
    } catch (e) {
      throw new Error(`line ${lineNo}: not JSON (${e.message})`);
    }
    if (obj.trace !== undefined) {
      if (obj.trace !== "bitwright") throw new Error(`line ${lineNo}: not a bitwright trace`);
      cur = newRun(obj, runs.length);
      runs.push(cur);
      continue;
    }
    if (cur === null) throw new Error(`line ${lineNo}: no header line before it`);
    addLine(cur, obj);
  }
  if (runs.length === 0) throw new Error("no trace in the file (no header line)");
  return runs.map(finishRun);
}

function newRun(header, index) {
  return {
    index,
    header,
    phases: header.phases ?? [],
    rules: [],
    rewrites: [],
    nodes: new Map(),
    assumptions: [],
    events: [],
    results: [],
    stats: null,
  };
}

function addLine(run, o) {
  if (o.ev !== undefined) run.events.push(o);
  else if (o.node !== undefined && o.op !== undefined) run.nodes.set(o.node, o);
  else if (o.rule !== undefined && o.name !== undefined) run.rules[o.rule] = o;
  else if (o.rewrite !== undefined) run.rewrites[o.rewrite] = o;
  else if (o.assume !== undefined) run.assumptions[o.assume] = o;
  else if (o.result !== undefined) run.results[o.result] = o;
  else if (o.stats !== undefined) run.stats = o.stats;
  // Anything else is a kind of line this viewer does not know: skipped.
}

// ----- derived structure --------------------------------------------------------------------

const MBA = new Set(["mba"]);

/// What made a rewrite: `{ kind: "rule"|"pass"|"solver"|"rewrite", name, rule? }`.
export function maker(run, ev) {
  if (ev.rule !== undefined) {
    const r = run.rules[ev.rule];
    return { kind: "rule", name: r ? r.name : `rule ${ev.rule}`, rule: r };
  }
  if (ev.pass !== undefined) {
    return { kind: MBA.has(ev.pass) ? "solver" : "pass", name: ev.pass };
  }
  if (ev.rewrite !== undefined) {
    const r = run.rewrites[ev.rewrite];
    return { kind: "rewrite", name: r ? r.name : `rewrite ${ev.rewrite}` };
  }
  return { kind: "pass", name: "?" };
}

function finishRun(run) {
  const steps = [];
  const phaseRuns = [];
  const attempts = new Map(); // node id -> [attempt]
  const touch = (id) => {
    if (!attempts.has(id)) attempts.set(id, []);
    return attempts.get(id);
  };
  let round = null;
  let phase = null;
  let current = null; // the phase run under way
  let root = null;
  let lastStep = null;
  run.sizes = new Sizes(run.nodes);
  // The whole expression as the steps leave it: exact at every root, stage and phase
  // boundary; between them, each rewrite is replayed by structure (see `replace`).
  let whole = null;
  const replay = (s) => {
    if (whole === null) {
      s.whole = { before: s.before, after: s.after, paths: [[]], exact: false };
      return;
    }
    const { tree, paths } = replace(run, whole, s.before, s.after);
    s.whole = { before: whole, after: paths.length ? tree : whole, paths, exact: paths.length > 0 };
    if (paths.length) whole = tree;
  };
  for (const ev of run.events) {
    switch (ev.ev) {
      case "root":
        root = { index: ev.index, again: !!ev.again };
        whole = ev.root;
        break;
      case "phase_begin":
        whole = ev.root;
        round = ev.round;
        phase = ev.phase;
        current = {
          round,
          phase,
          name: run.phases[phase]?.name ?? `phase ${phase}`,
          before: ev.root,
          after: ev.root,
          applied: 0,
          kinds: {},
          notSmaller: 0,
          folded: 0,
          candidates: 0,
          spent: {},
          stopped: null,
          steps: [],
        };
        phaseRuns.push(current);
        break;
      case "phase_end":
        whole = ev.root;
        if (current) {
          current.after = ev.root;
          current.spent = ev.spent ?? {};
          current.stopped = ev.stopped ?? null;
        }
        current = null;
        break;
      case "stage": {
        const s = {
          kind: "stage",
          name: ev.stage,
          by: { kind: "stage", name: ev.stage },
          before: ev.before,
          after: ev.after,
          round,
          phase: null,
          root,
        };
        s.whole = { before: ev.before, after: ev.after, paths: [[]], exact: true };
        whole = ev.after;
        steps.push(s);
        lastStep = s;
        break;
      }
      case "candidate":
        if (current) current.candidates += 1;
        touch(ev.node).push({ type: "rule", rule: ev.rule, outcome: "candidate", round, phase });
        break;
      case "no_match":
      case "degraded":
      case "no_change":
      case "guard_false": {
        const list = ev.node != null ? touch(ev.node) : null;
        const last = list && list.length > 0 ? list[list.length - 1] : null;
        if (last && last.type === "rule" && last.rule === ev.rule && last.outcome === "candidate") {
          last.outcome = ev.ev;
          if (ev.pred) {
            last.pred = ev.pred;
            last.args = ev.args ?? [];
          }
        }
        break;
      }
      case "applied": {
        const by = maker(run, ev);
        const s = {
          kind: by.kind,
          name: by.name,
          by,
          before: ev.before,
          after: ev.after,
          round,
          phase,
          root,
          relied: null,
          explain: null,
          folds: [],
        };
        replay(s);
        steps.push(s);
        lastStep = s;
        if (current) {
          current.applied += 1;
          current.kinds[by.kind] = (current.kinds[by.kind] ?? 0) + 1;
          current.steps.push(s);
        }
        if (by.kind === "rule") {
          const list = touch(ev.before);
          const last = list[list.length - 1];
          if (last && last.type === "rule" && last.rule === ev.rule && last.outcome === "candidate") {
            last.outcome = "applied";
            last.step = s;
          } else {
            list.push({ type: "rule", rule: ev.rule, outcome: "applied", step: s, round, phase });
          }
        } else {
          touch(ev.before).push({ type: "pass", pass: by.name, outcome: "applied", step: s, round, phase });
        }
        break;
      }
      case "relied":
        if (lastStep && lastStep.relied === null) lastStep.relied = ev.on ?? [];
        break;
      case "explain":
        if (lastStep && lastStep.before === ev.node) lastStep.explain = ev.why;
        break;
      case "not_smaller":
        if (current) current.notSmaller += 1;
        touch(ev.node).push({
          type: "pass",
          pass: ev.pass,
          outcome: "not_smaller",
          candidate: ev.candidate,
          added: ev.added,
          freed: ev.freed,
          shared: ev.shared,
          round,
          phase,
        });
        break;
      case "folded": {
        if (current) current.folded += 1;
        const f = { kind: "fold", name: "constructor fold", by: { kind: "fold", name: "fold" }, before: ev.node, after: ev.after, round, phase, root };
        if (lastStep && lastStep.folds) lastStep.folds.push(f);
        replay(f);
        steps.push(f);
        break;
      }
      case "vetoed":
      case "rejected": {
        const by = maker(run, ev);
        const list = lastStep ? touch(lastStep.before) : null;
        if (list) list.push({ type: by.kind === "rule" ? "rule" : "pass", rule: ev.rule, pass: ev.pass, outcome: ev.ev, reason: ev.reason, round, phase });
        break;
      }
      default:
        break; // unknown event: skipped
    }
  }
  steps.forEach((s, i) => (s.index = i + 1));
  // Which step made each node, and which steps rewrote it (by structure).
  run.madeBy = new Map();
  run.rewrittenAt = new Map();
  for (const s of steps) {
    const ka = run.sizes.key(s.after);
    if (!run.madeBy.has(ka)) run.madeBy.set(ka, s);
    const kb = run.sizes.key(s.before);
    run.rewrittenAt.set(kb, [...(run.rewrittenAt.get(kb) ?? []), s]);
  }
  run.steps = steps;
  run.phaseRuns = phaseRuns;
  run.attempts = attempts;
  run.result = run.results[0] ?? null;
  run.rounds = phaseRuns.reduce((m, p) => Math.max(m, p.round + 1), 0);
  return run;
}

// ----- structure: keys, sizes, provenance ----------------------------------------------------

const COMMUTATIVE = new Set(["add", "mul", "and", "or", "xor"]);

/// Structural keys and DAG sizes of nodes and of virtual trees built over them.
class Sizes {
  constructor(nodes) {
    this.nodes = nodes;
    this.keys = new Map();
    this.ids = null;
  }

  /// A node of the trace with the structure of `t` (a node id or a virtual tree), if any.
  idOf(t) {
    if (typeof t === "number") return t;
    if (this.ids === null) {
      this.ids = new Map();
      for (const id of this.nodes.keys()) {
        const k = this.key(id);
        if (!this.ids.has(k)) this.ids.set(k, id);
      }
    }
    return this.ids.get(this.key(t)) ?? null;
  }

  /// A key equal for equal structures (hash-consed nodes: one per id).
  key(t) {
    if (typeof t === "number") {
      let k = this.keys.get(t);
      if (k === undefined) {
        const n = this.nodes.get(t);
        k = n ? nodeKey(n.op, n, (n.args ?? []).map((a) => this.key(a))) : `?${t}`;
        this.keys.set(t, k);
      }
      return k;
    }
    return nodeKey(t.op, t, t.args.map((a) => this.key(a)));
  }

  /// The number of distinct nodes in a tree (shared subterms once).
  size(t) {
    const seen = new Set();
    const walk = (x) => {
      const k = this.key(x);
      if (seen.has(k)) return;
      seen.add(k);
      for (const c of children(this.nodes, x)) walk(c);
    };
    walk(t);
    return seen.size;
  }
}

function nodeKey(op, n, kids) {
  const extra = [n.w, n.value ?? "", n.name ?? "", n.pred ?? "", n.lo ?? "", n.fp_op ?? "", n.output ?? ""].join(",");
  // The constructors order commutative operands: equal up to that order is equal.
  const ordered = COMMUTATIVE.has(op) || (op === "cmp" && (n.pred === "==" || n.pred === "!="));
  return `${op}(${extra}|${(ordered ? [...kids].sort() : kids).join(";")})`;
}

/// The operands of a node id or a virtual node.
export function children(nodes, t) {
  if (typeof t === "number") return nodes.get(t)?.args ?? [];
  return t.args;
}

/// Whether node id or virtual tree `t` contains node id `id` (by identity or structure).
export function contains(run, t, id) {
  const want = run.sizes.key(id);
  const seen = new Set();
  const walk = (x) => {
    const k = run.sizes.key(x);
    if (k === want) return true;
    if (seen.has(k)) return false;
    seen.add(k);
    return children(run.nodes, x).some(walk);
  };
  return walk(t);
}

/// For each step, the earlier step whose result it matched over (the rewrite it depends on).
export function provenance(run) {
  const byAfter = new Map();
  const out = new Map();
  for (const s of run.steps) {
    if (s.kind === "fold") continue;
    for (const [after, earlier] of byAfter) {
      if (after !== s.before && contains(run, s.before, after)) {
        out.set(s, earlier);
        break;
      }
    }
    byAfter.set(s.after, s);
  }
  return out;
}

// ----- snapshots: the whole expression after each step --------------------------------------

/// Replaces every occurrence of `target` (a node id, matched by structure, or by the node a
/// rebuilt virtual node came from) in tree `t` by `repl`, returning the new tree and the paths
/// replaced.
function replace(run, t, target, repl) {
  const want = run.sizes.key(target);
  const paths = [];
  const go = (x, path) => {
    if (run.sizes.key(x) === want || (typeof x !== "number" && x.origin === target)) {
      paths.push(path);
      return repl;
    }
    const kids = children(run.nodes, x);
    let changed = false;
    const next = kids.map((c, i) => {
      const r = go(c, [...path, i]);
      if (r !== c) changed = true;
      return r;
    });
    if (!changed) return x;
    const base = typeof x === "number" ? run.nodes.get(x) : x;
    const origin = typeof x === "number" ? x : x.origin;
    return { ...base, node: undefined, text: undefined, facts: undefined, assumed: undefined, args: next, virtual: true, origin };
  };
  const tree = go(t, []);
  return { tree, paths };
}

// ----- views' helpers -------------------------------------------------------------------------

/// The width of the symbols below node `id` (the widest), or the node's own width without
/// symbols: what `--width` was for the run that wrote it.
export function symbolWidth(run, id) {
  let w = 0;
  const seen = new Set();
  const walk = (x) => {
    if (seen.has(x)) return;
    seen.add(x);
    const n = run.nodes.get(x);
    if (!n) return;
    if (n.op === "sym") w = Math.max(w, n.w);
    for (const c of n.args ?? []) walk(c);
  };
  walk(id);
  return w || run.nodes.get(id)?.w || 64;
}

/// Everything the run says about one node (by structure): its attempts, the step that made it
/// and the steps that rewrote it.
export function aboutNode(run, t) {
  const id = run.sizes.idOf(t);
  const k = run.sizes.key(t);
  return {
    id,
    node: id === null ? null : run.nodes.get(id),
    attempts: id === null ? [] : (run.attempts.get(id) ?? []).filter((a) => a.outcome !== "candidate"),
    madeBy: run.madeBy.get(k) ?? null,
    rewrittenAt: run.rewrittenAt.get(k) ?? [],
  };
}

/// The text of a node: as the printer wrote it, when the trace has it.
export function textOf(run, id) {
  return run.nodes.get(id)?.text ?? null;
}

/// The rule attempts and pass attempts per node, as a list sorted by first appearance, for the
/// "why not" view.
export function attemptList(run) {
  const out = [];
  for (const [id, list] of run.attempts) {
    const real = list.filter((a) => a.outcome !== "candidate");
    if (real.length === 0) continue;
    out.push({ id, list: real });
  }
  return out;
}

/// A census of rule attempts over runs: per rule, candidates and outcomes.
export function census(runs) {
  const rules = new Map();
  const passes = new Map();
  for (const run of runs) {
    for (const [, list] of run.attempts) {
      for (const a of list) {
        if (a.type === "rule") {
          const r = run.rules[a.rule];
          const name = r ? r.name : `rule ${a.rule}`;
          if (!rules.has(name)) rules.set(name, { name, rule: r, candidates: 0, applied: 0, guard_false: 0, no_match: 0, degraded: 0, no_change: 0, rejected: 0, preds: {} });
          const c = rules.get(name);
          c.candidates += 1;
          const o = a.outcome === "candidate" ? "no_match" : a.outcome;
          if (o in c) c[o] += 1;
          else if (o === "vetoed") c.rejected += 1;
          if (a.pred) c.preds[a.pred] = (c.preds[a.pred] ?? 0) + 1;
        } else {
          const name = a.pass;
          if (!passes.has(name)) passes.set(name, { name, applied: 0, not_smaller: 0, rejected: 0 });
          const c = passes.get(name);
          if (a.outcome === "applied") c.applied += 1;
          else if (a.outcome === "not_smaller") c.not_smaller += 1;
          else c.rejected += 1;
        }
      }
    }
  }
  const byCount = (a, b) => b.candidates - a.candidates || a.name.localeCompare(b.name);
  return {
    rules: [...rules.values()].sort(byCount),
    passes: [...passes.values()].sort((a, b) => b.applied + b.not_smaller - (a.applied + a.not_smaller)),
  };
}

/// One row per run of a corpus.
export function corpusRows(runs) {
  return runs.map((run) => {
    const r = run.result;
    const kinds = {};
    for (const s of run.steps) {
      if (s.kind === "fold") continue;
      kinds[s.name] = (kinds[s.name] ?? 0) + 1;
    }
    let guardFalse = 0;
    for (const [, list] of run.attempts) for (const a of list) if (a.outcome === "guard_false") guardFalse += 1;
    return {
      run,
      input: r ? textOf(run, r.input) ?? "" : "",
      output: r ? textOf(run, r.expr) ?? "" : "",
      width: r ? symbolWidth(run, r.input) : null,
      sizeIn: r ? run.sizes.size(r.input) : 0,
      sizeOut: r ? run.sizes.size(r.expr) : 0,
      steps: run.steps.filter((s) => s.kind !== "fold").length,
      kinds,
      guardFalse,
      visits: run.stats?.node_visits ?? 0,
      end: r ? r.end : "?",
      stopped: r?.stopped ?? null,
      reliesOn: r?.relies_on ?? [],
    };
  });
}

/// Aligns two sequences of phase names (longest common subsequence): pairs of indices, `null`
/// where one side has no such phase.
export function alignPhases(a, b) {
  const n = a.length;
  const m = b.length;
  const dp = Array.from({ length: n + 1 }, () => new Array(m + 1).fill(0));
  for (let i = n - 1; i >= 0; i--) {
    for (let j = m - 1; j >= 0; j--) {
      dp[i][j] = a[i] === b[j] ? dp[i + 1][j + 1] + 1 : Math.max(dp[i + 1][j], dp[i][j + 1]);
    }
  }
  const out = [];
  let i = 0;
  let j = 0;
  while (i < n || j < m) {
    if (i < n && j < m && a[i] === b[j]) out.push([i++, j++]);
    else if (j < m && (i === n || dp[i][j + 1] >= dp[i + 1][j])) out.push([null, j++]);
    else out.push([i++, null]);
  }
  return out;
}

/// The phase runs of a run as `{ name, rounds: [phaseRun per round] }` rows.
export function phaseTable(run) {
  const rows = run.phases.map((p, i) => ({ index: i, name: p.name, groups: p.groups ?? null, rounds: [] }));
  for (const pr of run.phaseRuns) {
    if (rows[pr.phase]) rows[pr.phase].rounds[pr.round] = pr;
  }
  return rows;
}

export { COMMUTATIVE };

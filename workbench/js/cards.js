// The inspector's cards: a rule as written and proved, each pass's reasoning, known-bit lanes.

import { h, chip, kv } from "./dom.js";
import { print, short } from "./print.js";

const big = (s) => BigInt(s);

/// The signed reading of a `w`-bit value given as hex text.
export function signed(hex, w) {
  const v = big(hex);
  const top = 1n << BigInt(w - 1);
  return v >= top ? v - (1n << BigInt(w)) : v;
}

/// A value as hex with its signed decimal reading when that is short.
export function valueText(hex, w) {
  const v = big(hex);
  const s = signed(hex, w);
  if (v < 1024n) return v.toString();
  if (s < 0n && s > -1024n) return `${hex} (${s})`;
  return hex;
}

/// The known bits of a `w`-bit value as a lane, bit `w-1` on the left: `f(bit)` gives `u`
/// (unknown), `z` (known 0) or `o` (known 1); `marked(bit)` underlines a bit.
export function lane(w, f, marked) {
  const el = h("span", { class: "lane", title: `${w} bits, bit ${w - 1} on the left` });
  const bw = w > 32 ? 3 : w > 16 ? 6 : 9;
  for (let hi = w - 1; hi >= 0; hi -= 4) {
    const nib = h("span", { class: "nib" });
    for (let b = hi; b > hi - 4 && b >= 0; b--) {
      const i = h("i", { class: `${f(b)}${marked && marked(b) ? " dm" : ""}`, title: `bit ${b}` });
      i.style.setProperty("--bw", `${bw}px`);
      nib.append(i);
    }
    el.append(nib);
  }
  return el;
}

/// A lane from known-zero and known-one masks (hex text).
export function knownLane(w, zero, one, marked) {
  const z = big(zero);
  const o = big(one);
  return lane(w, (b) => ((o >> BigInt(b)) & 1n ? "o" : (z >> BigInt(b)) & 1n ? "z" : "u"), marked);
}

/// Known bits and intervals of a node's facts (and under assumptions, where they differ).
export function factsBlock(run, id, label) {
  const n = run.nodes.get(id);
  if (!n || !n.facts) return null;
  const w = n.w;
  const rows = [
    h("div", { class: "bitrow" }, h("span", { class: "nm", title: label ?? "" }, label ?? "facts"), knownLane(w, n.facts.zero, n.facts.one)),
  ];
  if (n.assumed) {
    rows.push(
      h(
        "div",
        { class: "bitrow" },
        h("span", { class: "nm" }, `assumed ${(n.assumed.relies ?? []).map((i) => `#${i}`).join(" ")}`),
        knownLane(w, n.assumed.zero, n.assumed.one),
      ),
    );
  }
  const range = (f) => `u ∈ [${valueText(f.u[0], w)}, ${valueText(f.u[1], w)}]${f.stride > 1 ? ` step ${f.stride}` : ""}`;
  rows.push(h("div", { class: "muted mono", style: { paddingLeft: "150px" } }, range(n.facts)));
  if (n.assumed) rows.push(h("div", { class: "mono", style: { paddingLeft: "150px", color: "var(--assume)" } }, `${range(n.assumed)} under assumptions`));
  return h("div", { class: "bits" }, rows);
}

/// The evidence a proof-ledger line records, as rows: `exhaustive(inst=6,maxw=6,…)`.
function ledgerRows(text) {
  if (!text) return [];
  const rows = [];
  const kind = text.split(" ")[0];
  for (const m of text.matchAll(/(\w+)\(([^)]*)\)/g)) {
    const f = Object.fromEntries(m[2].split(",").map((p) => p.split("=")));
    if (m[1] === "exhaustive") {
      const fired = f.fired && f.fired !== f.cases ? `, guard held in ${Number(f.fired).toLocaleString()}` : "";
      rows.push(["exhaustive", `widths 1–${f.maxw}: ${Number(f.cases).toLocaleString()} cases${fired}`]);
    } else if (m[1] === "sampled") {
      const fired = f.fired && f.fired !== f.cases ? `, guard held in ${Number(f.fired).toLocaleString()}` : "";
      rows.push(["sampled", `to 512 bits: ${f.inst} instances, ${Number(f.cases).toLocaleString()} cases${fired}`]);
    } else {
      rows.push([m[1], m[2]]);
    }
  }
  if (rows.length === 0) rows.push(["ledger", text]);
  return [["kind", kind], ...rows];
}

/// A rule as written, documented and proved.
export function ruleCard(rule) {
  if (!rule) return h("p", {}, "This rule is not described in the trace.");
  const ledger = ledgerRows(rule.ledger);
  const proof = [];
  if (rule.proven === false) proof.push("linked without a proof: sampled at every application");
  for (const [k, v] of ledger) if (k !== "kind") proof.push(`${k} ${v}`);
  return h(
    "div",
    {},
    h("div", { class: "why-head" }, chip("rule", rule.kind ?? "rule"), h("h2", {}, rule.name)),
    rule.doc ? h("p", { class: "lead" }, rule.doc) : null,
    rule.source ? h("pre", {}, rule.source) : h("p", { class: "muted" }, "No source text in the trace (a rule program of your own: give its source to Trace::with_source)."),
    kv([
      ...(rule.examples ?? []).slice(0, 2).map(([a, b], i) => [i === 0 ? "example" : "", `${a}  ⇒  ${b}`]),
      ["proved", proof.length ? h("span", { class: "sans" }, proof.join("; ")) : rule.proven ? "vouched for by its ledger" : null],
    ]),
  );
}

const RELH = ["=", "<u <s", "<u >s", ">u <s", ">u >s"];
const PREDS = {
  1: "x == y", 30: "x != y", 6: "x <u y", 24: "x >u y", 7: "x <=u y", 25: "x >=u y",
  10: "x <s y", 20: "x >s y", 11: "x <=s y", 21: "x >=s y", 0: "false", 31: "true",
};

/// A set of the five relations of a pair, as a row of cells.
export function relationRow(label, set, kclass = "k k-pass") {
  const row = [h("span", { class: "mono" }, label)];
  for (let b = 0; b < 5; b++) row.push(h("i", { class: (set >> b) & 1 ? "y" : "", title: RELH[b] }));
  return h("div", { class: `rel ${kclass}` }, [h("span"), ...RELH.map((r) => h("span", { class: "h" }, r))], row);
}

/// A pass's reasoning, by kind.
export function explainCard(run, step) {
  const why = step.explain;
  if (!why) {
    return h("p", { class: "muted" }, step.kind === "rule" ? "" : "No reasoning recorded for this rewrite (a trace written without explanations, or a route of the pass that records none).");
  }
  const w = run.nodes.get(step.before)?.w ?? 64;
  const name = (id) => short(run, id, 48);
  switch (why.kind) {
    case "fold":
      return h(
        "div",
        {},
        h("p", {}, "The node's known bits pin its value, so it becomes that constant."),
        h("div", { class: "bits" }, h("div", { class: "bitrow" }, h("span", { class: "nm" }, "known bits"), knownLane(w, why.zero, why.one))),
        kv([["value", valueText(why.value, w)], ["node", print(run, step.before)]]),
      );
    case "linear":
    case "carries":
      return h(
        "div",
        {},
        h("p", {}, why.kind === "linear" ? "Read as a linear sum c + Σ kᵢ·aᵢ over Z/2^W, then written back in canonical form." : "A carry network read as the affine form it computes" + (why.proved ? ", proved equal by the native prover." : " (a chain of shifts of one atom: equal by construction).")),
        h(
          "table",
          { class: "mini" },
          h("thead", {}, h("tr", {}, h("th", {}, "atom"), h("th", {}, "coefficient"))),
          h("tbody", {}, why.terms.map(([a, k]) => h("tr", {}, h("td", {}, name(a)), h("td", {}, valueText(k, w)))), h("tr", {}, h("td", { class: "muted" }, "constant"), h("td", {}, valueText(why.konst, w)))),
        ),
      );
    case "xor":
      return h(
        "div",
        {},
        h("p", {}, "Read as an xor sum k ⊕ ⊕ (aᵢ & mᵢ) over GF(2)^W, then written back in canonical form."),
        h("div", { class: "bits" }, why.terms.map(([a, m]) => h("div", { class: "bitrow" }, h("span", { class: "nm", title: print(run, a) }, name(a)), knownLane(w, notMask(m, w), m))), h("div", { class: "bitrow" }, h("span", { class: "nm" }, "constant k"), knownLane(w, notMask(why.konst, w), why.konst))),
        h("p", { class: "muted", style: { marginTop: "6px" } }, "Black: the bits of each atom's mask (and of the constant)."),
      );
    case "bitwise": {
      const atoms = why.atoms;
      const t = big(why.table);
      const rows = [];
      for (let i = 0; i < 1 << atoms.length; i++) {
        rows.push(h("tr", {}, atoms.map((_, k) => h("td", { class: (i >> k) & 1 ? "one" : "zero" }, (i >> k) & 1 ? "1" : "0")), h("td", { class: (t >> BigInt(i)) & 1n ? "one" : "zero" }, (t >> BigInt(i)) & 1n ? "1" : "0")));
      }
      return h(
        "div",
        {},
        h("p", {}, `A function of ${atoms.length} atom${atoms.length === 1 ? "" : "s"}, written as the minimum form of its truth table (every bit position alike).`),
        h("table", { class: "tt" }, h("thead", {}, h("tr", {}, atoms.map((a) => h("th", { title: print(run, a) }, name(a))), h("th", {}, "value"))), h("tbody", {}, rows)),
      );
    }
    case "relations":
      return h(
        "div",
        {},
        h("p", {}, "Two values stand in exactly one of five relations; every predicate on the pair is a set of them, and & | ^ ~ are set operations."),
        relationRow(`${name(why.x)} vs ${name(why.y)}`, why.set),
        kv([["set", PREDS[why.set] ?? `{${RELH.filter((_, b) => (why.set >> b) & 1).join(", ")}}`]]),
      );
    case "intervals":
      return h(
        "div",
        {},
        h("p", {}, "A set of values of one operand, as intervals; written as one comparison or range check."),
        kv([["operand", name(why.x)], ...why.set.map(([lo, hi], i) => [i === 0 ? "values" : "", `[${valueText(lo, w)}, ${valueText(hi, w)}]`])]),
      );
    case "linear_mba": {
      const atoms = why.atoms;
      return h(
        "div",
        {},
        h("p", {}, `A linear combination of bitwise functions of ${atoms.length} atoms, fixed by its values at the corners where each atom is all zeros or all ones; written as ${why.form}.`),
        h(
          "table",
          { class: "mini" },
          h("thead", {}, h("tr", {}, atoms.map((a) => h("th", { title: print(run, a) }, name(a))), h("th", {}, "value"))),
          h("tbody", {}, why.corners.map((v, p) => h("tr", {}, atoms.map((_, k) => h("td", {}, (p >> k) & 1 ? "−1" : "0")), h("td", {}, valueText(v, w))))),
        ),
      );
    }
    case "shuffle": {
      const sources = new Map();
      const cells = why.bits.map((b) => {
        if (b === 0 || b === 1) return String(b);
        const [of, bit] = b;
        if (!sources.has(of)) sources.set(of, String.fromCharCode(97 + sources.size));
        return `${sources.get(of)}${bit}`;
      });
      const row = h("div", { class: "mono", style: { display: "flex", flexWrap: "wrap", gap: "2px", fontSize: "10.5px" } });
      for (let i = cells.length - 1; i >= 0; i--) row.append(h("span", { title: `bit ${i}`, style: { border: "1px solid var(--line)", borderRadius: "2px", padding: "1px 3px", minWidth: "26px", textAlign: "center" } }, cells[i]));
      return h(
        "div",
        {},
        h("p", {}, "Each bit of the result traced to the bit it comes from (bit " + (cells.length - 1) + " on the left)."),
        row,
        kv([...sources].map(([of, l]) => [l, name(of)])),
      );
    }
    case "casts": {
      const sw = run.nodes.get(why.source)?.w ?? w;
      const lo = why.lo;
      const hi = why.lo + why.bits;
      return h(
        "div",
        {},
        h("p", {}, why.sign_extended ? "A sign extension written with shifts, read as one: the low bits of the value, sign-extended back." : `Only bits ${hi - 1}–${lo} of the value are read, so the narrowing was pushed into it, through the operations that keep those bits.`),
        h("div", { class: "bits" }, h("div", { class: "bitrow" }, h("span", { class: "nm" }, "bits read"), lane(sw, (b) => (b >= lo && b < hi ? "o" : "z")))),
        kv([["value", print(run, why.source)]]),
      );
    }
    case "demanded": {
      const ow = run.nodes.get(why.operand)?.w ?? w;
      return h(
        "div",
        {},
        h("p", {}, "The operand is observed only through some bits, and was simplified under those bits."),
        h("div", { class: "bits" }, h("div", { class: "bitrow" }, h("span", { class: "nm" }, "observed"), knownLane(ow, notMask(why.mask, ow), why.mask))),
        kv([["operand", print(run, why.operand)]]),
      );
    }
    case "invert":
      return h(
        "div",
        {},
        h("p", {}, "Injective layers undone from the compared side down to the value, each with the preimage of the constant under it."),
        h(
          "div",
          { class: "chain" },
          h("div", { class: "label" }, "layer"),
          h("div", { class: "label", style: { textAlign: "right" } }, "preimage"),
          why.layers.flatMap((l) => [
            h("div", { class: "lay" }, l.map, h("small", {}, `${l.bijective ? "bijective" : "injective"} · over ${short(run, l.inner, 40)}`)),
            h("div", { class: "pre" }, l.preimage === null ? "none" : valueText(l.preimage, run.nodes.get(l.inner)?.w ?? w)),
          ]),
        ),
      );
    case "division":
      return h(
        "div",
        {},
        h("p", {}, "A multiplication by a magic number recognized as a division by a constant, proved exact for every value the dividend can take."),
        kv([["dividend", print(run, why.dividend)], ["divisor", valueText(why.divisor, w)], ["signed", why.signed ? "yes" : "no"]]),
      );
    case "mba":
      return h(
        "div",
        {},
        h("p", {}, "The fragment was lowered over its atoms, simplified by the solver, and lifted back."),
        kv([
          ["atoms", why.atoms.map((a) => name(a)).join(", ")],
          ["evidence", why.evidence === "certificate" ? "bitwright's own certificate" : why.evidence],
          ["test", why.test ?? null],
          ["points", why.points ? String(why.points) : null],
        ]),
      );
    default:
      return h("pre", {}, JSON.stringify(why, null, 1));
  }
}

function notMask(hex, w) {
  const m = (1n << BigInt(w)) - 1n;
  return `0x${(m & ~big(hex)).toString(16)}`;
}

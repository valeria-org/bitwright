// Printing expressions from a trace's node table (and the virtual trees the model builds over
// it) the way bitwright's own printer does (`bitwright/src/text/print.rs`): its precedences, its
// literals, and `let` names for shared subterms. Optionally with highlights.

import { children } from "./model.js";

// Precedence levels, as the engine's printer has them; higher binds tighter.
const P_CMP = 1;
const P_OR = 2;
const P_XOR = 3;
const P_AND = 4;
const P_SHIFT = 5;
const P_SUM = 6;
const P_PROD = 7;
const P_UNARY = 8;
const P_ATOM = 9;

const INFIX = {
  add: ["+", P_SUM],
  sub: ["-", P_SUM],
  mul: ["*", P_PROD],
  shl: ["<<", P_SHIFT],
  lshr: [">>u", P_SHIFT],
  ashr: [">>s", P_SHIFT],
  and: ["&", P_AND],
  xor: ["^", P_XOR],
  or: ["|", P_OR],
};
const UNARY = { not: "~", neg: "-" };

/// The signed reading of a node's value, when it is a negative number above -65536.
function smallNegative(n) {
  if (n.w <= 1) return null;
  const v = BigInt(n.value);
  const top = 1n << BigInt(n.w - 1);
  if (v < top) return null;
  const s = v - (1n << BigInt(n.w));
  return s >= -65536n ? s : null;
}

/// A constant's spelling, without its width: 0 or 1 for one bit, a small negative number, a
/// decimal below 65536, else hexadecimal.
export function constText(n) {
  const v = BigInt(n.value);
  if (n.w === 1) return v === 0n ? "0" : "1";
  const neg = smallNegative(n);
  if (neg !== null) return neg.toString();
  if (v < 65536n) return v.toString();
  return `0x${v.toString(16)}`;
}

/// The operator of a node as one short token, for trees and tables.
export function opLabel(n) {
  if (!n) return "?";
  switch (n.op) {
    case "const":
      return constText(n);
    case "sym":
      return n.name ?? "?";
    case "cmp":
      return n.pred;
    case "zext":
    case "sext":
      return `${n.op}<${n.w}>`;
    case "extract":
      return n.lo === 0 ? `trunc<${n.w}>` : `extract<${n.lo}, ${n.w}>`;
    case "fp":
      return n.fp_op ?? "fp";
    default:
      return INFIX[n.op]?.[0] ?? UNARY[n.op] ?? n.op;
  }
}

const isPrefix = (a, b) => a.length <= b.length && a.every((v, i) => v === b[i]);

/// Prints `t` (a node id or a virtual tree). Options: `highlight`, paths (arrays of operand
/// positions from `t`) to mark; `html`, to escape and wrap each marked subterm in `<mark>`;
/// `spans` (with `html`), to wrap every subterm the trace knows as a node in
/// `<span class="t" data-n="id">`; `lets` (default true), to name subterms used more than once.
export function print(run, t, opts = {}) {
  const html = !!opts.html;
  const spans = html && !!opts.spans;
  const esc = (s) => (html ? s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;") : s);
  const marks = opts.highlight ?? [];
  const markKeys = new Set(marks.map((p) => p.join(".")));
  // A subterm on or around a marked path stays inline, so the mark can show (a mark on the
  // whole expression keeps the names).
  const inner = marks.filter((m) => m.length > 0);
  const nearMark = (path) => inner.some((m) => isPrefix(path, m) || isPrefix(m, path));
  const node = (x) => (typeof x === "number" ? run.nodes.get(x) : x);
  const key = (x) => run.sizes.key(x);

  // Uses (one per parent, each parent expanded once) and the post-order, as the engine counts.
  const uses = new Map([[key(t), 0]]);
  const order = [];
  const firstPath = new Map([[key(t), []]]);
  const visit = (x, path) => {
    children(run.nodes, x).forEach((c, i) => {
      const k = key(c);
      const u = (uses.get(k) ?? 0) + 1;
      uses.set(k, u);
      if (u === 1) {
        firstPath.set(k, [...path, i]);
        visit(c, [...path, i]);
      }
    });
    order.push(x);
  };
  visit(t, []);
  const names = new Map();
  const lets = [];
  const rootKey = key(t);
  const bound = opts.lets === false ? [] : order.filter((x) => {
    const k = key(x);
    return k !== rootKey && children(run.nodes, x).length > 0 && uses.get(k) >= 2 && !nearMark(firstPath.get(k));
  });

  const literal = (n, annotate, minPrec) => {
    let s = constText(n);
    if (annotate) s += `:${n.w}`;
    const neg = smallNegative(n) !== null;
    return (neg ? P_UNARY : P_ATOM) < minPrec ? `(${s})` : s;
  };
  const isLit = (x) => node(x)?.op === "const";

  // `x` inline: bound subterms by name (but `x` itself, when `self` is set).
  const inline = (x, path, minPrec, annotate, self = false) => {
    const k = key(x);
    let s;
    if (!self && names.has(k)) s = names.get(k);
    else s = term(x, path, minPrec, annotate);
    if (spans) {
      const id = run.sizes.idOf(x);
      if (id !== null) s = `<span class="t" data-n="${id}">${s}</span>`;
    }
    return html && markKeys.has(path.join(".")) ? `<mark>${s}</mark>` : s;
  };
  const term = (x, path, minPrec, annotate) => {
    const n = node(x);
    if (!n) return esc(`?${x}`);
    const kids = children(run.nodes, x);
    const at = (i, p, a = false) => inline(kids[i], [...path, i], p, a);
    let s;
    let prec = P_ATOM;
    switch (n.op) {
      case "const":
        return esc(literal(n, annotate, minPrec));
      case "sym":
        return esc(n.name ?? "?");
      case "cmp":
        prec = P_CMP;
        s = `${at(0, P_CMP + 1)} ${esc(n.pred)} ${at(1, P_CMP + 1)}`;
        break;
      case "zext":
      case "sext":
      case "extract":
        s = `${esc(opLabel(n))}(${at(0, 0, true)})`;
        break;
      case "concat":
        s = `concat(${at(0, 0, true)}, ${at(1, 0, true)})`;
        break;
      case "select": {
        const both = isLit(kids[1]) && isLit(kids[2]);
        s = `select(${at(0, 0)}, ${at(1, 0, both)}, ${at(2, 0)})`;
        break;
      }
      default:
        if (n.op === "add" && kids.length === 2 && isLit(kids[1]) && n.w > 1 && smallNegative(node(kids[1])) !== null) {
          // x + (-c) prints as x - c.
          prec = P_SUM;
          s = `${at(0, P_SUM)} - ${(-smallNegative(node(kids[1]))).toString()}`;
        } else if (INFIX[n.op] && kids.length === 2) {
          const [sym, p] = INFIX[n.op];
          prec = p;
          s = `${at(0, p)} ${esc(sym)} ${at(1, p + 1)}`;
        } else if (UNARY[n.op] && kids.length === 1) {
          prec = P_UNARY;
          s = `${esc(UNARY[n.op])}${at(0, P_UNARY)}`;
        } else {
          const name = n.op === "fp" ? n.fp_op ?? "fp" : n.op;
          s = `${esc(name)}(${kids.map((_, i) => at(i, 0, n.op === "ext")).join(", ")})`;
        }
    }
    return prec < minPrec ? `(${s})` : s;
  };
  bound.forEach((x, i) => {
    const k = key(x);
    lets.push(`let %${i} = ${inline(x, firstPath.get(k), 0, false, true)};`);
    names.set(k, `%${i}`);
  });
  const main = inline(t, [], 0, true);
  return lets.length === 0 ? main : `${lets.join(" ")} ${main}`;
}

/// Prints `t` without names for shared subterms, cut to `max` characters.
export function short(run, t, max = 64) {
  const s = print(run, t, { lets: false });
  return s.length > max ? `${s.slice(0, max - 1)}…` : s;
}

// ----- LaTeX ---------------------------------------------------------------------------------

const TEX_INFIX = {
  add: ["+", P_SUM],
  sub: ["-", P_SUM],
  mul: ["\\cdot", P_PROD],
  shl: ["\\ll", P_SHIFT],
  lshr: ["\\gg_{u}", P_SHIFT],
  ashr: ["\\gg_{s}", P_SHIFT],
  and: ["\\land", P_AND],
  xor: ["\\oplus", P_XOR],
  or: ["\\lor", P_OR],
};
const TEX_CMP = { "==": "=", "!=": "\\neq", "<u": "<_{u}", "<=u": "\\leq_{u}", "<s": "<_{s}", "<=s": "\\leq_{s}", ">u": ">_{u}", ">=u": "\\geq_{u}", ">s": ">_{s}", ">=s": "\\geq_{s}" };

/// `t` as LaTeX math (no `let`s: every subterm inline). Symbols' names are escaped.
export function latex(run, t) {
  const node = (x) => (typeof x === "number" ? run.nodes.get(x) : x);
  const name = (s) => s.replace(/[\\{}_^%$&#]/g, (c) => `\\${c}`);
  const go = (x, minPrec) => {
    const n = node(x);
    if (!n) return "?";
    const kids = children(run.nodes, x);
    const at = (i, p) => go(kids[i], p);
    let s;
    let prec = P_ATOM;
    switch (n.op) {
      case "const": {
        const v = BigInt(n.value);
        const neg = smallNegative(n);
        if (neg !== null) {
          prec = P_UNARY;
          s = `-${(-neg).toString()}`;
        } else s = v < 65536n ? v.toString() : `\\mathtt{0x${v.toString(16)}}`;
        break;
      }
      case "sym":
        s = (n.name ?? "?").length > 1 ? `\\mathit{${name(n.name)}}` : name(n.name ?? "?");
        break;
      case "cmp":
        prec = P_CMP;
        s = `${at(0, P_CMP + 1)} ${TEX_CMP[n.pred] ?? n.pred} ${at(1, P_CMP + 1)}`;
        break;
      case "zext":
      case "sext":
        s = `\\mathrm{${n.op}}_{${n.w}}\\!\\left(${at(0, 0)}\\right)`;
        break;
      case "extract":
        s = n.lo === 0 ? `\\mathrm{trunc}_{${n.w}}\\!\\left(${at(0, 0)}\\right)` : `${at(0, P_ATOM)}[${n.lo + n.w - 1}{:}${n.lo}]`;
        break;
      case "concat":
        prec = P_OR;
        s = `${at(0, P_OR + 1)} \\,\\Vert\\, ${at(1, P_OR + 1)}`;
        break;
      case "select":
        s = `\\mathrm{ite}\\!\\left(${at(0, 0)},\\, ${at(1, 0)},\\, ${at(2, 0)}\\right)`;
        break;
      default:
        if (TEX_INFIX[n.op] && kids.length === 2) {
          const [sym, p] = TEX_INFIX[n.op];
          prec = p;
          s = `${at(0, p)} ${sym} ${at(1, p + 1)}`;
        } else if (n.op === "not" && kids.length === 1) {
          prec = P_UNARY;
          s = `\\lnot ${at(0, P_UNARY)}`;
        } else if (n.op === "neg" && kids.length === 1) {
          prec = P_UNARY;
          s = `-${at(0, P_UNARY)}`;
        } else {
          const f = n.op === "fp" ? n.fp_op ?? "fp" : n.op;
          s = `\\mathrm{${name(f)}}\\!\\left(${kids.map((_, i) => at(i, 0)).join(",\\, ")}\\right)`;
        }
    }
    return prec < minPrec ? `\\left(${s}\\right)` : s;
  };
  return go(t, 0);
}

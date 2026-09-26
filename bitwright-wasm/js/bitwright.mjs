// bitwright in WebAssembly: `const bw = await instantiate(bytes)`, then `bw.simplify(text)`.
// `bytes` is the module (`bitwright_wasm.wasm`) as an ArrayBuffer, a typed array, or a fetch
// Response. Every function takes and returns strings, and throws an Error with bitwright's
// message on failure.
//
// Host rewrites are JavaScript functions `(site, node) => handle | null`, called while the
// engine runs. They see nodes as BigInt handles of the expression being simplified, through the
// `site` (valid during the call only): `kind`, `op`, `children`, `width`, `lo`, `value`,
// `facts` and `print` to inspect, and `constant`, `un`, `bin`, `cmp`, `zext`, `sext`, `trunc`,
// `extract`, `concat` and `select` to build (each null when it cannot). An exception a rewrite
// throws is rethrown when the call ends.

const OPS = {
  simplify: 0,
  simplifyStandard: 1,
  synthesize: 2,
  prove: 3,
  validate: 4,
  infer: 5,
  lift: 6,
  equivalent: 7,
  toSmtlib: 8,
  version: 9,
  simplifyWith: 10,
  checkRewrite: 11,
  template: 12,
  checkTemplate: 13,
  names: 14,
};

const FRONT_ENDS = { pcode: 0, vex: 1, llvm: 2 };

// A word of an option line: no spaces, no line breaks.
function word(s, what) {
  const w = String(s);
  if (w === "" || /\s/.test(w)) {
    throw new Error(`${what} ${JSON.stringify(w)} must be one word`);
  }
  return w;
}

const hex = (v) => `0x${BigInt(v).toString(16)}`;

// `node_visits=3 host.changed=1` as `{ nodeVisits: 3, host: { changed: 1 } }`.
function parseStats(line) {
  const stats = { host: {} };
  for (const field of line.split(" ")) {
    const [key, value] = field.split("=");
    const camel = key.replace(/_(\w)/g, (_, c) => c.toUpperCase());
    if (camel.startsWith("host.")) {
      stats.host[camel.slice(5)] = Number(value);
    } else {
      stats[camel] = Number(value);
    }
  }
  return stats;
}

export async function instantiate(bytes) {
  const source = bytes instanceof Response ? await bytes.arrayBuffer() : bytes;
  // The rewrites of the call running now, the site they see, and what they threw.
  let active = null;
  const imports = {
    bitwright: {
      rewrite: (index, node) => {
        const call = active;
        if (call === null) {
          return 0n;
        }
        try {
          const out = call.rewrites[index].rewrite(call.site, node);
          return out == null ? 0n : BigInt.asUintN(64, BigInt(out));
        } catch (err) {
          call.errors.push(err);
          return 0n;
        }
      },
    },
  };
  const { instance } = await WebAssembly.instantiate(source, imports);
  const ex = instance.exports;
  const enc = new TextEncoder();
  const dec = new TextDecoder();

  function put(s) {
    const b = enc.encode(s);
    const p = ex.bw_alloc(b.length);
    new Uint8Array(ex.memory.buffer, p, b.length).set(b);
    return [p, b.length];
  }

  function call(op, a = "", b = "", n = 0) {
    const [ap, al] = put(a);
    const [bp, bl] = put(b);
    const r = ex.bw_call(op, ap, al, bp, bl, n);
    ex.bw_dealloc(ap, al);
    ex.bw_dealloc(bp, bl);
    // Memory may have grown: views are made after the call.
    const view = new DataView(ex.memory.buffer);
    const status = view.getUint8(r);
    const len = view.getUint32(r + 1, true);
    const text = dec.decode(new Uint8Array(ex.memory.buffer, r + 5, len));
    ex.bw_dealloc(r, len + 5);
    if (status !== 0) {
      throw new Error(text);
    }
    return text;
  }

  // The text of a buffer a `bw_site_*` export returns, or null.
  function take(r) {
    const view = new DataView(ex.memory.buffer);
    const status = view.getUint8(r);
    const len = view.getUint32(r + 1, true);
    const text = dec.decode(new Uint8Array(ex.memory.buffer, r + 5, len));
    ex.bw_dealloc(r, len + 5);
    return status === 0 ? text : null;
  }

  const [KINDS, UNOPS, BINOPS, CMPOPS] = call(OPS.names)
    .split("\n")
    .map((line) => line.split(" "));
  const code = (names, op, what) => {
    const i = names.indexOf(op);
    if (i < 0) {
      throw new Error(`unknown ${what} ${JSON.stringify(op)}`);
    }
    return i;
  };
  const handle = (e) => BigInt.asUintN(64, BigInt(e));
  const built = (h) => (h === 0n ? null : h);
  const unsigned = (text) => BigInt(`0x${text}`);

  const site = {
    kind: (e) => {
      const k = ex.bw_site_kind(handle(e));
      return k < 0 ? null : KINDS[k];
    },
    op: (e) => take(ex.bw_site_op(handle(e))),
    children: (e) => {
      const t = take(ex.bw_site_children(handle(e)));
      return t ? t.split(" ").map(BigInt) : [];
    },
    width: (e) => ex.bw_site_width(handle(e)) || null,
    lo: (e) => {
      const lo = ex.bw_site_lo(handle(e));
      return lo < 0 ? null : lo;
    },
    value: (e) => {
      const t = take(ex.bw_site_value(handle(e)));
      return t === null ? null : unsigned(t);
    },
    // Known bits, unsigned and signed bounds (BigInts), or null when the budget declined.
    facts: (e) => {
      const t = take(ex.bw_site_facts(handle(e)));
      if (t === null) {
        return null;
      }
      const w = ex.bw_site_width(handle(e));
      const [knownZero, knownOne, umin, umax, ustride, smin, smax] = t.split(" ").map(unsigned);
      const signed = (v) => BigInt.asIntN(w, v);
      return { knownZero, knownOne, umin, umax, ustride, smin: signed(smin), smax: signed(smax) };
    },
    print: (e) => take(ex.bw_site_print(handle(e))),
    constant: (value, width) => {
      const [p, l] = put(`0x${BigInt.asUintN(width, BigInt(value)).toString(16)}:${width}`);
      const r = ex.bw_site_const(p, l);
      ex.bw_dealloc(p, l);
      return built(r);
    },
    un: (op, a) => built(ex.bw_site_un(code(UNOPS, op, "unary operator"), handle(a))),
    bin: (op, a, b) =>
      built(ex.bw_site_bin(code(BINOPS, op, "binary operator"), handle(a), handle(b))),
    cmp: (op, a, b) => built(ex.bw_site_cmp(code(CMPOPS, op, "comparison"), handle(a), handle(b))),
    zext: (a, width) => built(ex.bw_site_cast(0, handle(a), width)),
    sext: (a, width) => built(ex.bw_site_cast(1, handle(a), width)),
    trunc: (a, width) => built(ex.bw_site_cast(2, handle(a), width)),
    extract: (a, lo, length) => built(ex.bw_site_extract(handle(a), lo, length)),
    concat: (hi, lo) => built(ex.bw_site_concat(handle(hi), handle(lo))),
    select: (c, t, e) => built(ex.bw_site_select(handle(c), handle(t), handle(e))),
  };

  // Runs `f` with `rewrites` answering the module's calls; rethrows what one threw.
  function withRewrites(rewrites, f) {
    const outer = active;
    const current = { rewrites, site, errors: [] };
    active = current;
    try {
      return f();
    } finally {
      active = outer;
      if (current.errors.length > 0) {
        throw current.errors[0];
      }
    }
  }

  const rewriteLine = (r, i, trusted) => {
    if (typeof r.rewrite !== "function") {
      throw new Error("a rewrite needs a `rewrite` function");
    }
    return `rewrite ${i} ${trusted ? 1 : 0} ${r.revision ?? 1} ${word(r.name, "the name")} ${word(r.group ?? "host", "the group")}`;
  };

  // Simplifies with the options of `simplify` beyond `deobfuscate`.
  function simplifyWith(text, width, opts) {
    const rewrites = opts.rewrites ?? [];
    const lines = [`engine ${word(opts.engine ?? (opts.deobfuscate === false ? "standard" : "deobfuscate"), "the engine")}`];
    for (const [name, [zero, one]] of Object.entries(opts.known ?? {})) {
      lines.push(`known ${word(name, "the symbol")} ${hex(zero)} ${hex(one)}`);
    }
    rewrites.forEach((r, i) => lines.push(rewriteLine(r, i, r.trusted)));
    if (opts.sharing !== undefined) {
      lines.push(`sharing ${word(opts.sharing, "sharing")}`);
    }
    if (opts.maxRegion !== undefined) {
      lines.push(`max_region ${Number(opts.maxRegion)}`);
    }
    if (opts.maxRounds !== undefined) {
      lines.push(`max_rounds ${Number(opts.maxRounds)}`);
    }
    if (opts.stats) {
      lines.push("stats");
    }
    const out = withRewrites(rewrites, () => call(OPS.simplifyWith, text, lines.join("\n"), width));
    if (!opts.stats) {
      return out;
    }
    const at = out.lastIndexOf("\n");
    return { expr: out.slice(0, at), stats: parseStats(out.slice(at + 1)) };
  }

  return {
    // Simplifies expression text (symbols default to `width` bits), deobfuscating like the
    // command line's `simplify`, or with the standard engine only. Options for a compiler:
    // `engine` ("standard", "deobfuscate" or "compile"), `known` (a symbol's declared known
    // bits: `{ p: [zeroMask, oneMask] }`), `rewrites` (`{ name, rewrite, group, revision,
    // trusted }`: host rewrites), `sharing` ("roots" or "ignored"), `maxRegion`, `maxRounds`,
    // and `stats` (then the result is `{ expr, stats }`).
    simplify: (text, width = 64, opts = {}) => {
      const { deobfuscate = true, ...rest } = opts;
      if (Object.keys(rest).length === 0) {
        return call(deobfuscate ? OPS.simplify : OPS.simplifyStandard, text, "", width);
      }
      return simplifyWith(text, width, opts);
    },
    // Tests a host rewrite offline on expression texts: `{ passed, applications, points,
    // exhaustive, failure }`, `failure` null or `{ kind, message, node, result, second,
    // assignment }` (assignment: symbol name to BigInt). Options: `widths`, `variants`,
    // `maxExhaustiveBits`, `samples`, `seed`.
    checkRewrite: (rewrite, inputs, opts = {}) => {
      const lines = [rewriteLine(rewrite, 0, false)];
      if (opts.widths !== undefined) {
        lines.push(`widths ${opts.widths.map(Number).join(" ")}`);
      }
      for (const [key, name] of [
        ["variants", "variants"],
        ["maxExhaustiveBits", "max_exhaustive_bits"],
        ["samples", "samples"],
        ["seed", "seed"],
      ]) {
        if (opts[key] !== undefined) {
          lines.push(`${name} ${BigInt(opts[key])}`);
        }
      }
      const out = withRewrites([rewrite], () =>
        call(OPS.checkRewrite, inputs.join("\0"), lines.join("\n")),
      );
      if (out.startsWith("passed ")) {
        const [applications, points, exhaustive] = out.split(" ").slice(1).map(Number);
        return { passed: true, applications, points, exhaustive, failure: null };
      }
      const [head, message, node, result, second, ...assigned] = out.split("\0");
      const assignment = {};
      for (const a of assigned) {
        const [name, v] = a.split(" ");
        assignment[name] = unsigned(v);
      }
      const or = (s) => (s === "" ? null : s);
      const failure = {
        kind: head.slice("failed ".length),
        message,
        node: or(node),
        result: or(result),
        second: or(second),
        assignment,
      };
      return { passed: false, applications: 0, points: 0, exhaustive: 0, failure };
    },
    // An instruction's semantics as text over named parameters, instantiated with the
    // argument texts (parsed at `width` bits): the expression.
    template: (text, params, args, width = 64) =>
      call(OPS.template, text, [params.map((p) => word(p, "a parameter")).join(" "), ...args].join("\0"), width),
    // Reads a template with parameters of `widths`: throws its syntax or width error now.
    checkTemplate: (text, params, widths) => {
      call(OPS.checkTemplate, text, `${params.map((p) => word(p, "a parameter")).join(" ")}\0${widths.join(" ")}`);
    },
    // Simplifies, then searches for a smaller equal expression (proved).
    synthesize: (text, width = 64) => call(OPS.synthesize, text, "", width),
    // "equivalent", "different at …" (a counterexample) or "undecided".
    equivalent: (a, b, width = 64) => call(OPS.equivalent, a, b, width),
    // Verifies transformations in the syntax of the Alive paper: the report.
    prove: (text) => call(OPS.prove, text),
    // Translation validation of LLVM IR (`tgt` empty: @tgt against @src of `src`).
    validate: (src, tgt = "") => call(OPS.validate, src, tgt),
    // Each transformation's inferred precondition: `name TAB precondition` lines.
    infer: (text) => call(OPS.infer, text),
    // Lifted code ("pcode", "vex" or "llvm") read and deobfuscated: one line per register,
    // store and exit.
    lift: (from, code, fn = "") => {
      const n = FRONT_ENDS[from];
      if (n === undefined) {
        throw new Error(`unknown front end ${from} (pcode, vex or llvm)`);
      }
      return call(OPS.lift, code, fn, n);
    },
    // An SMT-LIB script defining the expression as `root0`.
    toSmtlib: (text, width = 64) => call(OPS.toSmtlib, text, "", width),
    version: () => call(OPS.version),
  };
}

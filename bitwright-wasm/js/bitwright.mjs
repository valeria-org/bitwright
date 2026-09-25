// bitwright in WebAssembly: `const bw = await instantiate(bytes)`, then `bw.simplify(text)`.
// `bytes` is the module (`bitwright_wasm.wasm`) as an ArrayBuffer, a typed array, or a fetch
// Response. Every function takes and returns strings, and throws an Error with bitwright's
// message on failure.

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
};

const FRONT_ENDS = { pcode: 0, vex: 1, llvm: 2 };

export async function instantiate(bytes) {
  const source = bytes instanceof Response ? await bytes.arrayBuffer() : bytes;
  const { instance } = await WebAssembly.instantiate(source, {});
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

  return {
    // Simplifies expression text (symbols default to `width` bits), deobfuscating like the
    // command line's `simplify`, or with the standard engine only.
    simplify: (text, width = 64, { deobfuscate = true } = {}) =>
      call(deobfuscate ? OPS.simplify : OPS.simplifyStandard, text, "", width),
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

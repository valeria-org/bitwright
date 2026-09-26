// node bitwright-wasm/js/test.mjs path/to/bitwright_wasm.wasm
import { readFile } from "node:fs/promises";
import assert from "node:assert/strict";
import { instantiate } from "./bitwright.mjs";

const bw = await instantiate(await readFile(process.argv[2]));
assert.match(bw.version(), /^\d+\.\d+\.\d+$/);
assert.equal(bw.simplify("(x & y) * (x | y) + (x & ~y) * (~x & y)", 64), "x * y");
assert.equal(bw.simplify("(x ^ y) + 2 * (x & y)", 32, { deobfuscate: false }), "x + y");
assert.equal(bw.synthesize("((x + y) & 1) ^ (x & 1)", 32), "y & 1");
assert.equal(bw.equivalent("x * 2", "x + x", 16), "equivalent");
assert.match(bw.equivalent("x + y", "x | y", 8), /^different at /);
assert.match(bw.prove("%r = select %c, %x, false\n=>\n%r = and %c, %x"), /^INVALID/);
assert.match(
  bw.validate(
    "define i8 @src(i8 %x) {\n  %r = mul i8 %x, 2\n  ret i8 %r\n}\n" +
      "define i8 @tgt(i8 %x) {\n  %r = add i8 %x, %x\n  ret i8 %r\n}\n",
  ),
  /^valid/,
);
assert.equal(bw.infer("%r = mul %x, C\n=>\n%r = shl %x, log2(C)"), "transformation 1\tisPowerOf2(C)\n");
assert.equal(
  bw.lift("vex", "t0 = GET:I64(rdi)\nt1 = GET:I64(rsi)\nt2 = Xor64(t0,t1)\nt3 = And64(t0,t1)\nt4 = Add64(t3,t3)\nt5 = Add64(t2,t4)\nPUT(rax) = t5"),
  "rax = rdi + rsi\n",
);
assert.match(bw.toSmtlib("x + 1", 8), /bvadd/);
assert.throws(() => bw.simplify("x +", 8), /./);
assert.throws(() => bw.lift("arm", "x"), /unknown front end/);

// In a compiler: the compile engine, declared known bits, counters.
assert.equal(bw.simplify("(x ^ y) + 2 * (x & y)", 32, { engine: "compile" }), "x + y");
assert.equal(bw.simplify("p & 15", 64, { engine: "compile", known: { p: [15n, 0n] } }), "0:64");
const counted = bw.simplify("(x ^ y) + 2 * (x & y)", 32, { engine: "compile", stats: true });
assert.equal(counted.expr, "x + y");
assert.equal(counted.stats.rounds, 1);
assert.equal(counted.stats.host.calls, 0);
assert.equal(bw.simplify("x + 0", 8, { engine: "standard", sharing: "ignored", maxRegion: 8, maxRounds: 2 }), "x");
assert.throws(() => bw.simplify("x", 8, { known: { y: [1n, 0n] } }), /no symbol y/);
assert.throws(() => bw.simplify("x", 8, { known: { x: [1n, 1n] } }), /both 0 and 1/);
assert.throws(() => bw.simplify("x", 8, { engine: "fast" }), /unknown option/);

// A host rewrite: `urem(x, c)` as `x` when the facts show `x < c`.
const needlessRem = {
  name: "acme.needless_rem",
  rewrite: (site, e) => {
    if (site.op(e) !== "urem") {
      return null;
    }
    const [x, c] = site.children(e);
    const bound = site.value(c);
    const facts = site.facts(x);
    return bound !== null && facts !== null && facts.umax < bound ? x : null;
  },
};
const rem = "urem(zext<32>(b:8), 1000)";
assert.equal(bw.simplify(rem, 32, { engine: "compile" }), "urem(zext<32>(b), 1000)");
for (const trusted of [false, true]) {
  const out = bw.simplify(rem, 32, { engine: "compile", rewrites: [{ ...needlessRem, trusted }], stats: true });
  assert.equal(out.expr, "zext<32>(b)");
  assert.equal(out.stats.host.changed, 1);
}
// Every site accessor, at `urem(zext<32>(b), 7)`; the result (larger) is not committed.
let seen = 0;
const inspect = {
  name: "t.inspect",
  trusted: true,
  rewrite: (site, e) => {
    if (site.op(e) !== "urem") {
      return null;
    }
    seen += 1;
    const [x, c] = site.children(e);
    assert.equal(site.kind(e), "binary");
    assert.equal(site.kind(x), "zext");
    assert.equal(site.kind(0n), null);
    assert.equal(site.width(e), 32);
    assert.equal(site.width(0n), null);
    assert.equal(site.value(c), 7n);
    assert.equal(site.value(x), null);
    assert.equal(site.print(e), "urem(zext<32>(b), 7)");
    const f = site.facts(x);
    assert.equal(f.umax, 255n);
    assert.equal(f.smin, 0n);
    const one = site.constant(1, 32);
    assert.equal(site.value(site.constant(-1, 32)), 0xffffffffn);
    const ex = site.extract(x, 2, 4);
    assert.equal(site.lo(ex), 2);
    const made = [
      site.un("neg", x),
      site.bin("add", x, one),
      site.cmp("ult", x, one),
      site.zext(x, 64),
      site.sext(x, 64),
      site.trunc(x, 8),
      site.concat(site.trunc(x, 8), site.trunc(x, 8)),
    ];
    for (const h of made) {
      assert.equal(typeof h, "bigint");
    }
    assert.equal(site.width(made[6]), 16);
    assert.equal(site.bin("add", x, site.trunc(x, 8)), null);
    assert.throws(() => site.bin("frob", x, one), /unknown binary operator/);
    return site.select(made[2], x, one);
  },
};
assert.equal(bw.simplify("urem(zext<32>(b:8), 7)", 32, { engine: "compile", rewrites: [inspect] }), "urem(zext<32>(b), 7)");
assert.ok(seen > 0);
// A wrong rewrite, sampled, is quarantined; an exception is rethrown after the call.
const dropAddend = { name: "t.drop", rewrite: (s, e) => (s.op(e) === "add" ? s.children(e)[0] : null) };
const bad = bw.simplify("x * y + z", 16, { engine: "compile", rewrites: [dropAddend], stats: true });
assert.equal(bad.expr, "x * y + z");
assert.ok(bad.stats.quarantined >= 1 && bad.stats.host.rejected >= 1);
assert.throws(
  () => bw.simplify("x + y", 8, { rewrites: [{ name: "t.throw", rewrite: () => { throw new Error("oops"); } }] }),
  /oops/,
);
assert.throws(() => bw.simplify("x", 8, { rewrites: [{ name: "two words", rewrite: () => null }] }), /one word/);

// Checking a rewrite offline.
const passed = bw.checkRewrite(needlessRem, ["urem(zext<32>(b), 1000)", "urem(x, 1000)"]);
assert.ok(passed.passed && passed.applications > 0 && passed.failure === null);
const small = bw.checkRewrite(
  { name: "t.xor", rewrite: (s, e) => {
    if (s.op(e) !== "xor") return null;
    const [a, y] = s.children(e);
    if (s.op(a) !== "xor") return null;
    const [x, z] = s.children(a);
    return z === y ? x : x === y ? z : null;
  } },
  ["(x ^ y) ^ y"],
  { widths: [4], variants: 0 },
);
assert.deepEqual([small.applications, small.points], [1, 256]);
const wrong = bw.checkRewrite({ name: "t.or", rewrite: (s, e) => (s.op(e) === "or" ? s.children(e)[0] : null) }, ["x | y"], { seed: 7 });
assert.equal(wrong.passed, false);
assert.equal(wrong.failure.kind, "differs");
assert.equal(wrong.failure.node, "x | y");
assert.equal(wrong.failure.result, "x");
assert.deepEqual(Object.keys(wrong.failure.assignment).sort(), ["x", "y"]);
assert.match(wrong.failure.message, /differs at/);
assert.equal(bw.checkRewrite(needlessRem, ["x + y"]).failure.kind, "never_applied");
assert.equal(bw.checkRewrite(needlessRem, ["x +"]).failure.kind, "unparsable");

// Templates.
assert.equal(bw.template("select(a <u b, a, b)", ["a", "b"], ["x * 3", "y"], 32), "let %0 = x * 3;\nselect(%0 <u y, %0, y)");
bw.checkTemplate("select(c, a + 1, b)", ["c", "a", "b"], [1, 32, 32]);
assert.throws(() => bw.checkTemplate("select(c, a + 1, b)", ["c", "a", "b"], [8, 8, 8]), /./);
assert.throws(() => bw.template("a + a", ["a", "a"], ["x", "x"], 8), /repeated/);

// Memory growth between calls keeps working.
const big = Array.from({ length: 200 }, (_, i) => `(x${i % 7} ^ ${i})`).join(" + ");
bw.simplify(big, 64);
console.log("ok");

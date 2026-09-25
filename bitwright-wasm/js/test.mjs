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
// Memory growth between calls keeps working.
const big = Array.from({ length: 200 }, (_, i) => `(x${i % 7} ^ ${i})`).join(" + ");
bw.simplify(big, 64);
console.log("ok");

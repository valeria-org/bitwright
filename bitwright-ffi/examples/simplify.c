/* Simplifies an expression, evaluates it, and asks for facts, from C.
 *
 *   cargo build --release -p bitwright-ffi
 *   cc -std=c99 -I bitwright-ffi/include bitwright-ffi/examples/simplify.c \
 *      -L target/release -lbitwright -o simplify
 *   LD_LIBRARY_PATH=target/release ./simplify
 */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

#include "bitwright.h"

#define CHECK(call)                                                                            \
    do {                                                                                       \
        bw_status s_ = (call);                                                                 \
        if (s_ != BW_OK) {                                                                     \
            fprintf(stderr, "%s:%d: error %d: %s\n", __FILE__, __LINE__, s_, bw_last_error()); \
            exit(1);                                                                           \
        }                                                                                      \
    } while (0)

int main(void) {
    if (bw_abi_version() != BW_ABI_VERSION) {
        fprintf(stderr, "header and library differ\n");
        return 1;
    }
    bw_context *cx = bw_context_new();
    bw_engine *engine = bw_engine_new(BW_PRESET_STANDARD);
    if (!cx || !engine) {
        fprintf(stderr, "%s\n", bw_last_error());
        return 1;
    }

    /* Parse, simplify, print. */
    bw_expr e, s;
    char *text;
    CHECK(bw_parse(cx, "(x & y) + (x | y)", 64, &e));
    CHECK(bw_simplify(engine, cx, e, &s));
    CHECK(bw_print(cx, s, 0, &text));
    printf("simplified: %s\n", text);
    bw_string_free(text);

    /* Build with the constructors: a * 3 + 1, at 8 bits. */
    bw_expr a, three, prod, one, f;
    CHECK(bw_symbol(cx, "a", 8, &a));
    CHECK(bw_const_u64(cx, 8, 3, &three));
    CHECK(bw_bin(cx, BW_MUL, a, three, &prod));
    CHECK(bw_const_u64(cx, 8, 1, &one));
    CHECK(bw_bin(cx, BW_ADD, prod, one, &f));

    /* Evaluate at a = 100: 301 mod 256 = 45. */
    bw_value v = bw_value_u64(8, 100), r;
    CHECK(bw_eval(cx, f, &a, &v, 1, &r));
    printf("f(100) = %" PRIu64 "\n", r.limbs[0]);

    /* Facts: (a & 0xf0) | 1 has bits 1..3 known zero and bit 0 known one. */
    bw_expr m, masked, g;
    bw_facts facts;
    CHECK(bw_const_u64(cx, 8, 0xf0, &m));
    CHECK(bw_bin(cx, BW_AND, a, m, &masked));
    CHECK(bw_bin(cx, BW_OR, masked, one, &g));
    CHECK(bw_facts_of(cx, g, NULL, &facts));
    printf("known zero 0x%02" PRIx64 ", known one 0x%02" PRIx64 ", range [%" PRIu64
           ", %" PRIu64 "] by %" PRIu64 "\n",
           facts.known_zero.limbs[0], facts.known_one.limbs[0], facts.umin.limbs[0],
           facts.umax.limbs[0], facts.ustride);

    /* Under the assumption a <u 16, a & 0xf0 is 0. */
    bw_assumptions *assumptions = bw_assumptions_new();
    bw_expr sixteen, lt, zero;
    bw_proof proof;
    CHECK(bw_const_u64(cx, 8, 16, &sixteen));
    CHECK(bw_cmp(cx, BW_ULT, a, sixteen, &lt));
    CHECK(bw_assume(assumptions, cx, lt, true, NULL));
    CHECK(bw_const_u64(cx, 8, 0, &zero));
    CHECK(bw_prove_cmp(cx, BW_EQ, masked, zero, assumptions, &proof));
    printf("a <u 16 proves a & 0xf0 == 0: %s (relies on 0x%" PRIx64 ")\n",
           proof.truth == BW_TRUE ? "yes" : "no", proof.relies_on);

    /* Floating point: 0.1 + 0.2 in binary32 (0x3dcccccd and 0x3e4ccccd), to nearest and toward
     * zero. The last two arguments of bw_fp are for conversions; a sum ignores them. */
    bw_expr pq[2], near, down;
    bw_value tenths[2], sum;
    CHECK(bw_symbol(cx, "p", 32, &pq[0]));
    CHECK(bw_symbol(cx, "q", 32, &pq[1]));
    CHECK(bw_fp(cx, BW_FP_ADD, BW_RNE, BW_F32, pq, 2, BW_F32, 0, &near));
    CHECK(bw_fp(cx, BW_FP_ADD, BW_RTZ, BW_F32, pq, 2, BW_F32, 0, &down));
    tenths[0] = bw_value_u64(32, 0x3dcccccd);
    tenths[1] = bw_value_u64(32, 0x3e4ccccd);
    CHECK(bw_print(cx, near, 0, &text));
    CHECK(bw_eval(cx, near, pq, tenths, 2, &sum));
    printf("%s at 0.1, 0.2: 0x%08" PRIx64, text, sum.limbs[0]);
    bw_string_free(text);
    CHECK(bw_eval(cx, down, pq, tenths, 2, &sum));
    printf(", toward zero 0x%08" PRIx64 "\n", sum.limbs[0]);

    /* Errors are status codes with a message. */
    bw_expr bad;
    bw_status st = bw_parse(cx, "x +", 8, &bad);
    printf("error %d: %s\n", st, bw_last_error());

    bw_assumptions_free(assumptions);
    bw_engine_free(engine);
    bw_context_free(cx);
    return 0;
}

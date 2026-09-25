/*
 * bitwright.h: the C API of bitwright, hash-consed fixed-width bit-vector expressions with
 * exact evaluation, bit-level facts and verified simplification.
 *
 * Built from the `bitwright-ffi` crate (`cargo build --release -p bitwright-ffi`), which gives
 * `libbitwright` as a shared and a static library. `bitwright.hpp` is a C++ wrapper over this
 * header. The book's "C, C++ and Python" chapter is the guide.
 *
 * Conventions
 * - Every fallible function returns a `bw_status`: `BW_OK` (0) or an error code. On an error
 *   `bw_last_error()` describes it, and the output parameters are left unchanged.
 * - Objects (`bw_context`, `bw_engine`, ...) are created by a `*_new` function and released by
 *   the matching `*_free`, which accepts NULL.
 * - Strings passed in are NUL-terminated UTF-8. Strings returned in a `char **` are owned by the
 *   caller and released with `bw_string_free`.
 * - A `bw_expr` is a handle to an expression node, valid in the context that created it until
 *   that context is cleared or freed. 0 (`BW_NULL_EXPR`) is never a valid handle. A handle used
 *   with another context, or after `bw_context_clear`, is rejected (`BW_ERR_FOREIGN_EXPR`,
 *   `BW_ERR_STALE_EXPR`); it never refers to another node.
 * - Threads: a context and an assumption set may be used from one thread at a time. An engine
 *   is immutable once built and may be shared by any number of threads, each with its own
 *   context.
 * - Enumerations are passed as `int`; their values are fixed and never renumbered.
 */
#ifndef BITWRIGHT_H
#define BITWRIGHT_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Version of this header's ABI; `bw_abi_version()` gives the library's. They must be equal. */
#define BW_ABI_VERSION 1

/* ----- status ---------------------------------------------------------------------------- */

typedef int bw_status;

enum {
    BW_OK = 0,
    /* A width rule was violated: operands of different widths, a bad cast or extract, a width
     * outside 1..=512. */
    BW_ERR_WIDTH = 1,
    /* A value does not fit in its width (or has bits set above it). */
    BW_ERR_VALUE = 2,
    /* A handle from before the context was cleared. */
    BW_ERR_STALE_EXPR = 3,
    /* A handle from another context (or not a handle). */
    BW_ERR_FOREIGN_EXPR = 4,
    /* A symbol requested at a width other than the one it has. */
    BW_ERR_SYMBOL_WIDTH = 5,
    /* The context reached its node limit. */
    BW_ERR_ARENA_FULL = 6,
    /* Evaluation reached a symbol without a value. */
    BW_ERR_UNBOUND_SYMBOL = 7,
    /* A symbol's value has the wrong width. */
    BW_ERR_ENV_WIDTH = 8,
    /* A syntax or typing error in expression text or an SMT-LIB script. */
    BW_ERR_SYNTAX = 9,
    /* A substitution that replaces one expression twice. */
    BW_ERR_DUPLICATE_SUBSTITUTION = 10,
    /* The operation does not support this input. */
    BW_ERR_UNSUPPORTED = 11,
    /* An internal contract was violated (a library defect). */
    BW_ERR_CONTRACT = 12,
    /* A NULL pointer, an unknown enumeration value, text that is not UTF-8, or a node of the
     * wrong kind. */
    BW_ERR_INVALID_ARGUMENT = 13,
    /* A rule file that does not compile, a rule the checker cannot prove sound, a ledger that
     * does not parse or vouch for its rules, or an engine that does not link. */
    BW_ERR_RULES = 14,
    /* The assumptions contradict each other. */
    BW_ERR_INFEASIBLE = 15,
    /* The library panicked (a defect); the objects involved should be freed. */
    BW_ERR_PANIC = 16
};

/* A description of the last error on this thread, or "" if there was none. Valid until the
 * next call into the library on this thread. */
const char *bw_last_error(void);

/* The library's ABI version (`BW_ABI_VERSION` of the header it was built with). */
uint32_t bw_abi_version(void);

/* The bitwright version, e.g. "0.10.0". Static storage. */
const char *bw_version(void);

/* Releases a string returned by the library. Accepts NULL. */
void bw_string_free(char *s);

/* ----- values ------------------------------------------------------------------------------ */

#define BW_MAX_WIDTH 512
#define BW_VALUE_LIMBS 8

/* An exact value of 1..=512 bits: `limbs[0]` holds bits 0..63, `limbs[1]` bits 64..127, and so
 * on. Bits at and above `width` must be zero. */
typedef struct bw_value {
    uint16_t width;
    uint64_t limbs[BW_VALUE_LIMBS];
} bw_value;

/* `v` truncated to `width` bits (`width` in 1..=512). */
static inline bw_value bw_value_u64(uint16_t width, uint64_t v) {
    bw_value r;
    int i;
    r.width = width;
    for (i = 0; i < BW_VALUE_LIMBS; i++) {
        r.limbs[i] = 0;
    }
    r.limbs[0] = width < 64 ? v & ((UINT64_C(1) << width) - 1) : v;
    return r;
}

/* `v` in two's complement, truncated to `width` bits (`width` in 1..=512). */
static inline bw_value bw_value_i64(uint16_t width, int64_t v) {
    bw_value r = bw_value_u64(width, (uint64_t)v);
    int i;
    if (v < 0) {
        for (i = 1; i < BW_VALUE_LIMBS && 64 * i < width; i++) {
            r.limbs[i] = width - 64 * i >= 64 ? UINT64_MAX
                                             : (UINT64_C(1) << (width - 64 * i)) - 1;
        }
    }
    return r;
}

/* ----- operators --------------------------------------------------------------------------- */

/* Unary operators: W bits to W bits. */
typedef enum bw_unop {
    BW_NOT = 0,    /* bitwise complement */
    BW_NEG = 1,    /* two's-complement negation */
    BW_POPCNT = 2, /* number of set bits */
    BW_CLZ = 3,    /* leading zeros; clz(0) = W */
    BW_CTZ = 4,    /* trailing zeros; ctz(0) = W */
    BW_BSWAP = 5,  /* byte reversal; W a multiple of 8 */
    BW_BITREV = 6  /* bit reversal */
} bw_unop;

/* Binary operators: two W-bit operands to W bits. Every operator is total (SMT-LIB QF_BV):
 * udiv(x, 0) = ~0, urem(x, 0) = x, and shifts by W or more give 0 (or the sign fill). */
typedef enum bw_binop {
    BW_ADD = 0,
    BW_SUB = 1,
    BW_MUL = 2,
    BW_UMULHI = 3, /* high W bits of the unsigned 2W-bit product */
    BW_SMULHI = 4, /* high W bits of the signed 2W-bit product */
    BW_UDIV = 5,
    BW_UREM = 6,
    BW_SDIV = 7,
    BW_SREM = 8,
    BW_AND = 9,
    BW_OR = 10,
    BW_XOR = 11,
    BW_SHL = 12,
    BW_LSHR = 13,
    BW_ASHR = 14,
    BW_ROTL = 15,
    BW_ROTR = 16,
    BW_PDEP = 17, /* parallel bit deposit under the mask in the second operand */
    BW_PEXT = 18  /* parallel bit extract under the mask in the second operand */
} bw_binop;

/* Comparisons: two W-bit operands to 1 bit. Nodes store only EQ, NE, ULT, ULE, SLT and SLE;
 * the others are built by swapping the operands. */
typedef enum bw_cmpop {
    BW_EQ = 0,
    BW_NE = 1,
    BW_ULT = 2,
    BW_ULE = 3,
    BW_UGT = 4,
    BW_UGE = 5,
    BW_SLT = 6,
    BW_SLE = 7,
    BW_SGT = 8,
    BW_SGE = 9
} bw_cmpop;

/* ----- contexts ---------------------------------------------------------------------------- */

typedef struct bw_context bw_context;

/* A handle to an expression node; see the conventions above. */
typedef uint64_t bw_expr;
#define BW_NULL_EXPR ((bw_expr)0)

/* A new, empty context. NULL only if the library panicked. */
bw_context *bw_context_new(void);

/* A new context with at most `max_nodes` nodes and at most `fact_work` transfer functions per
 * fact query; 0 keeps the default (2^24 nodes, 2^20 transfers). */
bw_context *bw_context_new_with(uint32_t max_nodes, uint32_t fact_work);

void bw_context_free(bw_context *cx);

/* Drops every node and symbol. Every handle of the context becomes stale. */
void bw_context_clear(bw_context *cx);

/* The number of nodes. */
size_t bw_context_len(const bw_context *cx);

/* ----- building ---------------------------------------------------------------------------- */

/* Every constructor canonicalizes: structurally equal expressions are one node (the same
 * handle), constants are folded and commutative operands ordered. */

/* The symbol named `name` of `width` bits (the same handle on every call). */
bw_status bw_symbol(bw_context *cx, const char *name, uint16_t width, bw_expr *out);

/* The symbol with integer key `key` (printed `#key`). */
bw_status bw_symbol_u64(bw_context *cx, uint64_t key, uint16_t width, bw_expr *out);

/* A symbol distinct from every other (printed `$k`). */
bw_status bw_fresh_symbol(bw_context *cx, uint16_t width, bw_expr *out);

bw_status bw_const(bw_context *cx, const bw_value *v, bw_expr *out);

/* `v`, which must fit in `width` bits unsigned. */
bw_status bw_const_u64(bw_context *cx, uint16_t width, uint64_t v, bw_expr *out);

/* `v`, which must fit in `width` bits signed (two's complement). */
bw_status bw_const_i64(bw_context *cx, uint16_t width, int64_t v, bw_expr *out);

bw_status bw_un(bw_context *cx, int op /* bw_unop */, bw_expr a, bw_expr *out);
bw_status bw_bin(bw_context *cx, int op /* bw_binop */, bw_expr a, bw_expr b, bw_expr *out);
bw_status bw_cmp(bw_context *cx, int op /* bw_cmpop */, bw_expr a, bw_expr b, bw_expr *out);

/* Zero and sign extension to a wider `width`, truncation to a narrower one. */
bw_status bw_zext(bw_context *cx, bw_expr a, uint16_t width, bw_expr *out);
bw_status bw_sext(bw_context *cx, bw_expr a, uint16_t width, bw_expr *out);
bw_status bw_trunc(bw_context *cx, bw_expr a, uint16_t width, bw_expr *out);

/* Bits [lo, lo + len) of `a`. */
bw_status bw_extract(bw_context *cx, bw_expr a, uint16_t lo, uint16_t len, bw_expr *out);

/* `hi` in the high bits, `lo` in the low bits. */
bw_status bw_concat(bw_context *cx, bw_expr hi, bw_expr lo, bw_expr *out);

/* `cond ? then : els`, with a 1-bit condition. */
bw_status bw_select(bw_context *cx, bw_expr cond, bw_expr then, bw_expr els, bw_expr *out);

/* ----- text -------------------------------------------------------------------------------- */

/* Parses expression text, e.g. "(x & y) + (x | y)" or "let m = x * 3; m ^ (m >>u 7)".
 * `default_width` is the width of symbols and literals it cannot infer (0: none, an error). */
bw_status bw_parse(bw_context *cx, const char *text, uint16_t default_width, bw_expr *out);

/* Print flags. */
#define BW_PRINT_NO_LETS 1u       /* repeat shared subterms instead of binding them with `let` */
#define BW_PRINT_SYMBOL_WIDTHS 2u /* annotate symbols with their widths (`x:64`) */

/* The expression in the text syntax, which parses back to the same expression. */
bw_status bw_print(const bw_context *cx, bw_expr e, unsigned flags, char **out);

/* ----- inspecting -------------------------------------------------------------------------- */

typedef enum bw_kind {
    BW_KIND_CONST = 0,
    BW_KIND_SYMBOL = 1,
    BW_KIND_UNARY = 2,   /* op is a bw_unop; children[0] */
    BW_KIND_BINARY = 3,  /* op is a bw_binop; children[0], children[1] */
    BW_KIND_COMPARE = 4, /* op is a bw_cmpop; children[0], children[1] */
    BW_KIND_ZEXT = 5,    /* children[0] extended to `width` */
    BW_KIND_SEXT = 6,
    BW_KIND_EXTRACT = 7, /* bits [lo, lo + width) of children[0] */
    BW_KIND_CONCAT = 8,  /* children[0] high, children[1] low */
    BW_KIND_SELECT = 9,  /* children[0] ? children[1] : children[2] */
    BW_KIND_EXT = 10,    /* output `lo` of a host extension operation */
    BW_KIND_FP = 11      /* op is a bw_fpop, the children its operands; see bw_fp_node_of */
} bw_kind;

/* One node. Unused children are BW_NULL_EXPR; `op` is -1 when the kind has none. */
typedef struct bw_node {
    int kind; /* bw_kind */
    int op;
    uint16_t width;
    uint16_t lo;
    uint32_t n_children;
    bw_expr children[3];
} bw_node;

bw_status bw_node_of(const bw_context *cx, bw_expr e, bw_node *out);

bw_status bw_width(const bw_context *cx, bw_expr e, uint16_t *out);

/* The value of a constant node (BW_ERR_INVALID_ARGUMENT for any other node). */
bw_status bw_const_value(const bw_context *cx, bw_expr e, bw_value *out);

/* The name of a symbol node: the name it was created with, `#k` for an integer key, `$k` for a
 * fresh symbol (BW_ERR_INVALID_ARGUMENT for any other node). */
bw_status bw_symbol_name(const bw_context *cx, bw_expr e, char **out);

/* The number of distinct nodes under `e`, `e` included. */
bw_status bw_dag_size(bw_context *cx, bw_expr e, uint32_t *out);

/* ----- floating point ---------------------------------------------------------------------- */

/* IEEE 754 binary arithmetic on bit-vectors that hold interchange encodings, in any format and
 * under every rounding mode, exactly (the book's chapter on floating point specifies it): results
 * are correctly rounded; a NaN result is the format's canonical quiet NaN; min and max are IEEE
 * 754-2019 minimumNumber and maximumNumber; conversions to integers saturate, a NaN giving 0.
 * Operations on constants fold, and bw_eval evaluates them, the same on every host. */

/* A format: `eb` exponent bits and `sb` significand bits, the hidden bit included (SMT-LIB's
 * convention), so an encoding is `eb + sb` bits wide. Valid when 2 <= eb <= 31, sb >= 2 and
 * eb + sb <= 512; a function given another fails with BW_ERR_WIDTH. */
typedef struct bw_fp_format {
    uint32_t eb;
    uint32_t sb;
} bw_fp_format;

/* The format (eb, sb), as it is: the functions that take a format check it. */
static inline bw_fp_format bw_fp_format_of(uint32_t eb, uint32_t sb) {
    bw_fp_format f;
    f.eb = eb;
    f.sb = sb;
    return f;
}

/* The named formats. BW_X87 holds the values of x87 extended precision (79 bits); bw_x87_load and
 * bw_x87_store convert from and to x87's 80-bit memory encoding. */
#define BW_F16 bw_fp_format_of(5, 11)    /* binary16 */
#define BW_BF16 bw_fp_format_of(8, 8)    /* bfloat16 */
#define BW_F32 bw_fp_format_of(8, 24)    /* binary32 */
#define BW_F64 bw_fp_format_of(11, 53)   /* binary64 */
#define BW_F128 bw_fp_format_of(15, 113) /* binary128 */
#define BW_F256 bw_fp_format_of(19, 237) /* binary256 */
#define BW_X87 bw_fp_format_of(15, 64)   /* x87 extended precision, as values */

/* Rounding modes (IEEE 754 section 4.3), named as in SMT-LIB and the text syntax. */
typedef enum bw_rounding {
    BW_RNE = 0, /* to nearest, ties to even */
    BW_RNA = 1, /* to nearest, ties away from zero */
    BW_RTP = 2, /* toward +infinity */
    BW_RTN = 3, /* toward -infinity */
    BW_RTZ = 4  /* toward zero */
} bw_rounding;

/* The operations of floating-point nodes, named as in the text syntax (`fp.add.rne.f32(a, b)`).
 * Operands and results are encodings of the node's format unless noted. */
typedef enum bw_fpop {
    BW_FP_ADD = 0,       /* a + b */
    BW_FP_MUL = 1,       /* a * b */
    BW_FP_DIV = 2,       /* a / b */
    BW_FP_FMA = 3,       /* a * b + c, rounded once */
    BW_FP_SQRT = 4,      /* square root */
    BW_FP_REM = 5,       /* IEEE remainder a - n * b, n the integer nearest a / b (exact) */
    BW_FP_ROUND = 6,     /* rounding to an integral value */
    BW_FP_MIN = 7,       /* minimumNumber: a NaN operand ignored, -0 < +0 */
    BW_FP_MAX = 8,       /* maximumNumber */
    BW_FP_EQ = 9,        /* a == b, 1 bit: false with a NaN, true for +0 and -0 */
    BW_FP_LT = 10,       /* a < b, 1 bit */
    BW_FP_LE = 11,       /* a <= b, 1 bit */
    BW_FP_CONVERT = 12,  /* to another format */
    BW_FP_FROM_SBV = 13, /* from a signed integer of any width */
    BW_FP_FROM_UBV = 14, /* from an unsigned integer of any width */
    BW_FP_TO_SBV = 15,   /* to a signed integer, saturating (a NaN gives 0) */
    BW_FP_TO_UBV = 16    /* to an unsigned integer, saturating (a NaN gives 0) */
} bw_fpop;

/* Comparisons for bw_fp_cmp, 1 bit, false when an operand is a NaN. GT and GE are built as LT and
 * LE with the operands swapped. */
typedef enum bw_fpcmp {
    BW_FPCMP_EQ = 0,
    BW_FPCMP_LT = 1,
    BW_FPCMP_LE = 2,
    BW_FPCMP_GT = 3,
    BW_FPCMP_GE = 4
} bw_fpcmp;

/* Classification tests for bw_fp_test, 1 bit. */
typedef enum bw_fptest {
    BW_FP_ISNAN = 0,       /* any NaN */
    BW_FP_ISINF = 1,       /* an infinity */
    BW_FP_ISZERO = 2,      /* a zero */
    BW_FP_ISSUBNORMAL = 3, /* nonzero, with the minimum exponent field */
    BW_FP_ISNORMAL = 4,    /* finite, nonzero and not subnormal */
    BW_FP_ISNEG = 5,       /* the sign bit set, and not a NaN */
    BW_FP_ISPOS = 6        /* the sign bit clear, and not a NaN */
} bw_fptest;

/* The operation `op` of `format` on the `n` operands `args`: 3 for BW_FP_FMA, 2 for the binary
 * operations and the comparisons, 1 for the others (BW_ERR_INVALID_ARGUMENT otherwise). The
 * operands are `format`'s width (BW_ERR_WIDTH otherwise), except the integer of BW_FP_FROM_SBV and
 * BW_FP_FROM_UBV: any width, `format` being the result's. `rm` is the rounding mode, ignored by
 * the operations without one (REM, MIN, MAX, EQ, LT, LE); `to` is the result's format for
 * BW_FP_CONVERT and `width` the result's width for BW_FP_TO_SBV and BW_FP_TO_UBV, each ignored
 * by the other operations. */
bw_status bw_fp(bw_context *cx, int op /* bw_fpop */, int rm /* bw_rounding */,
                bw_fp_format format, const bw_expr *args, size_t n, bw_fp_format to,
                uint16_t width, bw_expr *out);

/* The other operations are built as the text syntax builds them, from those nodes and from
 * bit-vector operators (and print as such), so every pass sees through them. */

/* `a - b`, built as `a + neg(b)` (the same function, bit for bit). */
bw_status bw_fp_sub(bw_context *cx, int rm /* bw_rounding */, bw_fp_format format, bw_expr a,
                    bw_expr b, bw_expr *out);

/* `a` with its sign bit flipped (a NaN too): `a ^ sign`. */
bw_status bw_fp_neg(bw_context *cx, bw_fp_format format, bw_expr a, bw_expr *out);

/* `a` with its sign bit cleared (a NaN too): `a & ~sign`. */
bw_status bw_fp_abs(bw_context *cx, bw_fp_format format, bw_expr a, bw_expr *out);

/* `a` with the sign bit of `b`: `(a & ~sign) | (b & sign)`. */
bw_status bw_fp_copysign(bw_context *cx, bw_fp_format format, bw_expr a, bw_expr b,
                         bw_expr *out);

/* The comparison `a op b`, 1 bit: a BW_FP_EQ, BW_FP_LT or BW_FP_LE node. */
bw_status bw_fp_cmp(bw_context *cx, int op /* bw_fpcmp */, bw_fp_format format, bw_expr a,
                    bw_expr b, bw_expr *out);

/* A classification test, 1 bit: one unsigned comparison of the encoding. */
bw_status bw_fp_test(bw_context *cx, int test /* bw_fptest */, bw_fp_format format, bw_expr a,
                     bw_expr *out);

/* An 80-bit x87 extended-precision encoding as a value of BW_X87 (79 bits), read as x87 reads it:
 * a pseudo-denormal is the normal value it stands for; an unnormal, a pseudo-infinity or a
 * pseudo-NaN is invalid and loads as the NaN. Built from extracts, concatenations and selects. */
bw_status bw_x87_load(bw_context *cx, bw_expr a, bw_expr *out);

/* A value of BW_X87 (79 bits) as its 80-bit x87 encoding, the explicit integer bit set exactly
 * when the exponent field is not zero. */
bw_status bw_x87_store(bw_context *cx, bw_expr a, bw_expr *out);

/* The operation of a floating-point node (BW_KIND_FP). */
typedef struct bw_fp_node {
    int op;              /* bw_fpop */
    int rm;              /* bw_rounding; -1 for the operations without one */
    bw_fp_format format; /* of the floating-point operands (the result's, from an integer) */
    bw_fp_format to;     /* BW_FP_CONVERT: the result's format; otherwise {0, 0} */
    uint16_t int_width;  /* BW_FP_TO_SBV, BW_FP_TO_UBV: the integer's width; otherwise 0 */
} bw_fp_node;

/* The operation of a floating-point node (BW_ERR_INVALID_ARGUMENT for any other node). */
bw_status bw_fp_node_of(const bw_context *cx, bw_expr e, bw_fp_node *out);

/* ----- evaluating and substituting --------------------------------------------------------- */

/* The value of `e` with `symbols[i]` (symbol nodes) bound to `values[i]`. */
bw_status bw_eval(bw_context *cx, bw_expr e, const bw_expr *symbols, const bw_value *values,
                  size_t n, bw_value *out);

/* `e` with every `from[i]` replaced by `to[i]` at once, rebuilt canonically. */
bw_status bw_substitute(bw_context *cx, bw_expr e, const bw_expr *from, const bw_expr *to,
                        size_t n, bw_expr *out);

/* ----- assumptions ------------------------------------------------------------------------- */

/* Constraints the caller knows to hold (a path condition, an invariant), numbered from 0 in
 * the order they are added. Results that use them report which in a `relies_on` mask: bit i for
 * constraint i < 63, and bit 63 for any constraint from 63 on. */
typedef struct bw_assumptions bw_assumptions;

bw_assumptions *bw_assumptions_new(void);
void bw_assumptions_free(bw_assumptions *a);

/* Assumes that the 1-bit predicate `p` of context `cx` holds (`holds`) or does not. `id` (may
 * be NULL) receives the constraint's number. A contradiction is not an error here: it makes the
 * set infeasible. */
bw_status bw_assume(bw_assumptions *a, bw_context *cx, bw_expr p, bool holds, uint32_t *id);

bool bw_assumptions_infeasible(const bw_assumptions *a);

/* ----- facts and proofs -------------------------------------------------------------------- */

/* What is known about every value of an expression. Signed bounds are two's-complement bit
 * patterns. */
typedef struct bw_facts {
    bw_value known_zero; /* bits known to be 0 */
    bw_value known_one;  /* bits known to be 1 */
    bw_value umin, umax; /* unsigned bounds */
    uint64_t ustride;    /* the unsigned values are among umin, umin + ustride, ..., umax
                            (0 when umin == umax, 1 for every value between) */
    bw_value smin, smax; /* signed bounds */
    uint64_t relies_on;  /* the assumptions used */
} bw_facts;

/* Facts about `e`, under `a` if it is not NULL (BW_ERR_INFEASIBLE if `a` is infeasible). */
bw_status bw_facts_of(bw_context *cx, bw_expr e, const bw_assumptions *a, bw_facts *out);

typedef enum bw_truth { BW_FALSE = 0, BW_TRUE = 1, BW_UNKNOWN = 2 } bw_truth;

/* A tri-state answer; BW_UNKNOWN is always a correct one. */
typedef struct bw_proof {
    int truth; /* bw_truth */
    uint64_t relies_on;
} bw_proof;

/* Whether `e` is nonzero (for a 1-bit predicate: whether it holds). `a` may be NULL. */
bw_status bw_prove(bw_context *cx, bw_expr e, const bw_assumptions *a, bw_proof *out);

/* Whether `a op b` holds. */
bw_status bw_prove_cmp(bw_context *cx, int op /* bw_cmpop */, bw_expr a, bw_expr b,
                       const bw_assumptions *as, bw_proof *out);

/* Whether `e` is an injective function of its subexpression `of` (with `bijective`: also of
 * the same width), with every value that does not depend on `of` held fixed. */
bw_status bw_prove_injective(bw_context *cx, bw_expr e, bw_expr of, bool bijective,
                             const bw_assumptions *as, bw_proof *out);

/* ----- simplifying ------------------------------------------------------------------------- */

typedef struct bw_engine bw_engine;
typedef struct bw_engine_builder bw_engine_builder;

typedef enum bw_preset {
    /* Fact folding, the built-in rules and the normal-form passes. */
    BW_PRESET_STANDARD = 0,
    /* The standard strategy, the linear MBA and bit-shuffle passes, and the MBA service with the
     * native solver, accepting only answers bitwright proves itself (the command line's
     * `simplify`). */
    BW_PRESET_DEOBFUSCATE = 1
} bw_preset;

/* An engine with a preset strategy. NULL on failure (see bw_last_error). */
bw_engine *bw_engine_new(int preset /* bw_preset */);
void bw_engine_free(bw_engine *e);

/* A builder, for engines with rules of your own. */
bw_engine_builder *bw_engine_builder_new(int preset /* bw_preset */);
void bw_engine_builder_free(bw_engine_builder *b);

/* Adds the rules of a `.bwr` source; their groups run in every rule phase after the built-in
 * ones. `ledger` is a proof ledger for them (from `bw_check_rules` or `bitwright check
 * --ledger`); with NULL, the rules are checked now, which can take a while. */
bw_status bw_engine_builder_add_rules(bw_engine_builder *b, const char *source,
                                      const char *ledger);

/* At most `rounds` rounds of the strategy (default 4; 0 reads as 1). */
void bw_engine_builder_set_max_rounds(bw_engine_builder *b, uint8_t rounds);

/* Also applies the rules that hold for floats as values, every NaN one value (`x * 1` is `x`):
 * a result may then differ from the input in a NaN's payload or sign. */
void bw_engine_builder_set_float_values(bw_engine_builder *b, bool yes);

/* Refuses every rewrite of the rule (`group::rule`) or pass (`linear`, `xor`, …) named. */
bw_status bw_engine_builder_refuse(bw_engine_builder *b, const char *name);

/* The engine. The builder stays valid and may build again. */
bw_status bw_engine_builder_build(const bw_engine_builder *b, bw_engine **out);

/* Checks every rule of a `.bwr` source and gives the proof ledger vouching for them;
 * BW_ERR_RULES (with a counterexample, when there is one) if a rule is not proven sound. */
bw_status bw_check_rules(const char *source, char **ledger);

/* Caps on the work of one call, in the units of the engine's charging schedule. `UINT64_MAX`
 * is unlimited. */
typedef struct bw_budget {
    uint64_t node_visits;
    uint64_t candidates;
    uint64_t match_steps;
    uint64_t rewrites;
    uint64_t new_nodes;
    uint64_t fact_work;
    uint64_t pass_work;
    uint64_t mba_calls;
    uint64_t eqsat_nodes;
    uint64_t eqsat_work;
} bw_budget;

/* The default budget: generous caps for one call. */
bw_budget bw_budget_default(void);

typedef enum bw_end {
    BW_END_COMPLETED = 0, /* the strategy ran to its end */
    BW_END_BUDGET = 1,    /* a budget stopped it; the result is valid but not final */
    BW_END_DECLINED = 2   /* not processed */
} bw_end;

/* Which limit stopped a run (BW_END_BUDGET). */
typedef enum bw_limit {
    BW_LIMIT_NODE_VISITS = 0,
    BW_LIMIT_CANDIDATES = 1,
    BW_LIMIT_MATCH_STEPS = 2,
    BW_LIMIT_REWRITES = 3,
    BW_LIMIT_NEW_NODES = 4,
    BW_LIMIT_FACT_WORK = 5,
    BW_LIMIT_PASS_WORK = 6,
    BW_LIMIT_MBA_CALLS = 7,
    BW_LIMIT_EQSAT_NODES = 8,
    BW_LIMIT_EQSAT_WORK = 9,
    BW_LIMIT_DEADLINE = 10,
    BW_LIMIT_ARENA_CAPACITY = 11
} bw_limit;

/* The result for one root: equal to the input wherever the assumptions in `relies_on` hold
 * (everywhere when it is 0). */
typedef struct bw_outcome {
    bw_expr expr;
    bool changed;
    int end;   /* bw_end */
    int limit; /* bw_limit for BW_END_BUDGET, else -1 */
    uint64_t relies_on;
} bw_outcome;

/* `e` simplified with the default budget and no assumptions. */
bw_status bw_simplify(const bw_engine *engine, bw_context *cx, bw_expr e, bw_expr *out);

/* Simplifies `n` roots in one call (they share work), writing `outcomes[0..n)`. `budget` and
 * `a` may be NULL (the default budget; no assumptions). */
bw_status bw_engine_run(const bw_engine *engine, bw_context *cx, const bw_expr *roots, size_t n,
                        const bw_budget *budget, const bw_assumptions *a,
                        bw_outcome *outcomes);

/* ----- SMT-LIB ----------------------------------------------------------------------------- */

/* A QF_BV script (QF_BVFP with floating-point operations) declaring the roots' symbols and
 * defining the K-th root as `rootK`. */
bw_status bw_smtlib_export(bw_context *cx, const bw_expr *roots, size_t n, char **out);

typedef struct bw_smt_import bw_smt_import;

typedef enum bw_smt_part {
    BW_SMT_SYMBOLS = 0,     /* declared constants */
    BW_SMT_DEFINITIONS = 1, /* definitions without parameters */
    BW_SMT_ASSERTIONS = 2   /* asserted formulas, as 1-bit expressions (no names) */
} bw_smt_part;

/* Reads a QF_BV script, floating-point (QF_BVFP) terms included, into `cx`. */
bw_status bw_smtlib_import(bw_context *cx, const char *script, bw_smt_import **out);
void bw_smt_import_free(bw_smt_import *imp);

/* The number of entries of a part (0 for an unknown part). */
size_t bw_smt_import_count(const bw_smt_import *imp, int part /* bw_smt_part */);

/* Entry `i` of a part: its expression and, for symbols and definitions, its name (owned by the
 * import; NULL for assertions). `name` may be NULL. */
bw_status bw_smt_import_get(const bw_smt_import *imp, int part, size_t i, bw_expr *e,
                            const char **name);

/* ----- proofs and synthesis ----------------------------------------------------------------- */

typedef enum bw_equivalence {
    BW_DIFFERENT = 0,  /* refuted: they differ at some values of the symbols */
    BW_EQUIVALENT = 1, /* proved equal for every value */
    BW_UNDECIDED = -1  /* not decided within the conflict budget */
} bw_equivalence;

/* Whether `a` and `b` are equal for every value of their symbols, by bitwright's own
 * bit-blaster and SAT solver, within `conflicts` conflicts. */
bw_status bw_equivalent(bw_context *cx, bw_expr a, bw_expr b, uint64_t conflicts,
                        int *verdict /* bw_equivalence */);

/* The smallest expression equal to `e` that synthesis finds (proved equal), of at most
 * `max_size` nodes: `*found` is false (and `*out` is `e`) when there is none. */
bw_status bw_synthesize(bw_context *cx, bw_expr e, uint8_t max_size, bw_expr *out, bool *found);

/* ----- memory ------------------------------------------------------------------------------ */

typedef struct bw_memory bw_memory;

/* A memory from `addr_width`-bit addresses to `cell_width`-bit cells, all unknown (the symbols
 * `name.0`, `name.1`, …). Its loads and stores are expressions of the context they are made
 * in (use one context per memory). NULL on failure. */
bw_memory *bw_memory_new(const char *name, uint16_t addr_width, uint16_t cell_width,
                         bool big_endian);
void bw_memory_free(bw_memory *m);

/* Known contents of 8-bit cells from `start` on, before any load or store. */
bw_status bw_memory_set_bytes(bw_memory *m, uint64_t start, const uint8_t *data, size_t n);

/* Stores `value` (a whole number of cells) at `addr`: the memory moves to the new version. */
bw_status bw_memory_store(bw_memory *m, bw_context *cx, bw_expr addr, bw_expr value);

/* Loads `cells` cells at `addr` from the current version, as one value. */
bw_status bw_memory_load(bw_memory *m, bw_context *cx, bw_expr addr, uint16_t cells,
                         bw_expr *out);

/* ----- lifted code ------------------------------------------------------------------------- */

typedef struct bw_lifted bw_lifted;

typedef enum bw_front_end {
    BW_LIFT_PCODE = 0, /* Ghidra p-code, one operation per line */
    BW_LIFT_VEX = 1,   /* VEX IR as pyvex prints an IRSB */
    BW_LIFT_LLVM = 2   /* an LLVM IR function (its return value is the output `ret`) */
} bw_front_end;

typedef enum bw_lifted_part {
    BW_LIFTED_INPUTS = 0,  /* registers read before written: a name and a symbol */
    BW_LIFTED_OUTPUTS = 1, /* registers written: a name and the final value */
    BW_LIFTED_STORES = 2,  /* stores: an address and a value */
    BW_LIFTED_EXITS = 3    /* conditional exits: a condition and a target */
} bw_lifted_part;

/* Reads lifted code into `cx`. `function` names the LLVM IR function (NULL: the first). */
bw_status bw_lift(bw_context *cx, int from /* bw_front_end */, const char *code,
                  const char *function, bw_lifted **out);
void bw_lifted_free(bw_lifted *l);

/* The number of entries of a part (0 for an unknown part). */
size_t bw_lifted_count(const bw_lifted *l, int part /* bw_lifted_part */);

/* Entry `i` of a part: a name (owned by `l`; NULL for stores and exits) and one or two
 * expressions. Any output pointer may be NULL. */
bw_status bw_lifted_get(const bw_lifted *l, int part, size_t i, const char **name, bw_expr *a,
                        bw_expr *b);

/* Where the block continues: `*has` is false when it does not say. */
bw_status bw_lifted_next(const bw_lifted *l, bw_expr *out, bool *has);

/* ----- compiler transformations ------------------------------------------------------------ */

typedef struct bw_transform_counts {
    uint32_t valid;
    uint32_t invalid;
    uint32_t undecided; /* unknown within the budget, or outside what bitwright models */
} bw_transform_counts;

/* Verifies transformations in the syntax of the Alive paper (`Pre:`, source, `=>`, target):
 * the report (as `bitwright prove` prints it, counterexamples included) and the counts.
 * `conflicts` is the SAT budget per question (0: the default). */
bw_status bw_transform_verify(const char *text, uint64_t conflicts, char **report,
                              bw_transform_counts *counts);

/* Translation validation: each function of `tgt` against the function of the same name in
 * `src`, or, with `tgt` NULL, `@tgt` against `@src` of one module. */
bw_status bw_transform_validate(const char *src, const char *tgt, uint64_t conflicts,
                                char **report, bw_transform_counts *counts);

/* Infers each transformation's precondition over its symbolic constants: one line each, `name
 * TAB precondition-or-(none) TAB valid|invalid|undecided|-`. */
bw_status bw_transform_infer(const char *text, char **report);

#ifdef __cplusplus
}
#endif

#endif /* BITWRIGHT_H */

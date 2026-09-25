// bitwright.hpp: a header-only C++17 wrapper over the C API (bitwright.h).
//
// Objects own their C counterparts (RAII), errors are thrown as `bitwright::Error`, and
// expressions are small values (a context pointer and a handle) with operators:
//
//     bitwright::Context cx;
//     auto x = cx.symbol("x", 64), y = cx.symbol("y", 64);
//     auto e = (x & y) + (x | y);
//     std::cout << bitwright::Engine::standard().simplify(e) << "\n"; // x + y
//
// An `Expr` refers to its context without owning it: the context must outlive it. `==` on
// expressions compares handles (equal handles, equal expressions); comparisons that build a
// 1-bit expression are the methods `eq`, `ne`, `ult`, `ule`, `ugt`, `uge`, `slt`, `sle`, `sgt`
// and `sge`. `>>` is the logical shift (`ashr` is the arithmetic one). An integer operand is a
// constant of the other operand's width.
//
// Floating-point operations are methods named after the text syntax's (`fadd`, `fsqrt`, `feq`,
// `fisnan`, `to_float`, ...) that take the operands' format (`bitwright::F32`, any `FpFormat`) and
// a rounding mode (default `Rounding::Rne`):
//
//     auto a = cx.symbol("a", 32), b = cx.symbol("b", 32);
//     auto sum = a.fadd(b, bitwright::F32, bitwright::Rounding::Rtz);
//     std::cout << sum << "\n"; // fp.add.rtz.f32(a, b)
#ifndef BITWRIGHT_HPP
#define BITWRIGHT_HPP

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <memory>
#include <optional>
#include <ostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "bitwright.h"

namespace bitwright {

// ----- errors --------------------------------------------------------------------------------

// A failed call: the status code (`BW_ERR_*`) and the library's message.
class Error : public std::runtime_error {
  public:
    Error(bw_status status, const std::string &what) : std::runtime_error(what), status_(status) {}
    bw_status status() const noexcept { return status_; }

  private:
    bw_status status_;
};

namespace detail {

inline void check(bw_status s) {
    if (s != BW_OK) {
        throw Error(s, bw_last_error());
    }
}

template <class T> T *check_new(T *p) {
    if (p == nullptr) {
        throw Error(BW_ERR_PANIC, bw_last_error());
    }
    return p;
}

inline std::string take(char *s) {
    std::string r(s != nullptr ? s : "");
    bw_string_free(s);
    return r;
}

} // namespace detail

inline std::string version() { return bw_version(); }

// ----- enumerations --------------------------------------------------------------------------

enum class UnOp : int {
    Not = BW_NOT,
    Neg = BW_NEG,
    Popcnt = BW_POPCNT,
    Clz = BW_CLZ,
    Ctz = BW_CTZ,
    Bswap = BW_BSWAP,
    BitRev = BW_BITREV,
};

enum class BinOp : int {
    Add = BW_ADD,
    Sub = BW_SUB,
    Mul = BW_MUL,
    UMulHi = BW_UMULHI,
    SMulHi = BW_SMULHI,
    UDiv = BW_UDIV,
    URem = BW_UREM,
    SDiv = BW_SDIV,
    SRem = BW_SREM,
    And = BW_AND,
    Or = BW_OR,
    Xor = BW_XOR,
    Shl = BW_SHL,
    LShr = BW_LSHR,
    AShr = BW_ASHR,
    RotL = BW_ROTL,
    RotR = BW_ROTR,
    Pdep = BW_PDEP,
    Pext = BW_PEXT,
};

enum class CmpOp : int {
    Eq = BW_EQ,
    Ne = BW_NE,
    Ult = BW_ULT,
    Ule = BW_ULE,
    Ugt = BW_UGT,
    Uge = BW_UGE,
    Slt = BW_SLT,
    Sle = BW_SLE,
    Sgt = BW_SGT,
    Sge = BW_SGE,
};

enum class Kind : int {
    Const = BW_KIND_CONST,
    Symbol = BW_KIND_SYMBOL,
    Unary = BW_KIND_UNARY,
    Binary = BW_KIND_BINARY,
    Compare = BW_KIND_COMPARE,
    Zext = BW_KIND_ZEXT,
    Sext = BW_KIND_SEXT,
    Extract = BW_KIND_EXTRACT,
    Concat = BW_KIND_CONCAT,
    Select = BW_KIND_SELECT,
    Ext = BW_KIND_EXT,
    Fp = BW_KIND_FP,
};

enum class Truth : int { False = BW_FALSE, True = BW_TRUE, Unknown = BW_UNKNOWN };

enum class Preset : int { Standard = BW_PRESET_STANDARD, Deobfuscate = BW_PRESET_DEOBFUSCATE };

enum class End : int {
    Completed = BW_END_COMPLETED,
    Budget = BW_END_BUDGET,
    Declined = BW_END_DECLINED,
};

// ----- values --------------------------------------------------------------------------------

// An exact value of 1..=512 bits.
class Value {
  public:
    Value() : v_(bw_value_u64(1, 0)) {}
    // `v` truncated to `width` bits.
    Value(uint16_t width, uint64_t v) : v_(bw_value_u64(width, v)) {}
    explicit Value(const bw_value &v) : v_(v) {}

    // `v` in two's complement, truncated to `width` bits.
    static Value from_signed(uint16_t width, int64_t v) { return Value(bw_value_i64(width, v)); }

    // Little-endian 64-bit limbs; bits at and above `width` must be zero (checked when the value
    // is used).
    static Value from_limbs(uint16_t width, const std::vector<uint64_t> &limbs) {
        bw_value v = bw_value_u64(width, 0);
        for (std::size_t i = 0; i < limbs.size() && i < BW_VALUE_LIMBS; i++) {
            v.limbs[i] = limbs[i];
        }
        return Value(v);
    }

    uint16_t width() const { return v_.width; }
    uint64_t limb(std::size_t i) const { return i < BW_VALUE_LIMBS ? v_.limbs[i] : 0; }
    bool bit(uint16_t i) const { return i < v_.width && ((v_.limbs[i / 64] >> (i % 64)) & 1); }

    // The value, if it fits in 64 bits.
    std::optional<uint64_t> to_u64() const {
        for (int i = 1; i < BW_VALUE_LIMBS; i++) {
            if (v_.limbs[i] != 0) {
                return std::nullopt;
            }
        }
        return v_.limbs[0];
    }

    // Hexadecimal, e.g. `0x2c`.
    std::string hex() const {
        static const char digits[] = "0123456789abcdef";
        std::string s;
        for (int i = (v_.width + 3) / 4 - 1; i >= 0; i--) {
            int d = static_cast<int>((v_.limbs[i / 16] >> (4 * (i % 16))) & 0xf);
            if (!s.empty() || d != 0 || i == 0) {
                s.push_back(digits[d]);
            }
        }
        return "0x" + s;
    }

    const bw_value &raw() const { return v_; }

    friend bool operator==(const Value &a, const Value &b) {
        if (a.v_.width != b.v_.width) {
            return false;
        }
        for (int i = 0; i < BW_VALUE_LIMBS; i++) {
            if (a.v_.limbs[i] != b.v_.limbs[i]) {
                return false;
            }
        }
        return true;
    }
    friend bool operator!=(const Value &a, const Value &b) { return !(a == b); }

  private:
    bw_value v_;
};

inline std::ostream &operator<<(std::ostream &os, const Value &v) {
    return os << v.hex() << ":" << v.width();
}

// ----- floating point ------------------------------------------------------------------------

// A binary floating-point format: `eb` exponent bits and `sb` significand bits, the hidden bit
// included, so an encoding is `eb + sb` bits wide. Valid when 2 <= eb <= 31, sb >= 2 and
// eb + sb <= 512 (checked where it is used: `BW_ERR_WIDTH`).
struct FpFormat : bw_fp_format {
    constexpr FpFormat() : bw_fp_format{0, 0} {}
    constexpr FpFormat(uint32_t exponent_bits, uint32_t significand_bits)
        : bw_fp_format{exponent_bits, significand_bits} {}
    constexpr FpFormat(const bw_fp_format &f) : bw_fp_format(f) {}

    // The width of an encoding.
    constexpr uint16_t width() const { return static_cast<uint16_t>(eb + sb); }

    friend constexpr bool operator==(const FpFormat &a, const FpFormat &b) {
        return a.eb == b.eb && a.sb == b.sb;
    }
    friend constexpr bool operator!=(const FpFormat &a, const FpFormat &b) { return !(a == b); }
};

inline constexpr FpFormat F16{5, 11};    // binary16
inline constexpr FpFormat BF16{8, 8};    // bfloat16
inline constexpr FpFormat F32{8, 24};    // binary32
inline constexpr FpFormat F64{11, 53};   // binary64
inline constexpr FpFormat F128{15, 113}; // binary128
inline constexpr FpFormat F256{19, 237}; // binary256
// The values of x87 extended precision (79 bits); `x87_load` and `x87_store` convert from and to
// its 80-bit memory encoding.
inline constexpr FpFormat X87{15, 64};

enum class Rounding : int {
    Rne = BW_RNE, // to nearest, ties to even
    Rna = BW_RNA, // to nearest, ties away from zero
    Rtp = BW_RTP, // toward +infinity
    Rtn = BW_RTN, // toward -infinity
    Rtz = BW_RTZ, // toward zero
};

// The operations of floating-point nodes (`bw_fpop`).
enum class FpOp : int {
    Add = BW_FP_ADD,
    Mul = BW_FP_MUL,
    Div = BW_FP_DIV,
    Fma = BW_FP_FMA,
    Sqrt = BW_FP_SQRT,
    Rem = BW_FP_REM,
    Round = BW_FP_ROUND,
    Min = BW_FP_MIN,
    Max = BW_FP_MAX,
    Eq = BW_FP_EQ,
    Lt = BW_FP_LT,
    Le = BW_FP_LE,
    Convert = BW_FP_CONVERT,
    FromSbv = BW_FP_FROM_SBV,
    FromUbv = BW_FP_FROM_UBV,
    ToSbv = BW_FP_TO_SBV,
    ToUbv = BW_FP_TO_UBV,
};

// Comparisons, false when an operand is a NaN.
enum class FpCmp : int {
    Eq = BW_FPCMP_EQ,
    Lt = BW_FPCMP_LT,
    Le = BW_FPCMP_LE,
    Gt = BW_FPCMP_GT,
    Ge = BW_FPCMP_GE,
};

// Classification tests.
enum class FpTest : int {
    IsNan = BW_FP_ISNAN,
    IsInf = BW_FP_ISINF,
    IsZero = BW_FP_ISZERO,
    IsSubnormal = BW_FP_ISSUBNORMAL,
    IsNormal = BW_FP_ISNORMAL,
    IsNeg = BW_FP_ISNEG,
    IsPos = BW_FP_ISPOS,
};

// The operation of a floating-point node (Kind::Fp).
struct FpNode {
    FpOp op;
    std::optional<Rounding> rm;        // none for Rem, Min, Max and the comparisons
    FpFormat format;                   // of the operands (the result's, from an integer)
    std::optional<FpFormat> to;        // FpOp::Convert: the result's format
    std::optional<uint16_t> int_width; // FpOp::ToSbv, FpOp::ToUbv: the integer's width
};

// ----- expressions ---------------------------------------------------------------------------

class Expr;

// One node: its kind, operator (for unary, binary, comparison and floating-point nodes), width,
// and children.
struct Node {
    Kind kind;
    int op;      // UnOp, BinOp, CmpOp or FpOp by kind; -1 otherwise
    uint16_t lo; // first bit of an extract; output of an extension call
    uint16_t width;
    std::vector<Expr> children;
};

// A handle to an expression node of a context (which must outlive it).
class Expr {
  public:
    Expr() = default;
    Expr(bw_context *cx, bw_expr e) : cx_(cx), e_(e) {}

    bw_expr raw() const { return e_; }
    bw_context *context() const { return cx_; }
    explicit operator bool() const { return e_ != BW_NULL_EXPR; }

    uint16_t width() const {
        uint16_t w = 0;
        detail::check(bw_width(cx_, e_, &w));
        return w;
    }

    // The expression in the text syntax (`BW_PRINT_*` flags).
    std::string str(unsigned flags = 0) const {
        char *s = nullptr;
        detail::check(bw_print(cx_, e_, flags, &s));
        return detail::take(s);
    }

    Node node() const {
        bw_node n;
        detail::check(bw_node_of(cx_, e_, &n));
        Node r{static_cast<Kind>(n.kind), n.op, n.lo, n.width, {}};
        for (uint32_t i = 0; i < n.n_children; i++) {
            r.children.emplace_back(cx_, n.children[i]);
        }
        return r;
    }

    Kind kind() const { return node().kind; }
    std::vector<Expr> children() const { return node().children; }

    // The value of a constant node.
    std::optional<Value> value() const {
        if (kind() != Kind::Const) {
            return std::nullopt;
        }
        bw_value v;
        detail::check(bw_const_value(cx_, e_, &v));
        return Value(v);
    }

    // The name of a symbol node.
    std::optional<std::string> name() const {
        if (kind() != Kind::Symbol) {
            return std::nullopt;
        }
        char *s = nullptr;
        detail::check(bw_symbol_name(cx_, e_, &s));
        return detail::take(s);
    }

    // The number of distinct nodes under this one, itself included.
    uint32_t dag_size() const {
        uint32_t n = 0;
        detail::check(bw_dag_size(cx_, e_, &n));
        return n;
    }

    // A constant of this expression's width (`v` must fit in it).
    Expr constant(uint64_t v) const { return make(bw_const_u64, width(), v); }

    Expr un(UnOp op) const { return make(bw_un, static_cast<int>(op), e_); }
    Expr bin(BinOp op, Expr b) const { return make(bw_bin, static_cast<int>(op), e_, b.e_); }
    Expr cmp(CmpOp op, Expr b) const { return make(bw_cmp, static_cast<int>(op), e_, b.e_); }

    Expr popcnt() const { return un(UnOp::Popcnt); }
    Expr clz() const { return un(UnOp::Clz); }
    Expr ctz() const { return un(UnOp::Ctz); }
    Expr bswap() const { return un(UnOp::Bswap); }
    Expr bitrev() const { return un(UnOp::BitRev); }

    Expr udiv(Expr b) const { return bin(BinOp::UDiv, b); }
    Expr urem(Expr b) const { return bin(BinOp::URem, b); }
    Expr sdiv(Expr b) const { return bin(BinOp::SDiv, b); }
    Expr srem(Expr b) const { return bin(BinOp::SRem, b); }
    Expr umulhi(Expr b) const { return bin(BinOp::UMulHi, b); }
    Expr smulhi(Expr b) const { return bin(BinOp::SMulHi, b); }
    Expr ashr(Expr b) const { return bin(BinOp::AShr, b); }
    Expr rotl(Expr b) const { return bin(BinOp::RotL, b); }
    Expr rotr(Expr b) const { return bin(BinOp::RotR, b); }
    Expr pdep(Expr b) const { return bin(BinOp::Pdep, b); }
    Expr pext(Expr b) const { return bin(BinOp::Pext, b); }

    Expr eq(Expr b) const { return cmp(CmpOp::Eq, b); }
    Expr ne(Expr b) const { return cmp(CmpOp::Ne, b); }
    Expr ult(Expr b) const { return cmp(CmpOp::Ult, b); }
    Expr ule(Expr b) const { return cmp(CmpOp::Ule, b); }
    Expr ugt(Expr b) const { return cmp(CmpOp::Ugt, b); }
    Expr uge(Expr b) const { return cmp(CmpOp::Uge, b); }
    Expr slt(Expr b) const { return cmp(CmpOp::Slt, b); }
    Expr sle(Expr b) const { return cmp(CmpOp::Sle, b); }
    Expr sgt(Expr b) const { return cmp(CmpOp::Sgt, b); }
    Expr sge(Expr b) const { return cmp(CmpOp::Sge, b); }

    Expr zext(uint16_t w) const { return make(bw_zext, e_, w); }
    Expr sext(uint16_t w) const { return make(bw_sext, e_, w); }
    Expr trunc(uint16_t w) const { return make(bw_trunc, e_, w); }
    // Bits [lo, lo + len).
    Expr extract(uint16_t lo, uint16_t len) const { return make(bw_extract, e_, lo, len); }
    // This expression in the high bits, `lo` in the low bits.
    Expr concat(Expr lo) const { return make(bw_concat, e_, lo.e_); }
    // This 1-bit condition selecting `then` or `els`.
    Expr select(Expr then, Expr els) const { return make(bw_select, e_, then.e_, els.e_); }

    // Floating point (the book's chapter specifies it): this expression and the other operands
    // hold encodings of the format `f`, and a result is rounded by `rm`.

    Expr fadd(Expr b, FpFormat f, Rounding rm = Rounding::Rne) const {
        return fp_op(FpOp::Add, rm, f, {e_, b.e_});
    }
    // Built as `this + fneg(b)`.
    Expr fsub(Expr b, FpFormat f, Rounding rm = Rounding::Rne) const {
        return make(bw_fp_sub, static_cast<int>(rm), f, e_, b.e_);
    }
    Expr fmul(Expr b, FpFormat f, Rounding rm = Rounding::Rne) const {
        return fp_op(FpOp::Mul, rm, f, {e_, b.e_});
    }
    Expr fdiv(Expr b, FpFormat f, Rounding rm = Rounding::Rne) const {
        return fp_op(FpOp::Div, rm, f, {e_, b.e_});
    }
    // `this * b + c`, rounded once.
    Expr ffma(Expr b, Expr c, FpFormat f, Rounding rm = Rounding::Rne) const {
        return fp_op(FpOp::Fma, rm, f, {e_, b.e_, c.e_});
    }
    Expr fsqrt(FpFormat f, Rounding rm = Rounding::Rne) const {
        return fp_op(FpOp::Sqrt, rm, f, {e_});
    }
    // The IEEE remainder `this - n * b`, `n` the integer nearest `this / b` (exact).
    Expr frem(Expr b, FpFormat f) const { return fp_op(FpOp::Rem, Rounding::Rne, f, {e_, b.e_}); }
    // Rounding to an integral value.
    Expr fround(FpFormat f, Rounding rm = Rounding::Rne) const {
        return fp_op(FpOp::Round, rm, f, {e_});
    }
    // minimumNumber and maximumNumber: a NaN operand is ignored, and -0 < +0.
    Expr fmin(Expr b, FpFormat f) const { return fp_op(FpOp::Min, Rounding::Rne, f, {e_, b.e_}); }
    Expr fmax(Expr b, FpFormat f) const { return fp_op(FpOp::Max, Rounding::Rne, f, {e_, b.e_}); }

    // Comparisons, 1 bit: false when an operand is a NaN, and +0 equals -0.
    Expr fcmp(FpCmp op, Expr b, FpFormat f) const {
        return make(bw_fp_cmp, static_cast<int>(op), f, e_, b.e_);
    }
    Expr feq(Expr b, FpFormat f) const { return fcmp(FpCmp::Eq, b, f); }
    Expr flt(Expr b, FpFormat f) const { return fcmp(FpCmp::Lt, b, f); }
    Expr fle(Expr b, FpFormat f) const { return fcmp(FpCmp::Le, b, f); }
    Expr fgt(Expr b, FpFormat f) const { return fcmp(FpCmp::Gt, b, f); }
    Expr fge(Expr b, FpFormat f) const { return fcmp(FpCmp::Ge, b, f); }

    // The sign bit flipped, cleared, or taken from `b` (a NaN's too): bit-vector operators.
    Expr fneg(FpFormat f) const { return make(bw_fp_neg, f, e_); }
    Expr fabs(FpFormat f) const { return make(bw_fp_abs, f, e_); }
    Expr fcopysign(Expr b, FpFormat f) const { return make(bw_fp_copysign, f, e_, b.e_); }

    // Classification tests, 1 bit.
    Expr ftest(FpTest t, FpFormat f) const {
        return make(bw_fp_test, static_cast<int>(t), f, e_);
    }
    Expr fisnan(FpFormat f) const { return ftest(FpTest::IsNan, f); }
    Expr fisinf(FpFormat f) const { return ftest(FpTest::IsInf, f); }
    Expr fiszero(FpFormat f) const { return ftest(FpTest::IsZero, f); }
    Expr fissubnormal(FpFormat f) const { return ftest(FpTest::IsSubnormal, f); }
    Expr fisnormal(FpFormat f) const { return ftest(FpTest::IsNormal, f); }
    Expr fisneg(FpFormat f) const { return ftest(FpTest::IsNeg, f); }
    Expr fispos(FpFormat f) const { return ftest(FpTest::IsPos, f); }

    // This value of format `f` converted to the format `to`.
    Expr fconvert(FpFormat to, FpFormat f, Rounding rm = Rounding::Rne) const {
        return fp_op(FpOp::Convert, rm, f, {e_}, to);
    }
    // This integer, signed or unsigned, rounded to the format `f`.
    Expr to_float(FpFormat f, Rounding rm = Rounding::Rne, bool is_signed = true) const {
        return fp_op(is_signed ? FpOp::FromSbv : FpOp::FromUbv, rm, f, {e_});
    }
    // This value of format `f` rounded to an integer of `w` bits, signed or unsigned, and
    // saturated to its range (a NaN gives 0).
    Expr to_int(uint16_t w, FpFormat f, Rounding rm = Rounding::Rne, bool is_signed = true) const {
        return fp_op(is_signed ? FpOp::ToSbv : FpOp::ToUbv, rm, f, {e_}, FpFormat(), w);
    }
    // x87's 80-bit encoding as a value of X87 (79 bits), and back.
    Expr x87_load() const { return make(bw_x87_load, e_); }
    Expr x87_store() const { return make(bw_x87_store, e_); }

    // The operation of a floating-point node.
    std::optional<FpNode> fp_node() const {
        if (kind() != Kind::Fp) {
            return std::nullopt;
        }
        bw_fp_node n;
        detail::check(bw_fp_node_of(cx_, e_, &n));
        FpNode r{static_cast<FpOp>(n.op), std::nullopt, FpFormat(n.format), std::nullopt,
                 std::nullopt};
        if (n.rm >= 0) {
            r.rm = static_cast<Rounding>(n.rm);
        }
        if (r.op == FpOp::Convert) {
            r.to = FpFormat(n.to);
        }
        if (r.op == FpOp::ToSbv || r.op == FpOp::ToUbv) {
            r.int_width = n.int_width;
        }
        return r;
    }

    // Handle identity: equal handles are equal expressions.
    friend bool operator==(Expr a, Expr b) { return a.cx_ == b.cx_ && a.e_ == b.e_; }
    friend bool operator!=(Expr a, Expr b) { return !(a == b); }

  private:
    template <class F, class... A> Expr make(F f, A... args) const {
        bw_expr out = BW_NULL_EXPR;
        detail::check(f(cx_, args..., &out));
        return Expr(cx_, out);
    }

    Expr fp_op(FpOp op, Rounding rm, FpFormat f, std::initializer_list<bw_expr> args,
               FpFormat to = FpFormat(), uint16_t int_width = 0) const {
        return make(bw_fp, static_cast<int>(op), static_cast<int>(rm), f, args.begin(),
                    args.size(), to, int_width);
    }

    bw_context *cx_ = nullptr;
    bw_expr e_ = BW_NULL_EXPR;
};

inline std::ostream &operator<<(std::ostream &os, Expr e) { return os << e.str(); }

// The floating-point operation `op` of format `f` on `args`, operands of one context (see
// `bw_fp`): `rm` is its rounding mode, `to` the result's format for FpOp::Convert, `int_width` the
// result's width for FpOp::ToSbv and FpOp::ToUbv; the operations without them ignore them.
inline Expr fp(FpOp op, FpFormat f, const std::vector<Expr> &args, Rounding rm = Rounding::Rne,
               FpFormat to = FpFormat(), uint16_t int_width = 0) {
    if (args.empty()) {
        throw Error(BW_ERR_INVALID_ARGUMENT, "a floating-point operation needs operands");
    }
    std::vector<bw_expr> raw;
    for (Expr e : args) {
        raw.push_back(e.raw());
    }
    bw_context *cx = args[0].context();
    bw_expr out = BW_NULL_EXPR;
    detail::check(bw_fp(cx, static_cast<int>(op), static_cast<int>(rm), f, raw.data(), raw.size(),
                        to, int_width, &out));
    return Expr(cx, out);
}

#define BITWRIGHT_BINARY_OPERATOR(sym, op)                                                         \
    inline Expr operator sym(Expr a, Expr b) { return a.bin(BinOp::op, b); }                       \
    inline Expr operator sym(Expr a, uint64_t b) { return a.bin(BinOp::op, a.constant(b)); }       \
    inline Expr operator sym(uint64_t a, Expr b) { return b.constant(a).bin(BinOp::op, b); }
BITWRIGHT_BINARY_OPERATOR(+, Add)
BITWRIGHT_BINARY_OPERATOR(-, Sub)
BITWRIGHT_BINARY_OPERATOR(*, Mul)
BITWRIGHT_BINARY_OPERATOR(&, And)
BITWRIGHT_BINARY_OPERATOR(|, Or)
BITWRIGHT_BINARY_OPERATOR(^, Xor)
BITWRIGHT_BINARY_OPERATOR(<<, Shl)
BITWRIGHT_BINARY_OPERATOR(>>, LShr)
#undef BITWRIGHT_BINARY_OPERATOR

inline Expr operator~(Expr a) { return a.un(UnOp::Not); }
inline Expr operator-(Expr a) { return a.un(UnOp::Neg); }

// ----- assumptions, facts, proofs ------------------------------------------------------------

// Constraints known to hold, numbered from 0 in the order they are added.
class Assumptions {
  public:
    Assumptions() : a_(detail::check_new(bw_assumptions_new()), &bw_assumptions_free) {}

    // Assumes that the 1-bit predicate `p` holds (or, with `holds` false, does not); its number.
    uint32_t assume(Expr p, bool holds = true) {
        uint32_t id = 0;
        detail::check(bw_assume(a_.get(), p.context(), p.raw(), holds, &id));
        return id;
    }

    // Whether the constraints contradict each other.
    bool infeasible() const { return bw_assumptions_infeasible(a_.get()); }

    const bw_assumptions *raw() const { return a_.get(); }

  private:
    std::unique_ptr<bw_assumptions, void (*)(bw_assumptions *)> a_;
};

inline const bw_assumptions *raw_of(const Assumptions *a) { return a ? a->raw() : nullptr; }

// What is known about every value of an expression. `relies_on` has bit i set when constraint i
// (bit 63: some constraint from 63 on) was used.
struct Facts {
    Value known_zero, known_one;
    Value umin, umax;
    uint64_t ustride; // the unsigned values are among umin, umin + ustride, ..., umax
    Value smin, smax; // two's-complement bit patterns
    uint64_t relies_on;
};

struct Proof {
    Truth truth;
    uint64_t relies_on;
    explicit operator bool() const { return truth == Truth::True; }
};

inline Facts facts(Expr e, const Assumptions *a = nullptr) {
    bw_facts f;
    detail::check(bw_facts_of(e.context(), e.raw(), raw_of(a), &f));
    return Facts{Value(f.known_zero), Value(f.known_one), Value(f.umin),
                 Value(f.umax),       f.ustride,          Value(f.smin),
                 Value(f.smax),       f.relies_on};
}

namespace detail {
inline Proof proof(const bw_proof &p) { return Proof{static_cast<Truth>(p.truth), p.relies_on}; }
} // namespace detail

// Whether `e` is nonzero (a 1-bit predicate: whether it holds).
inline Proof prove(Expr e, const Assumptions *a = nullptr) {
    bw_proof p;
    detail::check(bw_prove(e.context(), e.raw(), raw_of(a), &p));
    return detail::proof(p);
}

// Whether `x op y` holds.
inline Proof prove(CmpOp op, Expr x, Expr y, const Assumptions *a = nullptr) {
    bw_proof p;
    detail::check(
        bw_prove_cmp(x.context(), static_cast<int>(op), x.raw(), y.raw(), raw_of(a), &p));
    return detail::proof(p);
}

// Whether `e` is an injective (or bijective) function of its subexpression `of`.
inline Proof prove_injective(Expr e, Expr of, bool bijective = false,
                             const Assumptions *a = nullptr) {
    bw_proof p;
    detail::check(bw_prove_injective(e.context(), e.raw(), of.raw(), bijective, raw_of(a), &p));
    return detail::proof(p);
}

// ----- contexts ------------------------------------------------------------------------------

// A script read from SMT-LIB.
struct SmtScript {
    std::vector<std::pair<std::string, Expr>> symbols;
    std::vector<std::pair<std::string, Expr>> definitions;
    std::vector<Expr> assertions;
};

// A hash-consed expression arena. Move-only; its expressions refer to it.
class Context {
  public:
    Context() : cx_(detail::check_new(bw_context_new())) {}
    // At most `max_nodes` nodes and `fact_work` transfers per fact query (0: the default).
    explicit Context(uint32_t max_nodes, uint32_t fact_work = 0)
        : cx_(detail::check_new(bw_context_new_with(max_nodes, fact_work))) {}
    ~Context() { bw_context_free(cx_); }
    Context(const Context &) = delete;
    Context &operator=(const Context &) = delete;
    Context(Context &&o) noexcept : cx_(std::exchange(o.cx_, nullptr)) {}
    Context &operator=(Context &&o) noexcept {
        std::swap(cx_, o.cx_);
        return *this;
    }

    bw_context *raw() const { return cx_; }
    Expr wrap(bw_expr e) const { return Expr(cx_, e); }

    // The number of nodes.
    std::size_t size() const { return bw_context_len(cx_); }
    // Drops every node: every expression of the context becomes stale.
    void clear() { bw_context_clear(cx_); }

    Expr symbol(const std::string &name, uint16_t width) {
        return make(bw_symbol, name.c_str(), width);
    }
    Expr symbol(uint64_t key, uint16_t width) { return make(bw_symbol_u64, key, width); }
    Expr fresh_symbol(uint16_t width) { return make(bw_fresh_symbol, width); }

    Expr constant(const Value &v) { return make(bw_const, &v.raw()); }
    // `v`, which must fit in `width` bits.
    Expr constant(uint16_t width, uint64_t v) { return make(bw_const_u64, width, v); }
    // `v`, which must fit in `width` bits signed.
    Expr constant_signed(uint16_t width, int64_t v) { return make(bw_const_i64, width, v); }

    // Parses expression text; `default_width` (0: none) types what cannot be inferred.
    Expr parse(const std::string &text, uint16_t default_width = 0) {
        return make(bw_parse, text.c_str(), default_width);
    }

    // The value of `e` with each symbol bound.
    Value eval(Expr e, const std::vector<std::pair<Expr, Value>> &env) {
        std::vector<bw_expr> syms;
        std::vector<bw_value> vals;
        for (const auto &[s, v] : env) {
            syms.push_back(s.raw());
            vals.push_back(v.raw());
        }
        bw_value out;
        detail::check(bw_eval(cx_, e.raw(), syms.data(), vals.data(), env.size(), &out));
        return Value(out);
    }

    // `e` with every `from` replaced by its `to` at once.
    Expr substitute(Expr e, const std::vector<std::pair<Expr, Expr>> &map) {
        std::vector<bw_expr> from, to;
        for (const auto &[f, t] : map) {
            from.push_back(f.raw());
            to.push_back(t.raw());
        }
        return make(bw_substitute, e.raw(), from.data(), to.data(), map.size());
    }

    // A QF_BV script (QF_BVFP with floating point) defining the K-th expression as `rootK`.
    std::string to_smtlib(const std::vector<Expr> &roots) {
        std::vector<bw_expr> r;
        for (Expr e : roots) {
            r.push_back(e.raw());
        }
        char *s = nullptr;
        detail::check(bw_smtlib_export(cx_, r.data(), r.size(), &s));
        return detail::take(s);
    }

    // Reads a QF_BV script, floating-point (QF_BVFP) terms included, into this context.
    SmtScript from_smtlib(const std::string &script) {
        bw_smt_import *imp = nullptr;
        detail::check(bw_smtlib_import(cx_, script.c_str(), &imp));
        std::unique_ptr<bw_smt_import, void (*)(bw_smt_import *)> guard(imp,
                                                                         &bw_smt_import_free);
        SmtScript out;
        for (int part : {BW_SMT_SYMBOLS, BW_SMT_DEFINITIONS, BW_SMT_ASSERTIONS}) {
            std::size_t n = bw_smt_import_count(imp, part);
            for (std::size_t i = 0; i < n; i++) {
                bw_expr e = BW_NULL_EXPR;
                const char *name = nullptr;
                detail::check(bw_smt_import_get(imp, part, i, &e, &name));
                if (part == BW_SMT_SYMBOLS) {
                    out.symbols.emplace_back(name, wrap(e));
                } else if (part == BW_SMT_DEFINITIONS) {
                    out.definitions.emplace_back(name, wrap(e));
                } else {
                    out.assertions.push_back(wrap(e));
                }
            }
        }
        return out;
    }

  private:
    template <class F, class... A> Expr make(F f, A... args) {
        bw_expr out = BW_NULL_EXPR;
        detail::check(f(cx_, args..., &out));
        return Expr(cx_, out);
    }

    bw_context *cx_;
};

// ----- engines -------------------------------------------------------------------------------

// Caps on the work of one call; starts at the default budget.
struct Budget : bw_budget {
    Budget() : bw_budget(bw_budget_default()) {}
};

// The result for one root: equal to the input wherever the constraints in `relies_on` hold.
struct Outcome {
    Expr expr;
    bool changed;
    End end;
    int limit; // bw_limit when `end` is End::Budget; -1 otherwise
    uint64_t relies_on;
};

// A simplifier. Immutable, cheap to copy, and safe to share between threads.
class Engine {
  public:
    explicit Engine(Preset preset = Preset::Standard)
        : e_(detail::check_new(bw_engine_new(static_cast<int>(preset))), &bw_engine_free) {}

    // Fact folding, the built-in rules and the normal-form passes.
    static Engine standard() { return Engine(Preset::Standard); }
    // Also the deobfuscation passes and the MBA service (the command line's `simplify`).
    static Engine deobfuscate() { return Engine(Preset::Deobfuscate); }

    Expr simplify(Expr e) const {
        bw_expr out = BW_NULL_EXPR;
        detail::check(bw_simplify(e_.get(), e.context(), e.raw(), &out));
        return Expr(e.context(), out);
    }

    // Simplifies roots of one context in one call.
    std::vector<Outcome> run(const std::vector<Expr> &roots, const Budget *budget = nullptr,
                             const Assumptions *a = nullptr) const {
        return run_with(roots, [&](bw_context *cx, const bw_expr *r, size_t n, bw_outcome *out) {
            return bw_engine_run(e_.get(), cx, r, n, budget, raw_of(a), out);
        });
    }

    // Simplifies roots of one context each on its own, on up to `threads` threads (0: all).
    std::vector<Outcome> run_each(const std::vector<Expr> &roots, size_t threads = 0,
                                  const Budget *budget = nullptr,
                                  const Assumptions *a = nullptr) const {
        return run_with(roots, [&](bw_context *cx, const bw_expr *r, size_t n, bw_outcome *out) {
            return bw_engine_run_each(e_.get(), cx, r, n, threads, budget, raw_of(a), out);
        });
    }

    const bw_engine *raw() const { return e_.get(); }

  private:
    friend class EngineBuilder;
    explicit Engine(bw_engine *e) : e_(e, &bw_engine_free) {}

    template <class Call>
    static std::vector<Outcome> run_with(const std::vector<Expr> &roots, Call call) {
        if (roots.empty()) {
            return {};
        }
        std::vector<bw_expr> r;
        for (Expr e : roots) {
            r.push_back(e.raw());
        }
        std::vector<bw_outcome> out(roots.size());
        bw_context *cx = roots[0].context();
        detail::check(call(cx, r.data(), r.size(), out.data()));
        std::vector<Outcome> res;
        for (const bw_outcome &o : out) {
            res.push_back(
                Outcome{Expr(cx, o.expr), o.changed, static_cast<End>(o.end), o.limit, o.relies_on});
        }
        return res;
    }

    std::shared_ptr<bw_engine> e_;
};

// An engine with rules of your own.
class EngineBuilder {
  public:
    explicit EngineBuilder(Preset preset = Preset::Standard)
        : b_(detail::check_new(bw_engine_builder_new(static_cast<int>(preset))),
             &bw_engine_builder_free) {}

    // Adds the rules of a `.bwr` source, with the proof ledger vouching for them, or none to
    // check them now.
    EngineBuilder &rules(const std::string &source,
                         const std::optional<std::string> &ledger = std::nullopt) {
        detail::check(bw_engine_builder_add_rules(b_.get(), source.c_str(),
                                                  ledger ? ledger->c_str() : nullptr));
        return *this;
    }

    EngineBuilder &max_rounds(uint8_t n) {
        bw_engine_builder_set_max_rounds(b_.get(), n);
        return *this;
    }

    // Also the rules that hold for floats as values (every NaN one value).
    EngineBuilder &float_values(bool yes = true) {
        bw_engine_builder_set_float_values(b_.get(), yes);
        return *this;
    }

    // Refuses the rewrites of a rule (`group::rule`) or a pass (`linear`, …).
    EngineBuilder &refuse(const std::string &name) {
        detail::check(bw_engine_builder_refuse(b_.get(), name.c_str()));
        return *this;
    }

    Engine build() const {
        bw_engine *e = nullptr;
        detail::check(bw_engine_builder_build(b_.get(), &e));
        return Engine(e);
    }

  private:
    std::unique_ptr<bw_engine_builder, void (*)(bw_engine_builder *)> b_;
};

// Checks every rule of a `.bwr` source; the proof ledger vouching for them.
inline std::string check_rules(const std::string &source) {
    char *s = nullptr;
    detail::check(bw_check_rules(source.c_str(), &s));
    return detail::take(s);
}

// ----- proofs and synthesis ------------------------------------------------------------------

// Whether `a` and `b` are equal for every value of their symbols: true (proved), false
// (refuted), or no value (not decided within `conflicts`).
inline std::optional<bool> equivalent(Expr a, Expr b, uint64_t conflicts = 1000000) {
    int v = BW_UNDECIDED;
    detail::check(bw_equivalent(a.context(), a.raw(), b.raw(), conflicts, &v));
    if (v == BW_UNDECIDED) {
        return std::nullopt;
    }
    return v == BW_EQUIVALENT;
}

// The smallest expression equal to `e` that synthesis finds (proved), if any.
inline std::optional<Expr> synthesize(Expr e, uint8_t max_size = 7) {
    bw_expr out = BW_NULL_EXPR;
    bool found = false;
    detail::check(bw_synthesize(e.context(), e.raw(), max_size, &out, &found));
    if (!found) {
        return std::nullopt;
    }
    return Expr(e.context(), out);
}

// ----- memory --------------------------------------------------------------------------------

// A memory: loads and stores as expressions of one context.
class Memory {
  public:
    explicit Memory(const std::string &name = "mem", uint16_t addr_width = 64,
                    uint16_t cell_width = 8, bool big_endian = false)
        : m_(detail::check_new(bw_memory_new(name.c_str(), addr_width, cell_width, big_endian)),
             &bw_memory_free) {}

    // Known contents of 8-bit cells from `start` on, before any load or store.
    void set_bytes(uint64_t start, const std::vector<uint8_t> &data) {
        detail::check(bw_memory_set_bytes(m_.get(), start, data.data(), data.size()));
    }
    void store(Expr addr, Expr value) {
        detail::check(bw_memory_store(m_.get(), addr.context(), addr.raw(), value.raw()));
    }
    Expr load(Expr addr, uint16_t cells = 1) {
        bw_expr out = BW_NULL_EXPR;
        detail::check(bw_memory_load(m_.get(), addr.context(), addr.raw(), cells, &out));
        return Expr(addr.context(), out);
    }

  private:
    std::unique_ptr<bw_memory, void (*)(bw_memory *)> m_;
};

// ----- lifted code ---------------------------------------------------------------------------

enum class FrontEnd : int { Pcode = BW_LIFT_PCODE, Vex = BW_LIFT_VEX, Llvm = BW_LIFT_LLVM };

// A block of lifted code, read into expressions.
struct Lifted {
    std::vector<std::pair<std::string, Expr>> inputs;  // registers read before written
    std::vector<std::pair<std::string, Expr>> outputs; // registers written: final values
    std::vector<std::pair<Expr, Expr>> stores;         // (address, value)
    std::vector<std::pair<Expr, Expr>> exits;          // (condition, target)
    std::optional<Expr> next;

    // The final value of a register (an output, else an input).
    std::optional<Expr> reg(const std::string &name) const {
        for (const auto *list : {&outputs, &inputs}) {
            for (const auto &[n, e] : *list) {
                if (n == name) {
                    return e;
                }
            }
        }
        return std::nullopt;
    }
};

// Reads lifted code into `cx` (`function` names an LLVM IR function; empty: the first).
inline Lifted lift(Context &cx, FrontEnd from, const std::string &code,
                   const std::string &function = "") {
    bw_lifted *l = nullptr;
    detail::check(bw_lift(cx.raw(), static_cast<int>(from), code.c_str(),
                          function.empty() ? nullptr : function.c_str(), &l));
    std::unique_ptr<bw_lifted, void (*)(bw_lifted *)> guard(l, &bw_lifted_free);
    Lifted out;
    for (int part : {BW_LIFTED_INPUTS, BW_LIFTED_OUTPUTS, BW_LIFTED_STORES, BW_LIFTED_EXITS}) {
        std::size_t n = bw_lifted_count(l, part);
        for (std::size_t i = 0; i < n; i++) {
            const char *name = nullptr;
            bw_expr a = BW_NULL_EXPR, b = BW_NULL_EXPR;
            detail::check(bw_lifted_get(l, part, i, &name, &a, &b));
            Expr ea(cx.raw(), a), eb(cx.raw(), b);
            switch (part) {
            case BW_LIFTED_INPUTS: out.inputs.emplace_back(name, ea); break;
            case BW_LIFTED_OUTPUTS: out.outputs.emplace_back(name, ea); break;
            case BW_LIFTED_STORES: out.stores.emplace_back(ea, eb); break;
            default: out.exits.emplace_back(ea, eb); break;
            }
        }
    }
    bw_expr next = BW_NULL_EXPR;
    bool has = false;
    detail::check(bw_lifted_next(l, &next, &has));
    if (has) {
        out.next = Expr(cx.raw(), next);
    }
    return out;
}

// ----- compiler transformations --------------------------------------------------------------

// A report on transformations (as `bitwright prove` prints it) and its counts.
struct TransformReport {
    std::string text;
    uint32_t valid = 0, invalid = 0, undecided = 0;
};

namespace detail {
inline TransformReport report(char *s, const bw_transform_counts &c) {
    return TransformReport{take(s), c.valid, c.invalid, c.undecided};
}
} // namespace detail

// Verifies transformations in the syntax of the Alive paper.
inline TransformReport verify_transforms(const std::string &text, uint64_t conflicts = 0) {
    char *s = nullptr;
    bw_transform_counts c{};
    detail::check(bw_transform_verify(text.c_str(), conflicts, &s, &c));
    return detail::report(s, c);
}

// Translation validation of LLVM IR functions (`tgt` empty: @tgt against @src of `src`).
inline TransformReport validate_functions(const std::string &src, const std::string &tgt = "",
                                          uint64_t conflicts = 0) {
    char *s = nullptr;
    bw_transform_counts c{};
    detail::check(bw_transform_validate(src.c_str(), tgt.empty() ? nullptr : tgt.c_str(),
                                        conflicts, &s, &c));
    return detail::report(s, c);
}

// Each transformation's inferred precondition: `name TAB precondition TAB verdict` lines.
inline std::string infer_preconditions(const std::string &text) {
    char *s = nullptr;
    detail::check(bw_transform_infer(text.c_str(), &s));
    return detail::take(s);
}

} // namespace bitwright

#endif // BITWRIGHT_HPP

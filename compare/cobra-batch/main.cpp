// Portions of this file (EvaluateToSignature, and SimplifyOne, which is SimplifyAndPrint with the
// printing replaced by a returned answer) are adapted from CoBRA's tools/cobra-cli/main.cpp
// (Trail of Bits, https://github.com/trailofbits/CoBRA, commit af44b8a), licensed under the
// Apache License, Version 2.0: see LICENSE-APACHE in this directory. The rest of the file follows
// bitwright's license.
//
// cobra-batch: runs CoBRA's command-line pipeline (tools/cobra-cli/main.cpp) on each line of a
// file and writes, per line, the microseconds and peak heap bytes the simplification took, a
// status and CoBRA's answer:
//
//   cobra-batch INPUT OUTPUT [--bitwidth N] [--max-vars N]
//   output line: MICROS <tab> HEAP <tab> ok|unsupported|error <tab> TEXT
//
// The pipeline is the CLI's, step for step: parse, fold constant bitwise subtrees, evaluate the
// signature, Simplify with spot checks, and the full-width check. Timing and heap cover
// everything from the text to the answer, parsing included, as for every tool in
// bitwright-compare. `unsupported` answers are CoBRA's unchanged expression, as the CLI prints
// them.

#include "ExprParser.h"
#include "cobra/core/Classifier.h"
#include "cobra/core/Expr.h"
#include "cobra/core/ExprUtils.h"
#include "cobra/core/SignatureChecker.h"
#include "cobra/core/Simplifier.h"

#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <new>
#include <string>
#include <vector>

// ----- heap counting: requested bytes, like the Rust side's counting allocator --------------

namespace {
    std::size_t g_live = 0;
    std::size_t g_peak = 0;

    void *CountedAlloc(std::size_t n, std::size_t align) {
        // A header before the block holds its size and the header's own size.
        const std::size_t head = align < 16 ? 16 : align;
        void *base             = nullptr;
        if (align <= 16) {
            base = std::malloc(n + head);
        } else {
            const std::size_t total = (n + head + align - 1) / align * align;
            base                    = std::aligned_alloc(align, total);
        }
        if (base == nullptr) { throw std::bad_alloc(); }
        auto *p                              = static_cast< char * >(base) + head;
        reinterpret_cast< std::size_t * >(p)[-1] = n;
        reinterpret_cast< std::size_t * >(p)[-2] = head;
        g_live += n;
        if (g_live > g_peak) { g_peak = g_live; }
        return p;
    }

    void CountedFree(void *ptr) noexcept {
        if (ptr == nullptr) { return; }
        auto *p                  = static_cast< char * >(ptr);
        const std::size_t n      = reinterpret_cast< std::size_t * >(p)[-1];
        const std::size_t head   = reinterpret_cast< std::size_t * >(p)[-2];
        g_live -= n;
        std::free(p - head);
    }

    std::size_t HeapStart() {
        g_peak = g_live;
        return g_live;
    }
} // namespace

void *operator new(std::size_t n) { return CountedAlloc(n, 16); }
void *operator new[](std::size_t n) { return CountedAlloc(n, 16); }
void *operator new(std::size_t n, std::align_val_t a) {
    return CountedAlloc(n, static_cast< std::size_t >(a));
}
void *operator new[](std::size_t n, std::align_val_t a) {
    return CountedAlloc(n, static_cast< std::size_t >(a));
}
void operator delete(void *p) noexcept { CountedFree(p); }
void operator delete[](void *p) noexcept { CountedFree(p); }
void operator delete(void *p, std::size_t) noexcept { CountedFree(p); }
void operator delete[](void *p, std::size_t) noexcept { CountedFree(p); }
void operator delete(void *p, std::align_val_t) noexcept { CountedFree(p); }
void operator delete[](void *p, std::align_val_t) noexcept { CountedFree(p); }
void operator delete(void *p, std::size_t, std::align_val_t) noexcept { CountedFree(p); }
void operator delete[](void *p, std::size_t, std::align_val_t) noexcept { CountedFree(p); }

// ----- the CLI's pipeline --------------------------------------------------------------------

namespace {
    // tools/cobra-cli/main.cpp: EvaluateToSignature.
    std::vector< uint64_t >
    EvaluateToSignature(const cobra::Expr &ast, uint32_t num_vars, uint32_t bitwidth) {
        const std::size_t kLen = std::size_t{ 1 } << num_vars;
        std::vector< uint64_t > sig(kLen);
        for (std::size_t i = 0; i < kLen; ++i) {
            std::vector< uint64_t > var_values(num_vars);
            for (uint32_t v = 0; v < num_vars; ++v) { var_values[v] = (i >> v) & 1; }
            sig[i] = cobra::EvalExpr(ast, var_values, bitwidth);
        }
        return sig;
    }

    struct Answer {
        std::string status;
        std::string text;
    };

    // tools/cobra-cli/main.cpp: SimplifyAndPrint, without printing.
    Answer SimplifyOne(
        const cobra::Expr &ast, const std::vector< std::string > &vars, uint32_t bitwidth,
        uint32_t max_vars
    ) {
        auto num_vars = static_cast< uint32_t >(vars.size());
        auto sig      = EvaluateToSignature(ast, num_vars, bitwidth);
        cobra::Options opts{ .bitwidth = bitwidth, .max_vars = max_vars, .spot_check = true };
        opts.evaluator = cobra::Evaluator::FromExpr(
            ast, bitwidth, cobra::EvaluatorTraceKind::kCliOriginalAst
        );
        auto result = cobra::Simplify(sig, vars, &ast, opts);
        if (!result.has_value()) { return { "error", result.error().message }; }
        const auto &out = result.value();
        if (out.kind == cobra::SimplifyOutcome::Kind::kError) {
            return { "error", out.diag.reason };
        }
        if (out.kind == cobra::SimplifyOutcome::Kind::kUnchangedUnsupported) {
            return { "unsupported", cobra::Render(*out.expr, vars, bitwidth) };
        }
        std::vector< uint32_t > var_map;
        if (out.real_vars.size() < vars.size()) {
            var_map = cobra::BuildVarSupport(vars, out.real_vars);
        }
        auto fw = cobra::FullWidthCheck(ast, num_vars, *out.expr, var_map, bitwidth);
        if (!fw.passed) {
            return { "error", "CoB result is only correct on {0,1} inputs (polynomial target)" };
        }
        return { "ok", cobra::Render(*out.expr, out.real_vars, bitwidth) };
    }

    std::string OneLine(std::string s) {
        for (auto &c : s) {
            if (c == '\n' || c == '\t' || c == '\r') { c = ' '; }
        }
        return s;
    }
} // namespace

int main(int argc, char *argv[]) {
    if (argc < 3) {
        std::cerr << "usage: cobra-batch INPUT OUTPUT [--bitwidth N] [--max-vars N]\n";
        return 2;
    }
    uint32_t bitwidth = 64;
    uint32_t max_vars = 16;
    for (int i = 3; i + 1 < argc; i += 2) {
        const std::string opt = argv[i];
        const auto value      = static_cast< uint32_t >(std::stoul(argv[i + 1]));
        if (opt == "--bitwidth") {
            bitwidth = value;
        } else if (opt == "--max-vars") {
            max_vars = value;
        } else {
            std::cerr << "unknown option " << opt << "\n";
            return 2;
        }
    }
    std::ifstream in(argv[1]);
    std::ofstream out(argv[2]);
    if (!in || !out) {
        std::cerr << "cannot open the input or output file\n";
        return 1;
    }
    std::string line;
    while (std::getline(in, line)) {
        const auto base = HeapStart();
        const auto t0   = std::chrono::steady_clock::now();
        auto parsed     = cobra::ParseToAst(line, bitwidth);
        if (!parsed.has_value()) {
            out << "0\t0\terror\t" << OneLine(parsed.error().message) << "\n";
            continue;
        }
        const auto &vars = parsed.value().vars;
        Answer a;
        {
            auto folded = cobra::FoldConstantBitwise(std::move(parsed.value().expr), bitwidth);
            a           = SimplifyOne(*folded, vars, bitwidth, max_vars);
        }
        const auto t1    = std::chrono::steady_clock::now();
        const auto heap  = g_peak - base;
        const double us  = std::chrono::duration< double, std::micro >(t1 - t0).count();
        out << us << "\t" << heap << "\t" << a.status << "\t" << OneLine(a.text) << "\n";
    }
    return 0;
}

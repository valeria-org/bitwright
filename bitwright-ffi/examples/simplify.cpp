// Simplifies, evaluates and reasons about expressions from C++.
//
//   cargo build --release -p bitwright-ffi
//   c++ -std=c++17 -I bitwright-ffi/include bitwright-ffi/examples/simplify.cpp
//       -L target/release -lbitwright -o simplify
//   LD_LIBRARY_PATH=target/release ./simplify
#include <iostream>

#include "bitwright.hpp"

namespace bw = bitwright;

int main() {
    bw::Context cx;
    bw::Engine engine = bw::Engine::standard();

    // Operators build expressions; integers are constants of the other operand's width.
    bw::Expr x = cx.symbol("x", 64), y = cx.symbol("y", 64);
    std::cout << engine.simplify((x & y) + (x | y)) << "\n";   // x + y
    std::cout << engine.simplify(((x ^ 0x5a) + 3 - 3) ^ 0x5a) << "\n"; // x

    // Text works too, with `let` for sharing.
    bw::Expr h = cx.parse("let m = (x ^ 0xd3220fb78e33751f) * 0xd3220fb78e33751f; "
                          "(m ^ ((m >>u 32) >>u (m >>u 60))) * 0xd3220fb78e33751f == 0");
    std::cout << engine.simplify(h) << "\n"; // x == 0xd3220fb78e33751f

    // Linear MBA needs the deobfuscation preset.
    bw::Expr mba = cx.parse("(x ^ y) + 2 * (x & y)", 64);
    std::cout << bw::Engine::deobfuscate().simplify(mba) << "\n"; // x + y

    // Evaluation, at any width up to 512 bits.
    bw::Expr a = cx.symbol("a", 128);
    bw::Value v = cx.eval(a * a + 1, {{a, bw::Value::from_limbs(128, {0, 1})}});
    std::cout << "(2^64)^2 + 1 mod 2^128 = " << v << "\n";

    // Facts, and proofs under assumptions.
    bw::Expr b = cx.symbol("b", 8);
    bw::Facts f = bw::facts((b & 0xf0) | 1);
    std::cout << "known zero " << f.known_zero << ", range [" << f.umin << ", " << f.umax
              << "] by " << f.ustride << "\n";
    bw::Assumptions as;
    as.assume(b.ult(b.constant(16)));
    std::cout << "b <u 16 proves (b & 0xf0) == 0: "
              << (bw::prove(bw::CmpOp::Eq, b & 0xf0, b.constant(0), &as) ? "yes" : "no") << "\n";

    // Inspecting a node.
    bw::Node n = (x + y).node();
    std::cout << "x + y has " << n.children.size() << " children: " << n.children[0] << ", "
              << n.children[1] << "\n";

    // Errors are exceptions.
    try {
        cx.parse("x +");
    } catch (const bw::Error &e) {
        std::cout << "error " << e.status() << ": " << e.what() << "\n";
    }
    return 0;
}

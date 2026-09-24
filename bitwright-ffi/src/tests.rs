//! The C API called from Rust, as C would call it: results, and every error path (NULL
//! pointers, unknown enumerations, foreign and stale handles, values that do not fit).

use core::ptr::{null, null_mut};
use std::ffi::{CStr, CString};

use super::*;

fn cstr(s: &str) -> CString {
    CString::new(s).unwrap()
}

fn last_error() -> String {
    unsafe { CStr::from_ptr(bw_last_error()) }
        .to_str()
        .unwrap()
        .to_string()
}

/// Takes a string returned by the library.
fn take(s: *mut c_char) -> String {
    let r = unsafe { CStr::from_ptr(s) }.to_str().unwrap().to_string();
    unsafe { bw_string_free(s) };
    r
}

struct Cx(*mut BwContext);

impl Cx {
    fn new() -> Cx {
        Cx(bw_context_new())
    }

    fn parse(&self, s: &str, w: u16) -> u64 {
        let mut e = 0;
        let st = unsafe { bw_parse(self.0, cstr(s).as_ptr(), w, &mut e) };
        assert_eq!(st, BW_OK, "{}", last_error());
        e
    }

    fn print(&self, e: u64) -> String {
        let mut s = null_mut();
        assert_eq!(unsafe { bw_print(self.0, e, 0, &mut s) }, BW_OK);
        take(s)
    }

    fn sym(&self, name: &str, w: u16) -> u64 {
        let mut e = 0;
        assert_eq!(
            unsafe { bw_symbol(self.0, cstr(name).as_ptr(), w, &mut e) },
            BW_OK
        );
        e
    }

    fn konst(&self, w: u16, v: u64) -> u64 {
        let mut e = 0;
        assert_eq!(unsafe { bw_const_u64(self.0, w, v, &mut e) }, BW_OK);
        e
    }
}

impl Drop for Cx {
    fn drop(&mut self) {
        unsafe { bw_context_free(self.0) };
    }
}

fn val(w: u16, v: u64) -> BwValue {
    let mut limbs = [0; 8];
    limbs[0] = v;
    BwValue { width: w, limbs }
}

#[test]
fn version_and_abi() {
    assert_eq!(bw_abi_version(), ABI_VERSION);
    let v = unsafe { CStr::from_ptr(bw_version()) }.to_str().unwrap();
    assert_eq!(v, env!("CARGO_PKG_VERSION"));
}

#[test]
fn the_header_declares_every_entry_point_and_matches_the_tables() {
    let header = include_str!("../include/bitwright.h");
    let source = include_str!("lib.rs");
    let exported: Vec<&str> = source
        .lines()
        .filter_map(|l| l.split("extern \"C\" fn ").nth(1))
        .map(|rest| rest.split('(').next().unwrap())
        .collect();
    assert!(exported.len() > 50);
    for name in &exported {
        assert!(
            header.contains(&format!(" {name}(")) || header.contains(&format!("*{name}(")),
            "`{name}` is not declared in bitwright.h"
        );
    }
    // Every function the header declares is exported (the inline value helpers aside).
    for decl in header.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '(')) {
        if let Some(name) = decl.strip_suffix('(')
            && name.starts_with("bw_")
            && !name.starts_with("bw_value_")
        {
            assert!(
                exported.contains(&name),
                "`{name}` is declared but not exported"
            );
        }
    }
    // The enumeration values of the header are the tables' positions.
    let value_of = |name: &str| -> usize {
        let at = header.find(&format!("{name} = ")).expect(name) + name.len() + 3;
        let digits: String = header[at..]
            .chars()
            .take_while(char::is_ascii_digit)
            .collect();
        digits.parse().unwrap()
    };
    for (i, op) in UNOPS.iter().enumerate() {
        assert_eq!(value_of(&format!("BW_{}", op.name().to_uppercase())), i);
    }
    for (i, op) in BINOPS.iter().enumerate() {
        assert_eq!(value_of(&format!("BW_{}", op.name().to_uppercase())), i);
    }
    for (i, op) in CMPOPS.iter().enumerate() {
        assert_eq!(value_of(&format!("BW_{op:?}").to_uppercase()), i);
    }
    let limits = [
        "NODE_VISITS",
        "CANDIDATES",
        "MATCH_STEPS",
        "REWRITES",
        "NEW_NODES",
        "FACT_WORK",
        "PASS_WORK",
        "MBA_CALLS",
        "EQSAT_NODES",
        "EQSAT_WORK",
        "DEADLINE",
        "ARENA_CAPACITY",
    ];
    for (i, l) in limits.iter().enumerate() {
        assert_eq!(value_of(&format!("BW_LIMIT_{l}")), i);
    }
    for (name, code) in [
        ("BW_ERR_WIDTH", BW_ERR_WIDTH),
        ("BW_ERR_VALUE", BW_ERR_VALUE),
        ("BW_ERR_STALE_EXPR", BW_ERR_STALE_EXPR),
        ("BW_ERR_FOREIGN_EXPR", BW_ERR_FOREIGN_EXPR),
        ("BW_ERR_SYMBOL_WIDTH", BW_ERR_SYMBOL_WIDTH),
        ("BW_ERR_ARENA_FULL", BW_ERR_ARENA_FULL),
        ("BW_ERR_UNBOUND_SYMBOL", BW_ERR_UNBOUND_SYMBOL),
        ("BW_ERR_ENV_WIDTH", BW_ERR_ENV_WIDTH),
        ("BW_ERR_SYNTAX", BW_ERR_SYNTAX),
        (
            "BW_ERR_DUPLICATE_SUBSTITUTION",
            BW_ERR_DUPLICATE_SUBSTITUTION,
        ),
        ("BW_ERR_UNSUPPORTED", BW_ERR_UNSUPPORTED),
        ("BW_ERR_CONTRACT", BW_ERR_CONTRACT),
        ("BW_ERR_INVALID_ARGUMENT", BW_ERR_INVALID_ARGUMENT),
        ("BW_ERR_RULES", BW_ERR_RULES),
        ("BW_ERR_INFEASIBLE", BW_ERR_INFEASIBLE),
        ("BW_ERR_PANIC", BW_ERR_PANIC),
        ("BW_KIND_CONST", KIND_CONST),
        ("BW_KIND_SYMBOL", KIND_SYMBOL),
        ("BW_KIND_UNARY", KIND_UNARY),
        ("BW_KIND_BINARY", KIND_BINARY),
        ("BW_KIND_COMPARE", KIND_COMPARE),
        ("BW_KIND_ZEXT", KIND_ZEXT),
        ("BW_KIND_SEXT", KIND_SEXT),
        ("BW_KIND_EXTRACT", KIND_EXTRACT),
        ("BW_KIND_CONCAT", KIND_CONCAT),
        ("BW_KIND_SELECT", KIND_SELECT),
        ("BW_KIND_EXT", KIND_EXT),
        ("BW_PRESET_STANDARD", PRESET_STANDARD),
        ("BW_PRESET_DEOBFUSCATE", PRESET_DEOBFUSCATE),
        ("BW_SMT_SYMBOLS", SMT_SYMBOLS),
        ("BW_SMT_DEFINITIONS", SMT_DEFINITIONS),
        ("BW_SMT_ASSERTIONS", SMT_ASSERTIONS),
    ] {
        assert_eq!(value_of(name), code as usize, "{name}");
    }
    assert!(header.contains(&format!("#define BW_ABI_VERSION {ABI_VERSION}\n")));
    assert!(header.contains(&format!("#define BW_PRINT_NO_LETS {PRINT_NO_LETS}u ")));
    assert!(header.contains(&format!(
        "#define BW_PRINT_SYMBOL_WIDTHS {PRINT_SYMBOL_WIDTHS}u "
    )));
}

#[test]
fn parse_simplify_print() {
    let cx = Cx::new();
    let engine = bw_engine_new(PRESET_STANDARD);
    assert!(!engine.is_null());
    let e = cx.parse("(x & y) + (x | y)", 64);
    let mut s = 0;
    assert_eq!(unsafe { bw_simplify(engine, cx.0, e, &mut s) }, BW_OK);
    assert_eq!(cx.print(s), "x + y");
    // Printing flags: `let` bindings and symbol widths.
    let shared = cx.parse("let t = x * y; t + (t >>u 3)", 64);
    let mut p = null_mut();
    assert_eq!(unsafe { bw_print(cx.0, shared, 0, &mut p) }, BW_OK);
    assert!(take(p).starts_with("let"));
    let flags = PRINT_NO_LETS | PRINT_SYMBOL_WIDTHS;
    assert_eq!(unsafe { bw_print(cx.0, shared, flags, &mut p) }, BW_OK);
    assert_eq!(take(p), "x:64 * y:64 + (x * y >>u 3)");
    unsafe { bw_engine_free(engine) };
}

#[test]
fn the_deobfuscation_preset_solves_mba() {
    let cx = Cx::new();
    let engine = bw_engine_new(PRESET_DEOBFUSCATE);
    let e = cx.parse("(x ^ y) + 2 * (x & y)", 64);
    let mut s = 0;
    assert_eq!(unsafe { bw_simplify(engine, cx.0, e, &mut s) }, BW_OK);
    assert_eq!(cx.print(s), "x + y");
    unsafe { bw_engine_free(engine) };
}

#[test]
fn constructors_and_inspection() {
    let cx = Cx::new();
    let x = cx.sym("x", 16);
    let k = cx.konst(16, 0x1234);
    let mut e = 0;
    let mut n = BwNode {
        kind: -9,
        op: -9,
        width: 0,
        lo: 0,
        n_children: 0,
        children: [0; 3],
    };
    unsafe {
        assert_eq!(bw_bin(cx.0, 17, x, k, &mut e), BW_OK); // pdep
        assert_eq!(bw_node_of(cx.0, e, &mut n), BW_OK);
        assert_eq!(
            (n.kind, n.op, n.width, n.n_children),
            (KIND_BINARY, 17, 16, 2)
        );
        assert_eq!(&n.children[..2], &[x, k]);
        // `ugt` is stored as a swapped `ult`.
        assert_eq!(bw_cmp(cx.0, 4, x, k, &mut e), BW_OK);
        assert_eq!(bw_node_of(cx.0, e, &mut n), BW_OK);
        assert_eq!((n.kind, n.op, n.width), (KIND_COMPARE, 2, 1));
        assert_eq!(&n.children[..2], &[k, x]);
        assert_eq!(bw_un(cx.0, 2, x, &mut e), BW_OK); // popcnt
        assert_eq!(bw_node_of(cx.0, e, &mut n), BW_OK);
        assert_eq!((n.kind, n.op, n.n_children), (KIND_UNARY, 2, 1));
        assert_eq!(bw_extract(cx.0, x, 4, 8, &mut e), BW_OK);
        assert_eq!(bw_node_of(cx.0, e, &mut n), BW_OK);
        assert_eq!((n.kind, n.op, n.lo, n.width), (KIND_EXTRACT, -1, 4, 8));
        assert_eq!(bw_zext(cx.0, e, 32, &mut e), BW_OK);
        assert_eq!(bw_node_of(cx.0, e, &mut n), BW_OK);
        assert_eq!((n.kind, n.width), (KIND_ZEXT, 32));
        let mut c = 0;
        assert_eq!(bw_cmp(cx.0, 6, x, k, &mut c), BW_OK);
        assert_eq!(bw_select(cx.0, c, x, k, &mut e), BW_OK);
        assert_eq!(bw_node_of(cx.0, e, &mut n), BW_OK);
        assert_eq!((n.kind, n.n_children), (KIND_SELECT, 3));
        assert_eq!(bw_concat(cx.0, x, k, &mut e), BW_OK);
        assert_eq!(bw_node_of(cx.0, e, &mut n), BW_OK);
        assert_eq!((n.kind, n.width), (KIND_CONCAT, 32));
        assert_eq!(bw_node_of(cx.0, k, &mut n), BW_OK);
        assert_eq!((n.kind, n.n_children), (KIND_CONST, 0));
        let mut v = val(1, 0);
        assert_eq!(bw_const_value(cx.0, k, &mut v), BW_OK);
        assert_eq!((v.width, v.limbs[0]), (16, 0x1234));
        assert_eq!(bw_const_value(cx.0, x, &mut v), BW_ERR_INVALID_ARGUMENT);
        let mut name = null_mut();
        assert_eq!(bw_symbol_name(cx.0, x, &mut name), BW_OK);
        assert_eq!(take(name), "x");
        assert_eq!(bw_symbol_name(cx.0, k, &mut name), BW_ERR_INVALID_ARGUMENT);
        let mut f = 0;
        assert_eq!(bw_fresh_symbol(cx.0, 8, &mut f), BW_OK);
        assert_eq!(bw_symbol_name(cx.0, f, &mut name), BW_OK);
        assert!(take(name).starts_with('$'));
        assert_eq!(bw_symbol_u64(cx.0, 7, 8, &mut f), BW_OK);
        assert_eq!(bw_symbol_name(cx.0, f, &mut name), BW_OK);
        assert_eq!(take(name), "#7");
        let mut w = 0;
        assert_eq!(bw_width(cx.0, f, &mut w), BW_OK);
        assert_eq!(w, 8);
        // A negative constant fits signed.
        assert_eq!(bw_const_i64(cx.0, 16, -2, &mut e), BW_OK);
        assert_eq!(bw_const_value(cx.0, e, &mut v), BW_OK);
        assert_eq!(v.limbs[0], 0xfffe);
        assert_eq!(bw_const_i64(cx.0, 8, -129, &mut e), BW_ERR_VALUE);
        let mut size = 0;
        let sum = cx.parse("let t = x + 1; t * t", 16);
        assert_eq!(bw_dag_size(cx.0, sum, &mut size), BW_OK);
        assert_eq!(size, 4);
    }
}

#[test]
fn wide_values_round_trip() {
    let cx = Cx::new();
    let x = cx.sym("x", 200);
    let mut limbs = [0; 8];
    limbs[0] = u64::MAX;
    limbs[3] = 0xff; // bits 192..199
    let big = BwValue { width: 200, limbs };
    let mut k = 0;
    let mut out = val(1, 0);
    unsafe {
        assert_eq!(bw_const(cx.0, &big, &mut k), BW_OK);
        let mut e = 0;
        assert_eq!(bw_bin(cx.0, 11, x, k, &mut e), BW_OK); // xor
        assert_eq!(bw_eval(cx.0, e, &x, &big, 1, &mut out), BW_OK);
        assert_eq!(out.width, 200);
        assert!(out.limbs.iter().all(|&l| l == 0));
        // Bits above the width, or a limb past it, do not fit.
        let mut bad = big;
        bad.limbs[3] = 0x1ff;
        assert_eq!(bw_const(cx.0, &bad, &mut k), BW_ERR_VALUE);
        bad.limbs[3] = 0xff;
        bad.limbs[7] = 1;
        assert_eq!(bw_const(cx.0, &bad, &mut k), BW_ERR_VALUE);
        assert_eq!(bw_const(cx.0, &val(0, 0), &mut k), BW_ERR_WIDTH);
        assert_eq!(bw_const(cx.0, &val(513, 0), &mut k), BW_ERR_WIDTH);
    }
}

#[test]
fn eval_and_substitute() {
    let cx = Cx::new();
    let e = cx.parse("x * 3 + y", 8);
    let (x, y) = (cx.sym("x", 8), cx.sym("y", 8));
    let mut out = val(1, 0);
    unsafe {
        let vals = [val(8, 100), val(8, 1)];
        assert_eq!(
            bw_eval(cx.0, e, [x, y].as_ptr(), vals.as_ptr(), 2, &mut out),
            BW_OK
        );
        assert_eq!(out.limbs[0], (300 + 1) % 256);
        // A missing symbol, a value of the wrong width, a non-symbol key.
        assert_eq!(
            bw_eval(cx.0, e, &x, &val(8, 1), 1, &mut out),
            BW_ERR_UNBOUND_SYMBOL
        );
        assert!(last_error().contains('y'));
        let vals = [val(8, 1), val(16, 1)];
        assert_eq!(
            bw_eval(cx.0, e, [x, y].as_ptr(), vals.as_ptr(), 2, &mut out),
            BW_ERR_ENV_WIDTH
        );
        assert_eq!(
            bw_eval(cx.0, e, &e, &val(8, 1), 1, &mut out),
            BW_ERR_INVALID_ARGUMENT
        );
        // x -> y + 1, y -> 5, at once.
        let one = cx.konst(8, 1);
        let mut yp1 = 0;
        assert_eq!(bw_bin(cx.0, 0, y, one, &mut yp1), BW_OK);
        let five = cx.konst(8, 5);
        let mut s = 0;
        assert_eq!(
            bw_substitute(cx.0, e, [x, y].as_ptr(), [yp1, five].as_ptr(), 2, &mut s),
            BW_OK
        );
        assert_eq!(cx.print(s), "(y + 1) * 3 + 5");
        assert_eq!(
            bw_substitute(cx.0, e, [x, x].as_ptr(), [y, y].as_ptr(), 2, &mut s),
            BW_ERR_DUPLICATE_SUBSTITUTION
        );
    }
}

#[test]
fn errors_leave_outputs_alone_and_are_described() {
    let cx = Cx::new();
    let other = Cx::new();
    let x = cx.sym("x", 8);
    let mut e = 42;
    unsafe {
        // NULL arguments.
        assert_eq!(
            bw_symbol(null_mut(), cstr("x").as_ptr(), 8, &mut e),
            BW_ERR_INVALID_ARGUMENT
        );
        assert!(last_error().contains("cx"));
        assert_eq!(bw_symbol(cx.0, null(), 8, &mut e), BW_ERR_INVALID_ARGUMENT);
        assert_eq!(
            bw_symbol(cx.0, cstr("x").as_ptr(), 8, null_mut()),
            BW_ERR_INVALID_ARGUMENT
        );
        assert!(last_error().contains("out"));
        // Not UTF-8.
        let latin1 = CString::new(vec![0xe9u8]).unwrap();
        assert_eq!(
            bw_symbol(cx.0, latin1.as_ptr(), 8, &mut e),
            BW_ERR_INVALID_ARGUMENT
        );
        // Unknown enumeration values.
        assert_eq!(bw_un(cx.0, 7, x, &mut e), BW_ERR_INVALID_ARGUMENT);
        assert_eq!(bw_bin(cx.0, -1, x, x, &mut e), BW_ERR_INVALID_ARGUMENT);
        assert_eq!(bw_cmp(cx.0, 10, x, x, &mut e), BW_ERR_INVALID_ARGUMENT);
        assert!(bw_engine_new(2).is_null());
        assert!(last_error().contains("preset"));
        // Width rules.
        let y = cx.sym("y", 16);
        assert_eq!(bw_bin(cx.0, 0, x, y, &mut e), BW_ERR_WIDTH);
        assert_eq!(bw_zext(cx.0, y, 8, &mut e), BW_ERR_WIDTH);
        assert_eq!(bw_un(cx.0, 5, cx.sym("z", 12), &mut e), BW_ERR_WIDTH); // bswap
        assert_eq!(
            bw_symbol(cx.0, cstr("x").as_ptr(), 9, &mut e),
            BW_ERR_SYMBOL_WIDTH
        );
        // Handles: null, foreign, stale.
        assert_eq!(bw_un(cx.0, 0, 0, &mut e), BW_ERR_FOREIGN_EXPR);
        assert_eq!(bw_un(other.0, 0, x, &mut e), BW_ERR_FOREIGN_EXPR);
        assert_eq!(bw_un(cx.0, 0, x + 1_000_000, &mut e), BW_ERR_FOREIGN_EXPR);
        // Syntax.
        assert_eq!(
            bw_parse(cx.0, cstr("x +").as_ptr(), 8, &mut e),
            BW_ERR_SYNTAX
        );
        assert_eq!(
            bw_parse(cx.0, cstr("p + q").as_ptr(), 0, &mut e),
            BW_ERR_SYNTAX
        );
        assert_eq!(e, 42);
        bw_context_clear(cx.0);
        assert_eq!(bw_context_len(cx.0), 0);
        assert_eq!(bw_un(cx.0, 0, x, &mut e), BW_ERR_STALE_EXPR);
        assert_eq!(e, 42);
        // The free functions accept NULL.
        bw_context_free(null_mut());
        bw_engine_free(null_mut());
        bw_engine_builder_free(null_mut());
        bw_assumptions_free(null_mut());
        bw_smt_import_free(null_mut());
        bw_string_free(null_mut());
        assert_eq!(bw_context_len(null()), 0);
    }
}

#[test]
fn the_arena_limit_is_an_error() {
    let cx = bw_context_new_with(4, 0);
    let mut e = 0;
    unsafe {
        let st = bw_parse(cx, cstr("a + b + c + d").as_ptr(), 8, &mut e);
        assert_eq!(st, BW_ERR_ARENA_FULL);
        bw_context_free(cx);
    }
}

#[test]
fn facts_proofs_and_assumptions() {
    let cx = Cx::new();
    let x = cx.sym("x", 8);
    let g = cx.parse("(x & 0xf0) | 1", 8);
    let mut f = BwFacts {
        known_zero: val(1, 0),
        known_one: val(1, 0),
        umin: val(1, 0),
        umax: val(1, 0),
        ustride: 7,
        smin: val(1, 0),
        smax: val(1, 0),
        relies_on: 7,
    };
    let mut p = BwProof {
        truth: -1,
        relies_on: 7,
    };
    unsafe {
        assert_eq!(bw_facts_of(cx.0, g, null(), &mut f), BW_OK);
        assert_eq!(f.known_zero.limbs[0], 0x0e);
        assert_eq!(f.known_one.limbs[0], 0x01);
        assert_eq!((f.umin.limbs[0], f.umax.limbs[0], f.ustride), (1, 0xf1, 16));
        assert_eq!(f.relies_on, 0);

        let a = bw_assumptions_new();
        let lt = cx.parse("x <u 16", 8);
        let mut id = 99;
        assert_eq!(bw_assume(a, cx.0, lt, true, &mut id), BW_OK);
        assert_eq!(id, 0);
        let masked = cx.parse("x & 0xf0", 8);
        let zero = cx.konst(8, 0);
        assert_eq!(bw_prove_cmp(cx.0, 0, masked, zero, null(), &mut p), BW_OK);
        assert_eq!(p.truth, 2);
        assert_eq!(bw_prove_cmp(cx.0, 0, masked, zero, a, &mut p), BW_OK);
        assert_eq!((p.truth, p.relies_on), (1, 1));
        assert_eq!(bw_facts_of(cx.0, x, a, &mut f), BW_OK);
        assert_eq!((f.umax.limbs[0], f.relies_on), (15, 1));
        // A 1-bit predicate, proved true or false.
        let ge = cx.parse("x >=u 16", 8);
        assert_eq!(bw_prove(cx.0, ge, a, &mut p), BW_OK);
        assert_eq!(p.truth, 0);
        // Only 1-bit predicates can be assumed.
        assert_eq!(bw_assume(a, cx.0, x, true, null_mut()), BW_ERR_WIDTH);
        assert!(!bw_assumptions_infeasible(a));
        assert_eq!(bw_assume(a, cx.0, lt, false, null_mut()), BW_OK);
        assert!(bw_assumptions_infeasible(a));
        assert_eq!(bw_facts_of(cx.0, x, a, &mut f), BW_ERR_INFEASIBLE);
        // Assumptions belong to one context.
        let other = Cx::new();
        let y = other.sym("y", 1);
        assert_eq!(
            bw_assume(a, other.0, y, true, null_mut()),
            BW_ERR_FOREIGN_EXPR
        );
        bw_assumptions_free(a);

        // Invertibility: a keyed mixer is a bijection of x.
        let h = cx.parse("(x ^ 0x5a) * 0x1d", 8);
        assert_eq!(bw_prove_injective(cx.0, h, x, true, null(), &mut p), BW_OK);
        assert_eq!(p.truth, 1);
        let lossy = cx.parse("x & 0x0f", 8);
        assert_eq!(
            bw_prove_injective(cx.0, lossy, x, false, null(), &mut p),
            BW_OK
        );
        assert_ne!(p.truth, 1);
    }
}

#[test]
fn runs_with_budgets_and_assumptions() {
    let cx = Cx::new();
    let engine = bw_engine_new(PRESET_STANDARD);
    let roots = [
        cx.parse("(x & y) + (x | y)", 32),
        cx.parse("x & 0xffff0000", 32),
        cx.sym("x", 32),
    ];
    let a = bw_assumptions_new();
    let small = cx.parse("x <u 0x10000", 32);
    let mut outs = [BwOutcome {
        expr: 0,
        changed: false,
        end: -1,
        limit: -9,
        relies_on: 0,
    }; 3];
    unsafe {
        assert_eq!(bw_assume(a, cx.0, small, true, null_mut()), BW_OK);
        let b = bw_budget_default();
        assert_eq!(b.mba_calls, 1 << 12);
        assert_eq!(
            bw_engine_run(engine, cx.0, roots.as_ptr(), 3, &b, a, outs.as_mut_ptr()),
            BW_OK
        );
        assert_eq!(cx.print(outs[0].expr), "x + y");
        assert!(outs[0].changed && outs[0].end == 0 && outs[0].limit == -1);
        assert_eq!(outs[0].relies_on, 0);
        assert_eq!(cx.print(outs[1].expr), "0:32");
        assert_eq!(outs[1].relies_on, 1);
        assert!(!outs[2].changed);
        // No budget at all: stopped, and valid.
        let mut none = b;
        none.node_visits = 0;
        let fresh = cx.parse("(p & q) + (p | q)", 32);
        assert_eq!(
            bw_engine_run(engine, cx.0, &fresh, 1, &none, null(), outs.as_mut_ptr()),
            BW_OK
        );
        assert_eq!((outs[0].end, outs[0].limit), (1, 0));
        // Nothing to do.
        assert_eq!(
            bw_engine_run(engine, cx.0, null(), 0, null(), null(), null_mut()),
            BW_OK
        );
        assert_eq!(
            bw_engine_run(engine, cx.0, &fresh, 1, null(), null(), null_mut()),
            BW_ERR_INVALID_ARGUMENT
        );
        bw_assumptions_free(a);
        bw_engine_free(engine);
    }
}

const RULES: &str = "bitwright 1;
group my.rules {
    rule and_or_complement<W>(x: W, y: W) { (x | y) & (x | ~y) => x }
}";

#[test]
fn engines_with_rules_of_your_own() {
    let cx = Cx::new();
    let e = cx.parse("(a | b) & (a | ~b)", 64);
    let mut ledger = null_mut();
    let mut engine = null_mut();
    let mut s = 0;
    unsafe {
        assert_eq!(bw_check_rules(cstr(RULES).as_ptr(), &mut ledger), BW_OK);
        let ledger = take(ledger);
        // With the ledger, and checked on the spot.
        for l in [Some(ledger.as_str()), None] {
            let b = bw_engine_builder_new(PRESET_STANDARD);
            let l = l.map(cstr);
            let lp = l.as_ref().map_or(null(), |l| l.as_ptr());
            assert_eq!(
                bw_engine_builder_add_rules(b, cstr(RULES).as_ptr(), lp),
                BW_OK
            );
            bw_engine_builder_set_max_rounds(b, 2);
            assert_eq!(bw_engine_builder_build(b, &mut engine), BW_OK);
            assert_eq!(bw_simplify(engine, cx.0, e, &mut s), BW_OK);
            assert_eq!(cx.print(s), "a");
            bw_engine_free(engine);
            bw_engine_builder_free(b);
        }

        // A ledger for other rules does not vouch for these.
        let other = "bitwright 1;\ngroup g {\n    rule r<W>(x: W) { x ^ x => 0 }\n}";
        let mut other_ledger = null_mut();
        assert_eq!(
            bw_check_rules(cstr(other).as_ptr(), &mut other_ledger),
            BW_OK
        );
        let b = bw_engine_builder_new(PRESET_DEOBFUSCATE);
        assert_eq!(
            bw_engine_builder_add_rules(b, cstr(RULES).as_ptr(), other_ledger),
            BW_OK
        );
        bw_string_free(other_ledger);
        assert_eq!(bw_engine_builder_build(b, &mut engine), BW_ERR_RULES);
        bw_engine_builder_free(b);

        // Unsound rules, and rules that do not compile.
        let unsound = "bitwright 1;\ngroup g {\n    rule bad<W>(x: W, y: W) { x | y => x }\n}";
        assert_eq!(
            bw_check_rules(cstr(unsound).as_ptr(), &mut null_mut()),
            BW_ERR_RULES
        );
        assert!(last_error().contains("unsound"), "{}", last_error());
        let b = bw_engine_builder_new(PRESET_STANDARD);
        assert_eq!(
            bw_engine_builder_add_rules(b, cstr(unsound).as_ptr(), null()),
            BW_ERR_RULES
        );
        assert_eq!(
            bw_engine_builder_add_rules(b, cstr("nonsense").as_ptr(), null()),
            BW_ERR_RULES
        );
        assert_eq!(
            bw_engine_builder_add_rules(b, cstr(RULES).as_ptr(), cstr("junk").as_ptr()),
            BW_ERR_RULES
        );
        // A builder with only presets builds the shared preset engine.
        assert_eq!(bw_engine_builder_build(b, &mut engine), BW_OK);
        bw_engine_free(engine);
        bw_engine_builder_free(b);
    }
}

#[test]
fn smtlib_round_trip() {
    let cx = Cx::new();
    let e = cx.parse("udiv(x, y) + (x << 3)", 8);
    let mut s = null_mut();
    let mut imp = null_mut();
    unsafe {
        assert_eq!(bw_smtlib_export(cx.0, &e, 1, &mut s), BW_OK);
        let script = take(s);
        assert!(script.contains("(define-fun root0 () (_ BitVec 8)"));
        let other = Cx::new();
        let with_assert = format!("{script}(assert (= root0 #x00))\n");
        assert_eq!(
            bw_smtlib_import(other.0, cstr(&with_assert).as_ptr(), &mut imp),
            BW_OK
        );
        assert_eq!(bw_smt_import_count(imp, SMT_SYMBOLS), 2);
        assert_eq!(bw_smt_import_count(imp, SMT_ASSERTIONS), 1);
        assert_eq!(bw_smt_import_count(imp, 3), 0);
        let n = bw_smt_import_count(imp, SMT_DEFINITIONS);
        let mut found = None;
        for i in 0..n {
            let mut d = 0;
            let mut name = null();
            assert_eq!(
                bw_smt_import_get(imp, SMT_DEFINITIONS, i, &mut d, &mut name),
                BW_OK
            );
            if CStr::from_ptr(name).to_str().unwrap() == "root0" {
                found = Some(d);
            }
        }
        assert_eq!(other.print(found.unwrap()), cx.print(e));
        let mut a = 0;
        let mut name = c"x".as_ptr();
        assert_eq!(
            bw_smt_import_get(imp, SMT_ASSERTIONS, 0, &mut a, &mut name),
            BW_OK
        );
        assert!(name.is_null());
        assert_eq!(
            bw_smt_import_get(imp, SMT_ASSERTIONS, 1, &mut a, null_mut()),
            BW_ERR_INVALID_ARGUMENT
        );
        bw_smt_import_free(imp);
        assert_eq!(
            bw_smtlib_import(other.0, cstr("(assert").as_ptr(), &mut imp),
            BW_ERR_SYNTAX
        );
    }
}

#[test]
fn engines_are_shared_between_threads() {
    let engine = bw_engine_new(PRESET_STANDARD) as usize;
    let threads: Vec<_> = (0..4)
        .map(|i| {
            std::thread::spawn(move || {
                let cx = Cx::new();
                let e = cx.parse(&format!("(x & {i}) + (x | {i})"), 32);
                let mut s = 0;
                let st = unsafe { bw_simplify(engine as *const BwEngine, cx.0, e, &mut s) };
                assert_eq!(st, BW_OK);
                cx.print(s)
            })
        })
        .collect();
    for (i, t) in threads.into_iter().enumerate() {
        assert_eq!(t.join().unwrap(), format!("x + {i}").replace("x + 0", "x"));
    }
    unsafe { bw_engine_free(engine as *mut BwEngine) };
}

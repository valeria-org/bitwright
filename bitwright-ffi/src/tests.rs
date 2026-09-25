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
    let source = [include_str!("lib.rs"), include_str!("more.rs")].concat();
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
    // Every function the header declares (or calls) is exported, the inline helpers aside.
    let ident = |c: char| c.is_ascii_alphanumeric() || c == '_';
    for (at, _) in header.match_indices("bw_") {
        if header[..at].ends_with(ident) {
            continue;
        }
        let name: String = header[at..].chars().take_while(|&c| ident(c)).collect();
        let inline = name.starts_with("bw_value_") || name == "bw_fp_format_of";
        if header[at + name.len()..].starts_with('(') && !inline {
            assert!(
                exported.contains(&name.as_str()),
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
    for (i, rm) in ROUNDINGS.iter().enumerate() {
        assert_eq!(value_of(&format!("BW_{}", rm.name().to_uppercase())), i);
    }
    for (i, op) in FPOPS.iter().enumerate() {
        assert_eq!(value_of(&format!("BW_FP_{}", op.to_uppercase())), i);
    }
    for (i, op) in FPCMPS.iter().enumerate() {
        assert_eq!(value_of(&format!("BW_FPCMP_{op:?}").to_uppercase()), i);
    }
    // (The tests' codes are checked against their semantics in `floating_point_values`.)
    let tests = [
        "ISNAN",
        "ISINF",
        "ISZERO",
        "ISSUBNORMAL",
        "ISNORMAL",
        "ISNEG",
        "ISPOS",
    ];
    assert_eq!(tests.len(), FPTESTS.len());
    for (i, t) in tests.iter().enumerate() {
        assert_eq!(value_of(&format!("BW_FP_{t}")), i);
    }
    // The named formats.
    let named = FpFormat::NAMED.into_iter().chain([(FpFormat::X87, "x87")]);
    for (f, name) in named {
        let def = format!("#define BW_{} bw_fp_format_of(", name.to_uppercase());
        let at = header.find(&def).expect(&def) + def.len();
        let args: Vec<u32> = header[at..]
            .split(')')
            .next()
            .unwrap()
            .split(", ")
            .map(|n| n.parse().unwrap())
            .collect();
        assert_eq!(args, [f.eb(), f.sb()], "{name}");
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
        ("BW_KIND_FP", KIND_FP),
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
        // Each on its own, on threads: the same answers.
        for threads in [1, 4, 0] {
            assert_eq!(
                bw_engine_run_each(
                    engine,
                    cx.0,
                    roots.as_ptr(),
                    3,
                    threads,
                    &b,
                    a,
                    outs.as_mut_ptr()
                ),
                BW_OK
            );
            assert_eq!(cx.print(outs[0].expr), "x + y");
            assert_eq!(cx.print(outs[1].expr), "0:32");
            assert_eq!((outs[1].relies_on, outs[2].changed), (1, false));
        }
        // Nothing to do.
        assert_eq!(
            bw_engine_run(engine, cx.0, null(), 0, null(), null(), null_mut()),
            BW_OK
        );
        assert_eq!(
            bw_engine_run_each(engine, cx.0, null(), 0, 2, null(), null(), null_mut()),
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

// ----- floating point -------------------------------------------------------------------------

fn rm(m: RoundingMode) -> c_int {
    code_of(&ROUNDINGS, &m)
}

fn f32_value(v: f32) -> BwValue {
    val(32, u64::from(v.to_bits()))
}

fn f64_value(v: f64) -> BwValue {
    val(64, v.to_bits())
}

impl Cx {
    /// `bw_fp`, which must succeed.
    fn fp(&self, op: &str, rm: c_int, f: FpFormat, args: &[u64], to: FpFormat, w: u16) -> u64 {
        let mut e = 0;
        let (f, to) = (c_format(f), c_format(to));
        let code = code_of(&FPOPS, &op);
        let st = unsafe {
            bw_fp(
                self.0,
                code,
                rm,
                f,
                args.as_ptr(),
                args.len(),
                to,
                w,
                &mut e,
            )
        };
        assert_eq!(st, BW_OK, "fp.{op}: {}", last_error());
        e
    }

    fn eval(&self, e: u64, env: &[(u64, BwValue)]) -> BwValue {
        let (syms, vals): (Vec<u64>, Vec<BwValue>) = env.iter().copied().unzip();
        let mut out = val(1, 0);
        let st = unsafe { bw_eval(self.0, e, syms.as_ptr(), vals.as_ptr(), env.len(), &mut out) };
        assert_eq!(st, BW_OK, "{}", last_error());
        out
    }

    fn node(&self, e: u64) -> BwNode {
        let mut n = BwNode {
            kind: -9,
            op: -9,
            width: 0,
            lo: 9,
            n_children: 0,
            children: [0; 3],
        };
        assert_eq!(
            unsafe { bw_node_of(self.0, e, &mut n) },
            BW_OK,
            "{}",
            last_error()
        );
        n
    }

    fn fp_node(&self, e: u64) -> BwFpNode {
        let mut n = BwFpNode {
            op: -9,
            rm: -9,
            format: c_format(FpFormat::F256),
            to: c_format(FpFormat::F256),
            int_width: 9,
        };
        let st = unsafe { bw_fp_node_of(self.0, e, &mut n) };
        assert_eq!(st, BW_OK, "{}", last_error());
        n
    }
}

/// An operation, its mode, its format, its operands, and the text syntax of the node.
type FpCase<'a> = (&'a str, Option<RoundingMode>, FpFormat, &'a [u64], &'a str);

/// Every operation of `bw_fpop`, built with `bw_fp`: the node the text syntax gives, and
/// inspected back.
#[test]
fn floating_point_nodes() {
    use RoundingMode::*;
    let cx = Cx::new();
    let (a, b, c) = (cx.sym("a", 32), cx.sym("b", 32), cx.sym("c", 32));
    let (d, e) = (cx.sym("d", 64), cx.sym("e", 64));
    let (h, i) = (cx.sym("h", 16), cx.sym("i", 16));
    let (s, t, tiny) = (cx.sym("s", 7), cx.sym("t", 7), FpFormat::new(3, 4).unwrap());
    let (f16, bf16, f32, f64) = (FpFormat::F16, FpFormat::BF16, FpFormat::F32, FpFormat::F64);
    // Conversions to another format are to binary64 and to an integer to 32 bits; the other
    // operations ignore both.
    let (to, w) = (f64, 32);
    let cases: [FpCase; 18] = [
        ("add", Some(Rne), f32, &[a, b], "fp.add.rne.f32(a, b)"),
        ("mul", Some(Rtz), f32, &[a, b], "fp.mul.rtz.f32(a, b)"),
        ("div", Some(Rtp), f64, &[d, e], "fp.div.rtp.f64(d, e)"),
        ("fma", Some(Rtn), f32, &[a, b, c], "fp.fma.rtn.f32(a, b, c)"),
        ("sqrt", Some(Rna), f16, &[h], "fp.sqrt.rna.f16(h)"),
        ("rem", None, f64, &[d, e], "fp.rem.f64(d, e)"),
        ("round", Some(Rtz), bf16, &[h], "fp.round.rtz.bf16(h)"),
        ("min", None, f32, &[a, b], "fp.min.f32(a, b)"),
        ("max", None, f32, &[a, b], "fp.max.f32(a, b)"),
        ("eq", None, f32, &[a, b], "fp.eq.f32(a, b)"),
        ("lt", None, f32, &[a, b], "fp.lt.f32(a, b)"),
        ("le", None, f64, &[e, d], "fp.le.f64(e, d)"),
        ("convert", Some(Rne), f32, &[a], "fp.convert.rne.f32.f64(a)"),
        ("add", Some(Rna), tiny, &[s, t], "fp.add.rna<3, 4>(s, t)"),
        ("from_sbv", Some(Rne), f64, &[i], "fp.from_sbv.rne.f64(i)"),
        ("from_ubv", Some(Rtn), f16, &[a], "fp.from_ubv.rtn.f16(a)"),
        ("to_sbv", Some(Rtz), f64, &[d], "fp.to_sbv.rtz.f64<32>(d)"),
        ("to_ubv", Some(Rne), f32, &[a], "fp.to_ubv.rne.f32<32>(a)"),
    ];
    for (op, mode, format, args, text) in cases {
        // An operation without a rounding mode ignores the one given.
        let e = cx.fp(op, mode.map_or(99, rm), format, args, to, w);
        assert_eq!(cx.print(e), text);
        assert_eq!(e, cx.parse(text, 0), "{text}");
        let n = cx.node(e);
        let mut width = 0;
        assert_eq!(unsafe { bw_width(cx.0, e, &mut width) }, BW_OK);
        let code = code_of(&FPOPS, &op);
        assert_eq!((n.kind, n.op, n.width, n.lo), (KIND_FP, code, width, 0));
        assert_eq!(&n.children[..n.n_children as usize], args, "{text}");
        let f = cx.fp_node(e);
        assert_eq!(f.op, n.op);
        assert_eq!(f.rm, mode.map_or(-1, rm), "{text}");
        assert_eq!(f.format, c_format(format));
        let want = match op {
            "convert" => (c_format(to), 0),
            "to_sbv" | "to_ubv" => (NO_FORMAT, w),
            _ => (NO_FORMAT, 0),
        };
        assert_eq!((f.to, f.int_width), want, "{text}");
    }
    // The other builders make bit-vector operators, or nodes of `bw_fpop`.
    let (f, mut out) = (c_format(f32), 0);
    unsafe {
        assert_eq!(bw_fp_sub(cx.0, rm(Rtp), f, a, b, &mut out), BW_OK);
        assert_eq!(out, cx.parse("fp.sub.rtp.f32(a, b)", 0));
        assert!(cx.print(out).starts_with("fp.add.rtp.f32("));
        assert_eq!(bw_fp_neg(cx.0, f, a, &mut out), BW_OK);
        assert_eq!(cx.print(out), "a ^ 0x80000000");
        assert_eq!(cx.node(out).kind, KIND_BINARY);
        assert_eq!(bw_fp_abs(cx.0, f, a, &mut out), BW_OK);
        assert_eq!(cx.print(out), "a & 0x7fffffff");
        assert_eq!(bw_fp_copysign(cx.0, f, a, b, &mut out), BW_OK);
        assert_eq!(out, cx.parse("fp.copysign.f32(a, b)", 0));
        // `gt` and `ge` are `lt` and `le` swapped.
        for (op, text) in [
            (FpCmpOp::Eq, "fp.eq.f32(a, b)"),
            (FpCmpOp::Lt, "fp.lt.f32(a, b)"),
            (FpCmpOp::Le, "fp.le.f32(a, b)"),
            (FpCmpOp::Gt, "fp.lt.f32(b, a)"),
            (FpCmpOp::Ge, "fp.le.f32(b, a)"),
        ] {
            let code = code_of(&FPCMPS, &op);
            assert_eq!(bw_fp_cmp(cx.0, code, f, a, b, &mut out), BW_OK);
            assert_eq!(cx.print(out), text);
        }
        for (t, name) in FPTESTS.iter().zip([
            "isnan",
            "isinf",
            "iszero",
            "issubnormal",
            "isnormal",
            "isneg",
            "ispos",
        ]) {
            let code = code_of(&FPTESTS, t);
            assert_eq!(bw_fp_test(cx.0, code, f, a, &mut out), BW_OK);
            assert_eq!(out, cx.parse(&format!("fp.{name}.f32(a)"), 0), "{name}");
            assert_eq!(cx.node(out).kind, KIND_COMPARE);
        }
        let x = cx.sym("x", 80);
        assert_eq!(bw_x87_load(cx.0, x, &mut out), BW_OK);
        assert_eq!(out, cx.parse("fp.x87_load(x)", 0));
        let v = cx.sym("v", 79);
        assert_eq!(bw_x87_store(cx.0, v, &mut out), BW_OK);
        assert_eq!(out, cx.parse("fp.x87_store(v)", 0));
        // Only floating-point nodes have a `bw_fp_node`.
        let mut n = cx.fp_node(cx.fp("add", 0, f32, &[a, b], f32, 0));
        assert_eq!(bw_fp_node_of(cx.0, a, &mut n), BW_ERR_INVALID_ARGUMENT);
        assert!(last_error().contains("floating-point"), "{}", last_error());
        assert_eq!(n.op, 0);
    }
}

/// Values: the semantics of bitwright's book, through `bw_eval` and folding.
#[test]
fn floating_point_values() {
    use RoundingMode::*;
    let cx = Cx::new();
    let (a, b) = (cx.sym("a", 32), cx.sym("b", 32));
    let f32 = FpFormat::F32;
    // 0.1 + 0.2 in binary32: the exact sum is 3/4 of the way to the next value up, so to nearest
    // it rounds up (to 0.3f), toward zero one unit in the last place lower.
    let env = [(a, f32_value(0.1)), (b, f32_value(0.2))];
    let near = cx.fp("add", rm(Rne), f32, &[a, b], f32, 0);
    let down = cx.fp("add", rm(Rtz), f32, &[a, b], f32, 0);
    let sum = 0.1f32 + 0.2f32;
    assert_eq!(cx.eval(near, &env).limbs[0], u64::from(sum.to_bits()));
    assert_eq!(sum, 0.3f32);
    assert_eq!(cx.eval(down, &env).limbs[0], u64::from(sum.to_bits() - 1));
    // Operations on constants fold, exactly.
    let tenth = cx.konst(32, u64::from(0.1f32.to_bits()));
    let fifth = cx.fp("add", rm(Rne), f32, &[tenth, tenth], f32, 0);
    let mut v = val(1, 0);
    unsafe {
        assert_eq!(bw_const_value(cx.0, fifth, &mut v), BW_OK);
    }
    assert_eq!(v.limbs[0], u64::from(0.2f32.to_bits()));
    // A NaN result is the canonical one; the comparisons are false on it.
    let d = cx.sym("d", 64);
    let root = cx.fp("sqrt", rm(Rne), FpFormat::F64, &[d], f32, 0);
    let nan = cx.eval(root, &[(d, f64_value(-1.0))]);
    assert_eq!(nan.limbs[0], 0x7ff8_0000_0000_0000);
    let eq = cx.fp("eq", 0, FpFormat::F64, &[d, root], f32, 0);
    assert_eq!(cx.eval(eq, &[(d, f64_value(-1.0))]).limbs[0], 0);
    // Conversions to integers saturate, and a NaN converts to 0.
    let to_i32 = cx.fp("to_sbv", rm(Rtz), FpFormat::F64, &[d], f32, 32);
    assert_eq!(
        cx.eval(to_i32, &[(d, f64_value(1e10))]).limbs[0],
        0x7fff_ffff
    );
    assert_eq!(
        cx.eval(to_i32, &[(d, f64_value(-2.9))]).limbs[0],
        0xffff_fffe
    );
    assert_eq!(cx.eval(to_i32, &[(d, f64_value(f64::NAN))]).limbs[0], 0);
    // binary16 has 11 bits of precision: 2049 rounds to 2048 or 2050.
    let i = cx.sym("i", 16);
    let half = |m| cx.fp("from_ubv", rm(m), FpFormat::F16, &[i], f32, 0);
    let at = |e| cx.eval(e, &[(i, val(16, 2049))]).limbs[0];
    assert_eq!(at(half(Rne)), 0x6800); // 2048
    assert_eq!(at(half(Rtp)), 0x6801); // 2050
    // Each test on sample values, against the library's value-level tests.
    let samples = [
        0.0f32,
        -0.0,
        1.5,
        -2.0,
        f32::MIN_POSITIVE / 4.0,
        -f32::MIN_POSITIVE / 2.0,
        f32::INFINITY,
        f32::NEG_INFINITY,
        f32::NAN,
        -f32::NAN,
    ];
    for (code, &t) in FPTESTS.iter().enumerate() {
        let mut e = 0;
        let st = unsafe { bw_fp_test(cx.0, code as c_int, c_format(f32), a, &mut e) };
        assert_eq!(st, BW_OK);
        for x in samples {
            let want = f32.test(t, &BitVec::from_f32(x)).unwrap();
            let got = cx.eval(e, &[(a, f32_value(x))]).limbs[0];
            assert_eq!(got, u64::from(want), "{t:?} of {x}");
        }
    }
    // x87: a store and a load give the value back; an unnormal loads as the NaN.
    let x = cx.sym("x", 80);
    let (mut load, mut store) = (0, 0);
    unsafe {
        assert_eq!(bw_x87_load(cx.0, x, &mut load), BW_OK);
        assert_eq!(bw_x87_store(cx.0, load, &mut store), BW_OK);
    }
    let one = {
        let mut limbs = [0; 8];
        limbs[0] = 1 << 63; // the integer bit
        limbs[1] = 0x3fff; // the biased exponent of 1.0
        BwValue { width: 80, limbs }
    };
    let back = cx.eval(store, &[(x, one)]);
    assert_eq!((back.width, back.limbs), (80, one.limbs));
    let mut unnormal = one;
    unnormal.limbs[0] = 0;
    let nan = FpFormat::X87.nan();
    assert_eq!(&cx.eval(load, &[(x, unnormal)]).limbs[..2], nan.limbs());
}

/// Facts, proofs and simplification see through floating-point operations.
#[test]
fn floating_point_facts_and_proofs() {
    use RoundingMode::*;
    let cx = Cx::new();
    let f64 = FpFormat::F64;
    let (i, j, b) = (cx.sym("i", 16), cx.sym("j", 16), cx.sym("b", 8));
    let fi = cx.fp("from_sbv", rm(Rne), f64, &[i], f64, 0);
    let fj = cx.fp("from_sbv", rm(Rne), f64, &[j], f64, 0);
    let product = cx.fp("mul", rm(Rne), f64, &[fi, fj], f64, 0);
    let mut isnan = 0;
    let mut p = BwProof {
        truth: -1,
        relies_on: 7,
    };
    unsafe {
        assert_eq!(
            bw_fp_test(cx.0, 0, c_format(f64), product, &mut isnan),
            BW_OK
        );
        // An integer converted to a float is never a NaN, nor a product of two of them.
        assert_eq!(bw_prove(cx.0, isnan, null(), &mut p), BW_OK);
        assert_eq!((p.truth, p.relies_on), (0, 0));
        let engine = bw_engine_new(PRESET_STANDARD);
        let mut s = 0;
        assert_eq!(bw_simplify(engine, cx.0, isnan, &mut s), BW_OK);
        assert_eq!(cx.print(s), "0:1");
        bw_engine_free(engine);
    }
    // A byte converted to a float, and back to 16 bits, is below 256.
    let fb = cx.fp("from_ubv", rm(Rne), f64, &[b], f64, 0);
    let back = cx.fp("to_ubv", rm(Rtz), f64, &[fb], f64, 16);
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
    unsafe {
        assert_eq!(bw_facts_of(cx.0, back, null(), &mut f), BW_OK);
    }
    assert_eq!(f.umax.width, 16);
    assert!(f.umax.limbs[0] < 256, "{:#x}", f.umax.limbs[0]);
    // SMT-LIB: exported to the FloatingPoint theory, and read back.
    let (p, q) = (cx.sym("p", 32), cx.sym("q", 32));
    let sum = cx.fp("add", rm(Rtz), FpFormat::F32, &[p, q], f64, 0);
    let mut s = null_mut();
    let mut imp = null_mut();
    let other = Cx::new();
    unsafe {
        assert_eq!(bw_smtlib_export(cx.0, &sum, 1, &mut s), BW_OK);
        let script = take(s);
        assert!(script.contains("(fp.add RTZ ((_ to_fp 8 24)"), "{script}");
        let st = bw_smtlib_import(other.0, cstr(&script).as_ptr(), &mut imp);
        assert_eq!(st, BW_OK, "{}", last_error());
        let n = bw_smt_import_count(imp, SMT_DEFINITIONS);
        let root = (0..n).find_map(|i| {
            let (mut d, mut name) = (0, null());
            assert_eq!(
                bw_smt_import_get(imp, SMT_DEFINITIONS, i, &mut d, &mut name),
                BW_OK
            );
            (CStr::from_ptr(name).to_str().unwrap() == "root0").then_some(d)
        });
        assert_eq!(other.print(root.unwrap()), "fp.add.rtz.f32(p, q)");
        bw_smt_import_free(imp);
    }
}

#[test]
fn floating_point_errors() {
    let cx = Cx::new();
    let (a, b, h) = (cx.sym("a", 32), cx.sym("b", 32), cx.sym("h", 16));
    let f32 = c_format(FpFormat::F32);
    let add = code_of(&FPOPS, &"add");
    let mut e = 42;
    unsafe {
        let fp = |op, rm, f, args: &[u64], to, w, out: &mut u64| {
            bw_fp(cx.0, op, rm, f, args.as_ptr(), args.len(), to, w, out)
        };
        // Formats outside 2 <= eb <= 31, sb >= 2, eb + sb <= 512.
        for (eb, sb) in [(1, 8), (32, 8), (8, 1), (11, 502), (0, 0), (8, u32::MAX)] {
            let bad = BwFpFormat { eb, sb };
            assert_eq!(fp(add, 0, bad, &[a, b], f32, 0, &mut e), BW_ERR_WIDTH);
            assert!(
                last_error().contains("floating-point format"),
                "{}",
                last_error()
            );
            assert_eq!(bw_fp_neg(cx.0, bad, a, &mut e), BW_ERR_WIDTH);
            assert_eq!(bw_fp_test(cx.0, 0, bad, a, &mut e), BW_ERR_WIDTH);
            // `to` is read by conversions only.
            let convert = code_of(&FPOPS, &"convert");
            assert_eq!(fp(convert, 0, f32, &[a], bad, 0, &mut e), BW_ERR_WIDTH);
        }
        assert_eq!(e, 42);
        // Operands of another width.
        assert_eq!(fp(add, 0, f32, &[a, h], f32, 0, &mut e), BW_ERR_WIDTH);
        assert!(last_error().contains("widths differ"), "{}", last_error());
        let f64 = c_format(FpFormat::F64);
        assert_eq!(fp(add, 0, f64, &[a, b], f32, 0, &mut e), BW_ERR_WIDTH);
        assert_eq!(bw_fp_sub(cx.0, 0, f32, a, h, &mut e), BW_ERR_WIDTH);
        assert_eq!(bw_fp_neg(cx.0, f32, h, &mut e), BW_ERR_WIDTH);
        assert_eq!(bw_fp_abs(cx.0, f32, h, &mut e), BW_ERR_WIDTH);
        assert_eq!(bw_fp_copysign(cx.0, f32, a, h, &mut e), BW_ERR_WIDTH);
        assert_eq!(bw_fp_cmp(cx.0, 0, f32, a, h, &mut e), BW_ERR_WIDTH);
        assert_eq!(bw_fp_test(cx.0, 0, f32, h, &mut e), BW_ERR_WIDTH);
        assert_eq!(bw_x87_load(cx.0, a, &mut e), BW_ERR_WIDTH);
        assert_eq!(bw_x87_store(cx.0, a, &mut e), BW_ERR_WIDTH);
        // Integer widths outside 1..=512.
        let to_sbv = code_of(&FPOPS, &"to_sbv");
        assert_eq!(fp(to_sbv, 0, f32, &[a], f32, 0, &mut e), BW_ERR_WIDTH);
        assert_eq!(fp(to_sbv, 0, f32, &[a], f32, 513, &mut e), BW_ERR_WIDTH);
        // The number of operands.
        assert_eq!(
            fp(add, 0, f32, &[a], f32, 0, &mut e),
            BW_ERR_INVALID_ARGUMENT
        );
        assert!(
            last_error().contains("takes 2 operands"),
            "{}",
            last_error()
        );
        let fma = code_of(&FPOPS, &"fma");
        assert_eq!(
            fp(fma, 0, f32, &[a, b], f32, 0, &mut e),
            BW_ERR_INVALID_ARGUMENT
        );
        assert_eq!(
            bw_fp(cx.0, add, 0, f32, null(), 2, f32, 0, &mut e),
            BW_ERR_INVALID_ARGUMENT
        );
        // Unknown codes: the operation, a rounding mode (read only where there is one), the
        // comparison, the test.
        assert_eq!(
            fp(17, 0, f32, &[a, b], f32, 0, &mut e),
            BW_ERR_INVALID_ARGUMENT
        );
        assert_eq!(
            fp(-1, 0, f32, &[a, b], f32, 0, &mut e),
            BW_ERR_INVALID_ARGUMENT
        );
        assert_eq!(
            fp(add, 5, f32, &[a, b], f32, 0, &mut e),
            BW_ERR_INVALID_ARGUMENT
        );
        assert!(last_error().contains("rounding mode"), "{}", last_error());
        assert_eq!(
            bw_fp_sub(cx.0, -1, f32, a, b, &mut e),
            BW_ERR_INVALID_ARGUMENT
        );
        assert_eq!(
            bw_fp_cmp(cx.0, 5, f32, a, b, &mut e),
            BW_ERR_INVALID_ARGUMENT
        );
        assert_eq!(bw_fp_test(cx.0, 7, f32, a, &mut e), BW_ERR_INVALID_ARGUMENT);
        assert_eq!(e, 42);
        let rem = code_of(&FPOPS, &"rem");
        assert_eq!(fp(rem, -7, f32, &[a, b], f32, 0, &mut e), BW_OK);
        // NULL pointers, foreign handles.
        assert_eq!(
            bw_fp_neg(null_mut(), f32, a, &mut e),
            BW_ERR_INVALID_ARGUMENT
        );
        assert_eq!(bw_fp_neg(cx.0, f32, a, null_mut()), BW_ERR_INVALID_ARGUMENT);
        let other = Cx::new();
        assert_eq!(bw_fp_abs(other.0, f32, a, &mut e), BW_ERR_FOREIGN_EXPR);
        assert_eq!(bw_fp_node_of(cx.0, e, null_mut()), BW_ERR_INVALID_ARGUMENT);
        let mut n = other.fp_node(other.parse("fp.max.f32(p, q)", 32));
        assert_eq!(bw_fp_node_of(cx.0, 0, &mut n), BW_ERR_FOREIGN_EXPR);
    }
}

#[test]
fn proofs_synthesis_memory_lifting_and_transformations() {
    use super::more::*;
    let cx = Cx::new();
    // Equivalence and synthesis.
    let (a, b) = (cx.parse("(x ^ y) + 2 * (x & y)", 32), cx.parse("x + y", 32));
    let mut v = 7;
    assert_eq!(unsafe { bw_equivalent(cx.0, a, b, 100_000, &mut v) }, BW_OK);
    assert_eq!(v, 1);
    let c = cx.parse("x | y", 32);
    assert_eq!(unsafe { bw_equivalent(cx.0, b, c, 100_000, &mut v) }, BW_OK);
    assert_eq!(v, 0);
    let e = cx.parse("((x + y) & 1) ^ (x & 1)", 32);
    let (mut s, mut found) = (0, false);
    assert_eq!(
        unsafe { bw_synthesize(cx.0, e, 7, &mut s, &mut found) },
        BW_OK
    );
    assert!(found);
    assert_eq!(cx.print(s), "y & 1");
    // Memory.
    let m = unsafe { bw_memory_new(cstr("mem").as_ptr(), 64, 8, false) };
    assert!(!m.is_null());
    let (slot, x) = (cx.parse("sp - 8", 64), cx.sym("v", 64));
    assert_eq!(unsafe { bw_memory_store(m, cx.0, slot, x) }, BW_OK);
    let mut back = 0;
    assert_eq!(
        unsafe { bw_memory_load(m, cx.0, slot, 8, &mut back) },
        BW_OK
    );
    assert_eq!(back, x);
    unsafe { bw_memory_free(m) };
    // Lifting.
    let mut l = null_mut();
    let code = cstr("t0 = GET:I64(rdi)\nt1 = Add64(t0,t0)\nPUT(rax) = t1");
    assert_eq!(
        unsafe { bw_lift(cx.0, 1, code.as_ptr(), null(), &mut l) },
        BW_OK
    );
    assert_eq!(unsafe { bw_lifted_count(l, 1) }, 1);
    let (mut name, mut out) = (null(), 0u64);
    assert_eq!(
        unsafe { bw_lifted_get(l, 1, 0, &mut name, &mut out, null_mut()) },
        BW_OK
    );
    assert_eq!(unsafe { CStr::from_ptr(name) }.to_str().unwrap(), "rax");
    assert_eq!(cx.print(out), "rdi + rdi");
    assert_ne!(
        unsafe { bw_lifted_get(l, 1, 5, null_mut(), null_mut(), null_mut()) },
        BW_OK
    );
    unsafe { bw_lifted_free(l) };
    // Transformations.
    let (mut report, mut counts) = (null_mut(), BwTransformCounts::default());
    let t = cstr("%r = select %c, %x, false\n=>\n%r = and %c, %x");
    assert_eq!(
        unsafe { bw_transform_verify(t.as_ptr(), 0, &mut report, &mut counts) },
        BW_OK
    );
    let text = take(report);
    assert!(text.starts_with("INVALID"), "{text}");
    assert_eq!((counts.valid, counts.invalid, counts.undecided), (0, 1, 0));
    let pair = cstr(
        "define i8 @src(i8 %x) {\n  %r = mul i8 %x, 2\n  ret i8 %r\n}\n\
         define i8 @tgt(i8 %x) {\n  %r = add i8 %x, %x\n  ret i8 %r\n}\n",
    );
    assert_eq!(
        unsafe { bw_transform_validate(pair.as_ptr(), null(), 0, &mut report, &mut counts) },
        BW_OK
    );
    take(report);
    assert_eq!(counts.valid, 1);
    let i = cstr("%r = mul %x, C\n=>\n%r = shl %x, log2(C)");
    assert_eq!(
        unsafe { bw_transform_infer(i.as_ptr(), &mut report) },
        BW_OK
    );
    assert_eq!(take(report), "transformation 1\tisPowerOf2(C)\tvalid\n");
    // A syntax error.
    let bad = cstr("%r = frob %x\n=>\n%r = %x");
    assert_eq!(
        unsafe { bw_transform_verify(bad.as_ptr(), 0, &mut report, &mut counts) },
        BW_ERR_SYNTAX
    );
    // Engines that refuse a pass.
    let bld = bw_engine_builder_new(0);
    assert_eq!(
        unsafe { bw_engine_builder_refuse(bld, cstr("linear").as_ptr()) },
        BW_OK
    );
    unsafe { bw_engine_builder_set_float_values(bld, true) };
    let mut eng = null_mut();
    assert_eq!(unsafe { bw_engine_builder_build(bld, &mut eng) }, BW_OK);
    let sum = cx.parse("x * 3 - x - x", 8);
    let mut r = 0;
    assert_eq!(unsafe { bw_simplify(eng, cx.0, sum, &mut r) }, BW_OK);
    let mut same = 7;
    assert_eq!(
        unsafe { bw_equivalent(cx.0, r, sum, 100_000, &mut same) },
        BW_OK
    );
    assert_eq!(same, 1);
    unsafe {
        bw_engine_free(eng);
        bw_engine_builder_free(bld);
    }
}

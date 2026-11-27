//! Integration tests for `Memory::merge`, `Memory::memset`, and `Memory::memcpy`.

use bitwright::engine::Engine;
use bitwright::memory::{Endian, Memory};
use bitwright::{BinOp, BitVec, CmpOpExt, Context, Error, ParseOptions, SymbolKey, Width};

fn simplify_str(cx: &mut Context, e: bitwright::Expr) -> String {
    let out = Engine::standard().simplify(cx, e).unwrap();
    cx.display(out.expr).to_string()
}

#[test]
fn diamond_stack_spill_merges_without_spurious_base_reads() {
    for endian in [Endian::Little, Endian::Big] {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let mut mem = Memory::new("mem", Width::W64, Width::W8, endian);

        let sp_slot = cx.parse("sp - 16", &o).unwrap();
        let sp_slot_alt = cx.parse("(sp - 24) + 8", &o).unwrap();
        let other_slot = cx.parse("sp - 8", &o).unwrap();
        let x = cx.parse("x", &o).unwrap();
        let y = cx.parse("y", &o).unwrap();
        let z = cx.parse("z", &o).unwrap();
        let cond = cx.symbol("cond", Width::W1).unwrap();

        // Shared prefix before diverging: write `z` at `[sp - 8]`.
        let lca = mem.store(&mut cx, mem.initial(), other_slot, z).unwrap();

        // Both arms overwrite `[sp - 16]` (written in equivalent normalized forms).
        let v_then = mem.store(&mut cx, lca, sp_slot, x).unwrap();
        let v_else = mem.store(&mut cx, lca, sp_slot_alt, y).unwrap();

        let v_join = mem.merge(&mut cx, cond, v_then, v_else).unwrap();
        assert!(
            mem.reads().is_empty(),
            "same-slot diamond spill must not allocate dead base symbols"
        );

        let reloaded = mem.load(&mut cx, v_join, sp_slot, 8).unwrap();
        assert!(mem.reads().is_empty());

        let simplified = Engine::standard().simplify(&mut cx, reloaded).unwrap().expr;
        let expected = cx.select(cond, x, y).unwrap();
        assert_eq!(simplified, expected);

        // Shared prefix cell `[sp - 8]` remains `z` untouched across the merge.
        assert_eq!(mem.load(&mut cx, v_join, other_slot, 8).unwrap(), z);
        assert!(mem.reads().is_empty());
    }
}

#[test]
fn merge_deduplicates_within_branch_and_handles_intervening_symbolic_aliases() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W32);
    let mut mem = Memory::new("mem", Width::W32, Width::W8, Endian::Little);

    let slot = cx.parse("sp - 4", &o).unwrap();
    let ptr = cx.parse("p", &o).unwrap();
    let cond = cx.symbol("cond", Width::W1).unwrap();

    let a8 = cx.symbol("a", Width::W8).unwrap();
    let b8 = cx.symbol("b", Width::W8).unwrap();
    let c8 = cx.symbol("c", Width::W8).unwrap();
    let d8 = cx.symbol("d", Width::W8).unwrap();

    // `then` writes `a` to `slot`, writes `b` to `ptr`, then overwrites `slot` with `c`.
    // The earlier store `(slot, a)` is overshadowed even with `(ptr, b)` in between.
    let vt1 = mem.store(&mut cx, mem.initial(), slot, a8).unwrap();
    let vt2 = mem.store(&mut cx, vt1, ptr, b8).unwrap();
    let vt3 = mem.store(&mut cx, vt2, slot, c8).unwrap();

    // `else` writes `d` to `slot`, then `a` to `ptr` (potentially aliasing `slot`).
    let ve1 = mem.store(&mut cx, mem.initial(), slot, d8).unwrap();
    let ve2 = mem.store(&mut cx, ve1, ptr, a8).unwrap();

    let vm = mem.merge(&mut cx, cond, vt3, ve2).unwrap();
    let read_slot = mem.load(&mut cx, vm, slot, 1).unwrap();
    let read_ptr = mem.load(&mut cx, vm, ptr, 1).unwrap();

    // `slot` was unconditionally written on both sides, so reading `slot` never needs a base
    // read at `slot` (only `ptr` needed a base read because `then` wrote `ptr` before `slot`
    // while `else` also wrote `ptr`, wait: both wrote `ptr` too!).
    assert!(
        mem.reads().is_empty(),
        "both `slot` and `ptr` are written on both sides, so zero unknown base reads are needed: {:?}",
        mem.reads()
    );

    for sp_val in [0x100u64, 0x200] {
        for p_val in [sp_val.wrapping_sub(4), sp_val, 0x300] {
            for c_val in [0u64, 1] {
                let env = [
                    (
                        SymbolKey::from("sp"),
                        BitVec::wrapping_from_u64(Width::W32, sp_val),
                    ),
                    (
                        SymbolKey::from("p"),
                        BitVec::wrapping_from_u64(Width::W32, p_val),
                    ),
                    (
                        SymbolKey::from("cond"),
                        BitVec::wrapping_from_u64(Width::W1, c_val),
                    ),
                    (
                        SymbolKey::from("a"),
                        BitVec::wrapping_from_u64(Width::W8, 11),
                    ),
                    (
                        SymbolKey::from("b"),
                        BitVec::wrapping_from_u64(Width::W8, 22),
                    ),
                    (
                        SymbolKey::from("c"),
                        BitVec::wrapping_from_u64(Width::W8, 33),
                    ),
                    (
                        SymbolKey::from("d"),
                        BitVec::wrapping_from_u64(Width::W8, 44),
                    ),
                ];
                let vals = cx.eval(&[read_slot, read_ptr], &env[..]).unwrap();
                let slot_addr = sp_val.wrapping_sub(4);
                let (want_slot, want_ptr) = if c_val != 0 {
                    // then: [slot := 11], [p := 22], [slot := 33]
                    let at_p = if p_val == slot_addr { 33 } else { 22 };
                    (33, at_p)
                } else {
                    // else: [slot := 44], [p := 11]
                    let at_s = if p_val == slot_addr { 11 } else { 44 };
                    (at_s, 11)
                };
                assert_eq!(vals[0].to_u64(), Some(want_slot));
                assert_eq!(vals[1].to_u64(), Some(want_ptr));
            }
        }
    }
}

#[test]
fn merge_exhaustive_3bit_address_space_and_multiway_joins() {
    let mut cx = Context::new();
    let aw = Width::new(3).unwrap();
    let w2 = Width::new(2).unwrap();
    let cw = Width::W8;

    let k0 = cx.constant_u64(aw, 0).unwrap();
    let k1 = cx.constant_u64(aw, 1).unwrap();
    let k4 = cx.constant_u64(aw, 4).unwrap();
    let p = cx.symbol("p", aw).unwrap();
    let q = cx.symbol("q", aw).unwrap();
    let r = cx.symbol("r", aw).unwrap();
    let p1 = cx.add(p, k1).unwrap();
    let q_xor_4 = cx.bin(BinOp::Xor, q, k4).unwrap();

    let sel = cx.symbol("sel", w2).unwrap();
    let zero2 = cx.zero(w2).unwrap();
    let one2 = cx.one(w2).unwrap();
    let two2 = cx.constant_u64(w2, 2).unwrap();
    let is0 = cx.cmp(CmpOpExt::Eq, sel, zero2).unwrap();
    let is1 = cx.cmp(CmpOpExt::Eq, sel, one2).unwrap();
    let is2 = cx.cmp(CmpOpExt::Eq, sel, two2).unwrap();

    let v0_sym = cx.symbol("v0", cw).unwrap();
    let v1_sym = cx.symbol("v1", cw).unwrap();
    let v2_sym = cx.symbol("v2", cw).unwrap();
    let v3_sym = cx.symbol("v3", cw).unwrap();
    let pre_sym = cx.symbol("vpre", cw).unwrap();

    // Known region at [4..6) plus unknown cells elsewhere.
    let mut mem = Memory::new("m", aw, cw, Endian::Little)
        .with_bytes(4, &[0xde, 0xad])
        .unwrap();

    // Shared prefix on LCA.
    let lca = mem.store(&mut cx, mem.initial(), k0, pre_sym).unwrap();

    // Four switch-like arms branching from `lca` and cascading merges:
    // arm 0: [p := v0], [p + 1 := v1]
    let a0 = mem.store(&mut cx, lca, p, v0_sym).unwrap();
    let a0 = mem.store(&mut cx, a0, p1, v1_sym).unwrap();
    // arm 1: [q := v1], [p := v2]
    let a1 = mem.store(&mut cx, lca, q, v1_sym).unwrap();
    let a1 = mem.store(&mut cx, a1, p, v2_sym).unwrap();
    // arm 2: [q ^ 4 := v3]
    let a2 = mem.store(&mut cx, lca, q_xor_4, v3_sym).unwrap();
    // arm 3 (default): no stores (stays at `lca`)
    let a3 = lca;

    let m23 = mem.merge(&mut cx, is2, a2, a3).unwrap();
    let m123 = mem.merge(&mut cx, is1, a1, m23).unwrap();
    let m_all = mem.merge(&mut cx, is0, a0, m123).unwrap();

    let l0 = mem.load(&mut cx, a0, r, 1).unwrap();
    let l1 = mem.load(&mut cx, a1, r, 1).unwrap();
    let l2 = mem.load(&mut cx, a2, r, 1).unwrap();
    let l3 = mem.load(&mut cx, a3, r, 1).unwrap();
    let lm = mem.load(&mut cx, m_all, r, 1).unwrap();

    let image = |addr: &BitVec| {
        Some(BitVec::wrapping_from_u64(
            cw,
            addr.to_u64().unwrap().wrapping_mul(29).wrapping_add(7),
        ))
    };

    for pv in 0..8u64 {
        for qv in 0..8u64 {
            for rv in 0..8u64 {
                for sv in 0..4u64 {
                    let base_env = [
                        (SymbolKey::from("p"), BitVec::wrapping_from_u64(aw, pv)),
                        (SymbolKey::from("q"), BitVec::wrapping_from_u64(aw, qv)),
                        (SymbolKey::from("r"), BitVec::wrapping_from_u64(aw, rv)),
                        (SymbolKey::from("sel"), BitVec::wrapping_from_u64(w2, sv)),
                        (SymbolKey::from("v0"), BitVec::wrapping_from_u64(cw, 0x11)),
                        (SymbolKey::from("v1"), BitVec::wrapping_from_u64(cw, 0x22)),
                        (SymbolKey::from("v2"), BitVec::wrapping_from_u64(cw, 0x33)),
                        (SymbolKey::from("v3"), BitVec::wrapping_from_u64(cw, 0x44)),
                        (SymbolKey::from("vpre"), BitVec::wrapping_from_u64(cw, 0x99)),
                    ];
                    let env = mem.bind(&mut cx, &base_env, &image).unwrap();
                    let out = cx.eval(&[l0, l1, l2, l3, lm], &env[..]).unwrap();
                    let want = out[sv as usize];
                    assert_eq!(out[4], want, "p={pv} q={qv} r={rv} sel={sv}");
                }
            }
        }
    }
}

#[test]
fn memset_and_memcpy_simplify_through_engine() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    let mut mem = Memory::new("mem", Width::W64, Width::W8, Endian::Little);

    let buf = cx.parse("sp - 32", &o).unwrap();
    let dst = cx.parse("sp - 16", &o).unwrap();
    let zero_byte = cx.zero(Width::W8).unwrap();
    let x64 = cx.parse("x", &o).unwrap();

    // Clear 16 bytes at `sp - 32`, write `x` into `[sp - 28 .. sp - 20)`, copy 16 bytes to
    // `sp - 16`, and verify slices simplify cleanly.
    let v1 = mem
        .memset(&mut cx, mem.initial(), buf, zero_byte, 16)
        .unwrap();
    let buf_plus_4 = cx.parse("sp - 28", &o).unwrap();
    let v2 = mem.store(&mut cx, v1, buf_plus_4, x64).unwrap();
    let v3 = mem.memcpy(&mut cx, v2, dst, buf, 16).unwrap();
    assert!(mem.reads().is_empty());

    let dst_lo4 = mem.load(&mut cx, v3, dst, 4).unwrap();
    assert_eq!(simplify_str(&mut cx, dst_lo4), "0:32");

    let dst_mid8 = cx.parse("sp - 12", &o).unwrap();
    assert_eq!(mem.load(&mut cx, v3, dst_mid8, 8).unwrap(), x64);

    let dst_hi4 = cx.parse("sp - 4", &o).unwrap();
    let hi4 = mem.load(&mut cx, v3, dst_hi4, 4).unwrap();
    assert_eq!(simplify_str(&mut cx, hi4), "0:32");
}

#[test]
fn overlapping_memcpy_and_conditional_merge_preserve_memmove_semantics() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    let mut mem = Memory::new("mem", Width::W64, Width::W8, Endian::Little);

    let base = cx.parse("buf", &o).unwrap();
    let base_plus_2 = cx.parse("buf + 2", &o).unwrap();
    let word = cx.parse("w", &o).unwrap();
    let cond = cx.symbol("dir", Width::W1).unwrap();

    let v_init = mem.store(&mut cx, mem.initial(), base, word).unwrap();
    // Branch 1 (`dir == 1`): shift 6 bytes up by 2 (`memmove(buf + 2, buf, 6)`).
    let v_up = mem.memcpy(&mut cx, v_init, base_plus_2, base, 6).unwrap();
    // Branch 0 (`dir == 0`): shift 6 bytes down by 2 (`memmove(buf, buf + 2, 6)`).
    let v_down = mem.memcpy(&mut cx, v_init, base, base_plus_2, 6).unwrap();

    let v_merged = mem.merge(&mut cx, cond, v_up, v_down).unwrap();
    assert!(mem.reads().is_empty());

    let final_word = mem.load(&mut cx, v_merged, base, 8).unwrap();
    let sample = 0x0807_0605_0403_0201u64;
    for (dir_bit, expected) in [
        // Up by 2: bytes [01, 02, 01, 02, 03, 04, 05, 06]
        (1u64, 0x0605_0403_0201_0201u64),
        // Down by 2: bytes [03, 04, 05, 06, 07, 08, 07, 08]
        (0u64, 0x0807_0807_0605_0403u64),
    ] {
        let env = [
            (
                SymbolKey::from("buf"),
                BitVec::wrapping_from_u64(Width::W64, 0x4000),
            ),
            (
                SymbolKey::from("w"),
                BitVec::wrapping_from_u64(Width::W64, sample),
            ),
            (
                SymbolKey::from("dir"),
                BitVec::wrapping_from_u64(Width::W1, dir_bit),
            ),
        ];
        let got = cx.eval(&[final_word], &env[..]).unwrap()[0].to_u64();
        assert_eq!(got, Some(expected));
    }
}

#[test]
fn error_contracts_for_merge_memset_and_memcpy() {
    let mut cx = Context::new();
    let mut m1 = Memory::new("m1", Width::W32, Width::W8, Endian::Little);
    let m2 = Memory::new("m2", Width::W32, Width::W8, Endian::Little);

    let a32 = cx.symbol("a", Width::W32).unwrap();
    let a64 = cx.symbol("a64", Width::W64).unwrap();
    let b8 = cx.symbol("b8", Width::W8).unwrap();
    let b16 = cx.symbol("b16", Width::W16).unwrap();
    let c1 = cx.symbol("c", Width::W1).unwrap();

    // Cross-memory and diverged-clone versions rejected.
    let mut clone_m1 = m1.clone();
    let v_m1 = m1.store(&mut cx, m1.initial(), a32, b8).unwrap();
    let v_clone = clone_m1
        .store(&mut cx, clone_m1.initial(), a32, b8)
        .unwrap();

    assert!(matches!(
        m1.merge(&mut cx, c1, v_m1, m2.initial()),
        Err(Error::Unsupported(_))
    ));
    assert!(matches!(
        m1.merge(&mut cx, c1, v_m1, v_clone),
        Err(Error::Unsupported(_))
    ));
    assert!(matches!(
        m1.memset(&mut cx, m2.initial(), a32, b8, 4),
        Err(Error::Unsupported(_))
    ));
    assert!(matches!(
        m1.memcpy(&mut cx, m2.initial(), a32, a32, 4),
        Err(Error::Unsupported(_))
    ));

    // Width mismatches rejected even on fast-path counts (`cells == 0` or `v_then == v_else`).
    assert!(matches!(
        m1.merge(&mut cx, b8, v_m1, v_m1),
        Err(Error::Width(_))
    ));
    assert!(matches!(
        m1.memset(&mut cx, v_m1, a64, b8, 0),
        Err(Error::Width(_))
    ));
    assert!(matches!(
        m1.memset(&mut cx, v_m1, a32, b16, 0),
        Err(Error::Width(_))
    ));
    assert!(matches!(
        m1.memcpy(&mut cx, v_m1, a64, a32, 0),
        Err(Error::Width(_))
    ));
    assert!(matches!(
        m1.memcpy(&mut cx, v_m1, a32, a64, 0),
        Err(Error::Width(_))
    ));

    // Cell count cap enforced.
    assert!(matches!(
        m1.memset(&mut cx, v_m1, a32, b8, 4097),
        Err(Error::Unsupported(_))
    ));
    assert!(matches!(
        m1.memcpy(&mut cx, v_m1, a32, a32, 4097),
        Err(Error::Unsupported(_))
    ));
}

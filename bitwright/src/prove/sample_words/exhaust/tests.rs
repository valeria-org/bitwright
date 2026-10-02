use super::super::mask;
use super::*;
use crate::testutil::{Gen, Rng};
use crate::{BitVec, Context, Width};

/// Program::evaluate's input words for the 64 assignments `base .. base + 64`.
fn transposed(inputs: u32, base: u64) -> Vec<u64> {
    (0..inputs)
        .map(|k| (0..64).fold(0, |w, j| w | ((((base + j) >> k) & 1) << j)))
        .collect()
}

#[test]
fn blocks_match_per_lane_evaluation_at_every_slot() {
    let mut generator = Gen {
        rng: Rng(0x424c_4f43_4b53),
        max_w: 64,
        vars: Vec::new(),
    };
    let mut programs = 0;
    for round in 0..512 {
        let mut cx = Context::new();
        let width = [1, 2, 3, 8, 16, 31, 32, 63, 64][round % 9];
        let (root, _) = generator.expr(&mut cx, width, 4);
        let Some(program) = Program::compile(&mut cx, root.index(), &[], None) else {
            continue;
        };
        if program.inputs > 63 {
            continue;
        }
        programs += 1;
        let plan = Plan::new(&program);
        let mut values = vec![[0u64; LANES]; plan.steps.len()];
        let mut lanes = vec![0u64; program.ops.len()];
        // Starting points that exercise carries out of the low input bits.
        for base in [0u64, 64, generator.rng.next() & !63] {
            let base = if program.inputs == 0 {
                0
            } else {
                base & (u64::MAX >> (64 - program.inputs)) & !63
            };
            plan.block(base, LANES, &mut values);
            for half in 0..LANES as u64 / 64 {
                let inputs = transposed(program.inputs, base + 64 * half);
                for lane in 0..64 {
                    program.evaluate(&inputs, lane, &mut lanes);
                    for (slot, (step, _, mask)) in plan.steps.iter().enumerate() {
                        if matches!(step, Step::Skip) {
                            continue;
                        }
                        assert_eq!(
                            values[slot][(64 * half + u64::from(lane)) as usize] & mask,
                            lanes[slot],
                            "slot {slot} of {} at assignment {:#x}",
                            cx.display(root),
                            base + 64 * half + u64::from(lane),
                        );
                    }
                }
            }
        }
    }
    assert!(programs >= 300, "{programs}");
}

#[test]
fn the_first_failure_in_index_order_is_reported_whatever_the_stripes() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::new(20).unwrap()).unwrap();
    // Failing at two points far apart, in different stripes and threads; the lower one wins.
    let early = cx.constant_u64(Width::new(20).unwrap(), 0x1_2345).unwrap();
    let late = cx.constant_u64(Width::new(20).unwrap(), 0xf_edcb).unwrap();
    let a = cx.ne(x, early).unwrap();
    let b = cx.ne(x, late).unwrap();
    let p = cx.and(a, b).unwrap();
    for _ in 0..8 {
        let program = Program::compile(&mut cx, p.index(), &[], None).unwrap();
        let (found, evaluated) = program.exhaust(20).unwrap();
        let Exhausted::Fails(values) = found else {
            panic!("two failing assignments");
        };
        assert_eq!(values, vec![0x1_2345]);
        assert_eq!(evaluated, 0x1_2346);
    }
    let program = Program::compile(&mut cx, a.index(), &[], None).unwrap();
    assert!(
        program.exhaust(19).is_none(),
        "a limit below the domain declines"
    );
}

#[test]
fn constraints_filter_and_declared_bits_fix_the_enumerated_domain() {
    let mut cx = Context::new();
    let w = Width::new(24).unwrap();
    let x = cx.symbol("x", w).unwrap();
    // Known bits leave seven unknown bits, scattered: the domain is 128 assignments.
    let unknown = 0b1000_0001_0010_0100_1001_0010u64;
    let ones = 0x40_0001 & !unknown;
    cx.declare_known(
        x,
        crate::KnownBits::new(
            BitVec::from_u64(w, mask(24) & !(unknown | ones)).unwrap(),
            BitVec::from_u64(w, ones).unwrap(),
        )
        .unwrap(),
    )
    .unwrap();
    let largest = cx.constant_u64(w, unknown | ones).unwrap();
    let p = cx.ne(x, largest).unwrap();
    let program = Program::compile(&mut cx, p.index(), &[], None).unwrap();
    assert_eq!(program.inputs, 7);
    let (found, evaluated) = program.exhaust(7).unwrap();
    assert!(matches!(found, Exhausted::Fails(ref v) if *v == vec![unknown | ones]));
    assert_eq!(evaluated, 128);
    // The same point excluded by a constraint: nothing else fails.
    let constraint = cx.ne(x, largest).unwrap();
    let program = Program::compile(&mut cx, p.index(), &[constraint.index()], None).unwrap();
    let (found, evaluated) = program.exhaust(7).unwrap();
    assert!(matches!(found, Exhausted::Holds));
    assert_eq!(evaluated, 128);
}

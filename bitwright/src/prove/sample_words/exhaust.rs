//! Complete enumeration of a bounded word program, many assignments at a time.
//!
//! Each instruction is applied to a block of consecutive assignments before the next, so the
//! per-instruction dispatch is paid once per block and the lane loops vectorize. The first
//! failing assignment in enumeration order is reported, independently of the thread count.

use super::{Op, Program, Symbol, binary, signed};
use crate::{CmpOp, UnOp};
use std::sync::atomic::{AtomicU64, Ordering};

/// Assignments evaluated together.
const LANES: usize = 128;
/// Assignments claimed by a worker at a time.
const STRIPE: u64 = 1 << 16;

/// The result of enumerating every legal assignment.
pub(in crate::prove) enum Exhausted {
    /// The goal holds wherever the constraints do.
    Holds,
    /// The first assignment, in enumeration order, where the constraints hold and the goal
    /// does not: each symbol with its value.
    Fails(Vec<u64>),
}

#[derive(Clone, Copy)]
enum Src {
    Slot(usize),
    Imm(u64),
}

/// How a symbol's value is assembled from an assignment index.
enum Place {
    /// `ones | ((index >> first) & mask) << low`: consecutive coordinates on consecutive bits.
    Run { first: u32, mask: u64, low: u16 },
    /// Any other placement: each `(bit, coordinate)` separately.
    Bits(Vec<(u16, u32)>),
}

enum Step {
    /// Constants are applied as immediates and never written.
    Skip,
    Symbol(u64, Place),
    Unary(UnOp, Src),
    Binary(crate::BinOp, Src, Src),
    Compare(CmpOp, Src, Src, u16),
    Copy(Src),
    Sext(Src, u16),
    Extract(Src, u16),
    Concat(Src, Src, u16),
    Select(Src, Src, Src),
}

struct Plan {
    steps: Vec<(Step, u16, u64)>,
    goal: Src,
    constraints: Vec<Src>,
}

fn place(symbol: &Symbol) -> Place {
    let run = symbol
        .unknown
        .windows(2)
        .all(|w| w[1].0 == w[0].0 + 1 && w[1].1 == w[0].1 + 1);
    match symbol.unknown.first() {
        Some(&(low, first)) if run => Place::Run {
            first,
            mask: u64::MAX >> (64 - symbol.unknown.len()),
            low,
        },
        None => Place::Run {
            first: 0,
            mask: 0,
            low: 0,
        },
        _ => Place::Bits(symbol.unknown.clone()),
    }
}

impl Plan {
    fn new(program: &Program) -> Self {
        let src = |slot: usize| match program.ops[slot].op {
            Op::Constant(value) => Src::Imm(value & program.ops[slot].mask),
            _ => Src::Slot(slot),
        };
        let steps = program
            .ops
            .iter()
            .map(|instruction| {
                let step = match instruction.op {
                    Op::Constant(_) => Step::Skip,
                    Op::Symbol(slot) => {
                        let symbol = &program.symbols[slot];
                        Step::Symbol(symbol.ones, place(symbol))
                    }
                    Op::Unary(op, a) => Step::Unary(op, src(a)),
                    Op::Binary(op, a, b) => Step::Binary(op, src(a), src(b)),
                    Op::Compare(op, a, b, w) => Step::Compare(op, src(a), src(b), w),
                    Op::Zext(a) => Step::Copy(src(a)),
                    Op::Sext(a, w) => Step::Sext(src(a), w),
                    Op::Extract(a, lo) => Step::Extract(src(a), lo),
                    Op::Concat(a, b, low) => Step::Concat(src(a), src(b), low),
                    Op::Select(c, t, e) => Step::Select(src(c), src(t), src(e)),
                };
                (step, instruction.width, instruction.mask)
            })
            .collect();
        Plan {
            steps,
            goal: src(program.goal),
            constraints: program.constraints.iter().map(|&c| src(c)).collect(),
        }
    }

    /// Evaluates assignments `base .. base + LANES` and returns the lanes at which the
    /// constraints hold and the goal does not, as a mask over the first `valid` lanes.
    fn block(&self, base: u64, valid: usize, values: &mut [[u64; LANES]]) -> u128 {
        for (i, (step, width, mask)) in self.steps.iter().enumerate() {
            let (done, rest) = values.split_at_mut(i);
            let out = &mut rest[0];
            let m = *mask;
            match step {
                Step::Skip => {}
                Step::Symbol(ones, Place::Run { first, mask, low }) => {
                    for (j, o) in out.iter_mut().enumerate() {
                        *o = ones | ((((base + j as u64) >> first) & mask) << low);
                    }
                }
                Step::Symbol(ones, Place::Bits(bits)) => {
                    for (j, o) in out.iter_mut().enumerate() {
                        let index = base + j as u64;
                        *o = bits.iter().fold(*ones, |v, &(bit, coordinate)| {
                            v | (((index >> coordinate) & 1) << bit)
                        });
                    }
                }
                Step::Unary(op, a) => {
                    let w = u32::from(*width);
                    match op {
                        UnOp::Not => unary(out, done, *a, m, |x| !x),
                        UnOp::Neg => unary(out, done, *a, m, u64::wrapping_neg),
                        UnOp::Popcnt => unary(out, done, *a, m, |x| u64::from(x.count_ones())),
                        UnOp::Clz => unary(out, done, *a, m, |x| {
                            u64::from(x.leading_zeros() - (64 - w))
                        }),
                        UnOp::Ctz => {
                            unary(out, done, *a, m, |x| u64::from(x.trailing_zeros().min(w)))
                        }
                        UnOp::Bswap => unary(out, done, *a, m, |x| x.swap_bytes() >> (64 - w)),
                        UnOp::BitRev => unary(out, done, *a, m, |x| x.reverse_bits() >> (64 - w)),
                    }
                }
                Step::Binary(op, a, b) => {
                    use crate::BinOp as B;
                    let w = u64::from(*width);
                    match op {
                        B::Add => binary2(out, done, *a, *b, m, u64::wrapping_add),
                        B::Sub => binary2(out, done, *a, *b, m, u64::wrapping_sub),
                        B::Mul => binary2(out, done, *a, *b, m, u64::wrapping_mul),
                        B::And => binary2(out, done, *a, *b, m, |x, y| x & y),
                        B::Or => binary2(out, done, *a, *b, m, |x, y| x | y),
                        B::Xor => binary2(out, done, *a, *b, m, |x, y| x ^ y),
                        B::Shl => {
                            binary2(out, done, *a, *b, m, |x, y| if y >= w { 0 } else { x << y })
                        }
                        B::LShr => {
                            binary2(out, done, *a, *b, m, |x, y| if y >= w { 0 } else { x >> y })
                        }
                        // The remaining operators share the per-lane scalar definition.
                        &op => binary2(out, done, *a, *b, m, |x, y| binary(op, x, y, *width)),
                    }
                }
                Step::Compare(op, a, b, w) => {
                    let w = *w;
                    match op {
                        CmpOp::Eq => binary2(out, done, *a, *b, 1, |x, y| u64::from(x == y)),
                        CmpOp::Ne => binary2(out, done, *a, *b, 1, |x, y| u64::from(x != y)),
                        CmpOp::Ult => binary2(out, done, *a, *b, 1, |x, y| u64::from(x < y)),
                        CmpOp::Ule => binary2(out, done, *a, *b, 1, |x, y| u64::from(x <= y)),
                        CmpOp::Slt => binary2(out, done, *a, *b, 1, |x, y| {
                            u64::from(signed(x, w) < signed(y, w))
                        }),
                        CmpOp::Sle => binary2(out, done, *a, *b, 1, |x, y| {
                            u64::from(signed(x, w) <= signed(y, w))
                        }),
                    }
                }
                Step::Copy(a) => unary(out, done, *a, m, |x| x),
                Step::Sext(a, w) => {
                    let w = *w;
                    unary(out, done, *a, m, |x| signed(x, w) as u64);
                }
                Step::Extract(a, lo) => {
                    let lo = *lo;
                    unary(out, done, *a, m, |x| x >> lo);
                }
                Step::Concat(a, b, low) => {
                    let low = *low;
                    binary2(out, done, *a, *b, m, |x, y| (x << low) | y);
                }
                Step::Select(c, t, e) => {
                    for (j, o) in out.iter_mut().enumerate() {
                        let pick = if get(done, *c, j) != 0 { *t } else { *e };
                        *o = get(done, pick, j) & m;
                    }
                }
            }
        }
        let mut failing = 0u128;
        for j in 0..valid {
            if get(values, self.goal, j) == 0
                && self.constraints.iter().all(|&c| get(values, c, j) != 0)
            {
                failing |= 1 << j;
            }
        }
        failing
    }
}

#[inline(always)]
fn get(values: &[[u64; LANES]], s: Src, j: usize) -> u64 {
    match s {
        Src::Slot(i) => values[i][j],
        Src::Imm(v) => v,
    }
}

#[inline(always)]
fn unary(out: &mut [u64; LANES], done: &[[u64; LANES]], a: Src, m: u64, f: impl Fn(u64) -> u64) {
    match a {
        Src::Slot(i) => {
            let x = &done[i];
            for k in 0..LANES {
                out[k] = f(x[k]) & m;
            }
        }
        Src::Imm(v) => out.fill(f(v) & m),
    }
}

#[inline(always)]
fn binary2(
    out: &mut [u64; LANES],
    done: &[[u64; LANES]],
    a: Src,
    b: Src,
    m: u64,
    f: impl Fn(u64, u64) -> u64,
) {
    match (a, b) {
        (Src::Slot(i), Src::Slot(j)) => {
            let (x, y) = (&done[i], &done[j]);
            for k in 0..LANES {
                out[k] = f(x[k], y[k]) & m;
            }
        }
        (Src::Slot(i), Src::Imm(v)) => {
            let x = &done[i];
            for k in 0..LANES {
                out[k] = f(x[k], v) & m;
            }
        }
        (Src::Imm(v), Src::Slot(j)) => {
            let y = &done[j];
            for k in 0..LANES {
                out[k] = f(v, y[k]) & m;
            }
        }
        (Src::Imm(v), Src::Imm(u)) => out.fill(f(v, u) & m),
    }
}

/// Runs `work` on claimed stripes of `0..total` across the available threads, or on this
/// thread alone where threads cannot be spawned.
pub(in crate::prove) fn stripes(total: u64, stripe: u64, work: impl Fn(u64, u64) + Sync) {
    let next = AtomicU64::new(0);
    let worker = || {
        loop {
            let base = next.fetch_add(stripe, Ordering::Relaxed);
            if base >= total {
                break;
            }
            work(base, (base + stripe).min(total));
        }
    };
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get());
    let threads = threads.min(usize::try_from(total.div_ceil(stripe)).unwrap_or(usize::MAX));
    std::thread::scope(|scope| {
        for _ in 1..threads {
            // A target without threads still finishes every stripe on the calling thread.
            if std::thread::Builder::new()
                .spawn_scoped(scope, worker)
                .is_err()
            {
                break;
            }
        }
        worker();
    });
}

impl Program {
    /// Every legal assignment of the program's unknown input bits, in index order; `None` when
    /// it has more than `limit` of them.
    pub(in crate::prove) fn exhaust(&self, limit: u8) -> Option<(Exhausted, u64)> {
        if self.inputs > u32::from(limit.min(63)) {
            return None;
        }
        let plan = Plan::new(self);
        let total = 1u64 << self.inputs;
        // The smallest failing index found so far; stripes past it are skipped.
        let first = AtomicU64::new(u64::MAX);
        stripes(total, STRIPE, |start, end| {
            if start >= first.load(Ordering::Relaxed) {
                return;
            }
            let mut values = vec![[0u64; LANES]; plan.steps.len()];
            let mut base = start;
            while base < end {
                let valid = (end - base).min(LANES as u64) as usize;
                let failing = plan.block(base, valid, &mut values);
                if failing != 0 {
                    first.fetch_min(
                        base + u64::from(failing.trailing_zeros()),
                        Ordering::Relaxed,
                    );
                    return;
                }
                base += LANES as u64;
            }
        });
        let index = first.into_inner();
        if index == u64::MAX {
            return Some((Exhausted::Holds, total));
        }
        let values = self
            .symbols
            .iter()
            .map(|symbol| {
                symbol
                    .unknown
                    .iter()
                    .fold(symbol.ones, |v, &(bit, coordinate)| {
                        v | (((index >> coordinate) & 1) << bit)
                    })
            })
            .collect();
        Some((Exhausted::Fails(values), index + 1))
    }
}

#[cfg(test)]
mod tests;

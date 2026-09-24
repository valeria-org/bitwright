//! Self-checks for the floating-point oracle.
//!
//! None of these re-run the oracle's method (exact values rounded by the quantum formula). They
//! use (1) the host's IEEE 754 binary32/binary64 arithmetic (round to nearest even) as a
//! structurally different oracle; (2) a brute-force rounding for tiny formats that enumerates
//! every finite value and picks neighbours by exact native-integer comparisons; (3) hand-computed
//! cases from the contract; and (4) algebraic identities, exhaustively on tiny formats.

use super::*;

mod brute;
mod cases;
mod hardware;
mod identities;

const B16: Format = Format { eb: 5, sb: 11 };
const BF16: Format = Format { eb: 8, sb: 8 };
const B32: Format = Format { eb: 8, sb: 24 };
const B64: Format = Format { eb: 11, sb: 53 };
const B128: Format = Format { eb: 15, sb: 113 };
const X87V: Format = Format { eb: 15, sb: 64 };

/// Every tiny format of width at most 8.
const TINY: [Format; 15] = [
    Format { eb: 2, sb: 2 },
    Format { eb: 2, sb: 3 },
    Format { eb: 3, sb: 2 },
    Format { eb: 2, sb: 4 },
    Format { eb: 3, sb: 3 },
    Format { eb: 4, sb: 2 },
    Format { eb: 2, sb: 5 },
    Format { eb: 3, sb: 4 },
    Format { eb: 4, sb: 3 },
    Format { eb: 5, sb: 2 },
    Format { eb: 2, sb: 6 },
    Format { eb: 3, sb: 5 },
    Format { eb: 4, sb: 4 },
    Format { eb: 5, sb: 3 },
    Format { eb: 6, sb: 2 },
];

/// `x` as a `w`-bit value.
fn bw(w: u16, x: u128) -> Bits {
    Bits::from_u128(w, x)
}

fn val(x: &Bits) -> u128 {
    x.to_u128().expect("value fits in u128")
}

fn f32b(x: f32) -> Bits {
    bw(32, x.to_bits().into())
}

fn f64b(x: f64) -> Bits {
    bw(64, x.to_bits().into())
}

/// An encoding of `f` (width at most 128) from its fields.
fn enc(f: Format, neg: bool, e: u128, t: u128) -> Bits {
    let w = f.width();
    assert!(t < 1u128 << (f.sb - 1) && e < 1u128 << f.eb);
    bw(w, (u128::from(neg) << (w - 1)) | (e << (f.sb - 1)) | t)
}

/// splitmix64, deterministic.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn coin(&mut self) -> bool {
        self.next() & 1 == 1
    }

    /// A random encoding of `f` (width at most 64), biased toward zeros, infinities, NaNs,
    /// subnormals, the extreme binades, values near 1, and trailing significands with few or
    /// many bits set.
    fn value(&mut self, f: Format) -> u64 {
        let (eb, sb) = (u32::from(f.eb), u32::from(f.sb));
        let w = eb + sb;
        let tmask = (1u64 << (sb - 1)) - 1;
        let e_special = (1u64 << eb) - 1;
        let bias = (1u64 << (eb - 1)) - 1;
        let sign = u64::from(self.coin()) << (w - 1);
        let e = match self.below(16) {
            0 | 1 => 0,
            2 => e_special,
            3 => 1,
            4 => e_special - 1,
            5 | 6 => bias - 2 + self.below(5),
            7 => 1 + self.below(u64::from(sb) + 2),
            _ => self.below(e_special + 1),
        };
        let t = match self.below(10) {
            0 | 1 => 0,
            2 => tmask,
            3 => 1,
            4 => 1 << (sb - 2),
            5 => tmask - self.below(4),
            6 => self.below(8),
            7 => (tmask >> self.below(u64::from(sb) - 1)) << self.below(4) & tmask,
            _ => self.next() & tmask,
        };
        sign | (e << (sb - 1)) | t
    }

    /// A second operand related to `a`: its negation (exact cancellation), a neighbour of `a` or
    /// of `-a`, `a` scaled down by about `p` binades (ties and sticky bits when added), or an
    /// unrelated value.
    fn related(&mut self, f: Format, a: u64) -> u64 {
        let (eb, sb) = (u32::from(f.eb), u32::from(f.sb));
        let w = eb + sb;
        let mask = if w == 64 { u64::MAX } else { (1u64 << w) - 1 };
        let sign = 1u64 << (w - 1);
        let emask = ((1u64 << eb) - 1) << (sb - 1);
        match self.below(6) {
            0 => a ^ sign,
            1 => ((a ^ sign).wrapping_add(self.below(5)).wrapping_sub(2)) & mask,
            2 => (a.wrapping_add(self.below(5)).wrapping_sub(2)) & mask,
            3 => {
                let e = (a & emask) >> (sb - 1);
                let e2 = e.saturating_sub(u64::from(sb) - 1 + self.below(3));
                let t = if self.coin() {
                    0
                } else {
                    self.next() & ((1u64 << (sb - 1)) - 1)
                };
                let s = if self.coin() {
                    a & sign
                } else {
                    (a ^ sign) & sign
                };
                s | (e2 << (sb - 1)) | t
            }
            _ => self.value(f),
        }
    }
}

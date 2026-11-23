//! Bit-blasting: every bit-vector operator as a circuit over the bits of its operands, with
//! bitwright's total semantics (SMT-LIB's): division by zero, shifts past the width, rotations
//! by any count. Bits are little-endian.

use super::aig::{Aig, FALSE, L, TRUE};
use crate::BitVec;

/// A bit-vector: its bits, least significant first.
pub type Bits = Vec<L>;

/// The constant `v`.
pub fn konst(v: &BitVec) -> Bits {
    (0..v.width().bits())
        .map(|i| if v.bit(i) == Some(true) { TRUE } else { FALSE })
        .collect()
}

/// A constant of `w` bits from a `u64` (truncated).
pub fn small(w: usize, v: u64) -> Bits {
    (0..w)
        .map(|i| {
            if i < 64 && (v >> i) & 1 == 1 {
                TRUE
            } else {
                FALSE
            }
        })
        .collect()
}

pub fn not(g: &mut Aig, a: &[L]) -> Bits {
    let _ = g;
    a.iter().map(|&x| x ^ 1).collect()
}

pub fn and(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    a.iter().zip(b).map(|(&x, &y)| g.and(x, y)).collect()
}

pub fn or(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    a.iter().zip(b).map(|(&x, &y)| g.or(x, y)).collect()
}

pub fn xor(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    xor_bits(g, a, b, false)
}

pub(super) fn xor_cancel_input(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    xor_bits(g, a, b, true)
}

fn xor_bits(g: &mut Aig, a: &[L], b: &[L], cancel_input: bool) -> Bits {
    a.iter()
        .zip(b)
        .enumerate()
        .map(|(i, (&x, &y))| {
            // Low-bit parity cones are small; wider bits cancel one shared input by
            // rebuilding only its XOR path, retaining the surrounding arithmetic branches.
            if i < 2 {
                g.xor_simplified(x, y)
            } else if cancel_input {
                g.xor_cancel_input(x, y)
            } else {
                g.xor(x, y)
            }
        })
        .collect()
}

pub fn mux(g: &mut Aig, c: L, t: &[L], e: &[L]) -> Bits {
    t.iter().zip(e).map(|(&x, &y)| g.mux(c, x, y)).collect()
}

/// `a + b + cin`, and the carry out.
pub fn add_carry(g: &mut Aig, a: &[L], b: &[L], cin: L) -> (Bits, L) {
    let mut c = cin;
    let mut out = Vec::with_capacity(a.len());
    for (&x, &y) in a.iter().zip(b) {
        let s = g.xor(x, y);
        out.push(g.xor(s, c));
        c = g.maj(x, y, c);
    }
    (out, c)
}

pub fn add(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    add_wrapping(g, a, b, FALSE)
}

pub fn sub(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    let nb = not(g, b);
    add_wrapping(g, a, &nb, TRUE)
}

fn add_wrapping(g: &mut Aig, a: &[L], b: &[L], cin: L) -> Bits {
    let mut carry = cin;
    let mut out = Vec::with_capacity(a.len());
    for (i, (&x, &y)) in a.iter().zip(b).enumerate() {
        if i + 1 == a.len() {
            // This column's outgoing carry is discarded modulo 2^W. Other columns
            // retain ordinary XOR shapes for carry encoding.
            let sum = g.xor_phase(x, y);
            out.push(g.xor_phase(sum, carry));
        } else {
            let sum = g.xor(x, y);
            out.push(g.xor(sum, carry));
            carry = g.maj(x, y, carry);
        }
    }
    out
}

pub fn neg(g: &mut Aig, a: &[L]) -> Bits {
    let z = vec![FALSE; a.len()];
    sub(g, &z, a)
}

/// `a <u b`: the borrow out of `a − b`.
pub fn ult(g: &mut Aig, a: &[L], b: &[L]) -> L {
    let nb = not(g, b);
    let (_, carry) = add_carry(g, a, &nb, TRUE);
    carry ^ 1
}

pub fn ule(g: &mut Aig, a: &[L], b: &[L]) -> L {
    ult(g, b, a) ^ 1
}

/// `a <s b`: unsigned with the sign bits flipped.
pub fn slt(g: &mut Aig, a: &[L], b: &[L]) -> L {
    let mut a2 = a.to_vec();
    let mut b2 = b.to_vec();
    if let (Some(x), Some(y)) = (a2.last_mut(), b2.last_mut()) {
        *x ^= 1;
        *y ^= 1;
    }
    ult(g, &a2, &b2)
}

pub fn sle(g: &mut Aig, a: &[L], b: &[L]) -> L {
    slt(g, b, a) ^ 1
}

pub fn eq(g: &mut Aig, a: &[L], b: &[L]) -> L {
    eq_bits(g, a, b, false)
}

pub(super) fn eq_factored(g: &mut Aig, a: &[L], b: &[L]) -> L {
    eq_bits(g, a, b, true)
}

fn eq_bits(g: &mut Aig, a: &[L], b: &[L], factor_joins: bool) -> L {
    let bits: Vec<L> = a
        .iter()
        .zip(b)
        .map(|(&x, &y)| {
            if factor_joins && y == TRUE {
                g.factor_positive_or(x, 2)
            } else if factor_joins && x == TRUE {
                g.factor_positive_or(y, 2)
            } else {
                g.xnor(x, y)
            }
        })
        .collect();
    g.and_all(&bits)
}

/// The product modulo `2^w`. Constant multipliers use shift/add rows, recoding
/// signed digits and sharing recurring pairs on dense words. Eligible 64-bit odd
/// constants may first split into cheaper modular factors with a source correction.
pub fn mul(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    if let Some((bit, data)) = binary_factor(a, b) {
        return data.iter().map(|&value| g.and(bit, value)).collect();
    }
    if b.iter().all(|&bit| bit <= TRUE) {
        return mul_constant(g, a, b);
    }
    if a.iter().all(|&bit| bit <= TRUE) {
        return mul_constant(g, b, a);
    }
    mul_rows(g, a, b)
}

/// A word whose only possibly nonzero bit is bit zero is exactly a Boolean multiplier.
/// Its product is a bitwise conditional copy, with no carries or signed-digit rows.
pub(super) fn binary_factor<'a>(a: &'a [L], b: &'a [L]) -> Option<(L, &'a [L])> {
    if !a.is_empty() && a[1..].iter().all(|&bit| bit == FALSE) {
        Some((a[0], b))
    } else if !b.is_empty() && b[1..].iter().all(|&bit| bit == FALSE) {
        Some((b[0], a))
    } else {
        None
    }
}

fn mul_constant(g: &mut Aig, a: &[L], constant: &[L]) -> Bits {
    if factorable_data(a)
        && let Some((small, other, correction)) = constant_factors(constant)
    {
        let first = self::small(a.len(), small);
        let second = self::small(a.len(), other);
        let intermediate = mul_constant_unfactored(g, a, &first);
        let product = mul_constant_unfactored(g, &intermediate, &second);
        return correct_product(g, product, a, correction);
    }
    mul_constant_unfactored(g, a, constant)
}

// Estimate active carry columns before any data-dependent row sharing.
fn constant_work(value: u64, width: usize) -> usize {
    if value == 0 {
        return 0;
    }
    if width == 64 {
        // Nonadjacent signed digits from parallel bit operations. Truncating the
        // addition discards exactly the carry which vanishes modulo 2^64.
        let half = value >> 1;
        let sum = value.wrapping_add(half);
        let changed = sum ^ half;
        let positive = sum & changed;
        let negative = half & changed;
        let digits = positive | negative;
        let highest = 63 - digits.leading_zeros();
        let initial_negative = negative >> highest & 1 != 0;
        let (columns, free) =
            if digits.count_ones() + u32::from(initial_negative) >= value.count_ones() {
                (value, 64 - value.trailing_zeros() as usize)
            } else {
                (
                    digits,
                    if initial_negative {
                        0
                    } else {
                        64 - highest as usize
                    },
                )
            };
        return weighted_columns(columns) - free;
    }
    let mut carry = false;
    let mut digits = 0;
    let mut signed_work = 0;
    let mut last = (0, false);
    let mut ordinary_work = 0;
    for i in 0..width {
        let bit = value >> i & 1 != 0;
        if bit {
            ordinary_work += width - i;
        }
        match usize::from(bit) + usize::from(carry) {
            0 => carry = false,
            2 => carry = true,
            _ => {
                let negative = i + 1 < width && value >> (i + 1) & 1 != 0;
                digits += 1;
                signed_work += width - i;
                last = (i, negative);
                carry = negative;
            }
        }
    }
    if digits + usize::from(last.1) >= value.count_ones() as usize {
        ordinary_work - (width - value.trailing_zeros() as usize)
    } else {
        signed_work - if last.1 { 0 } else { width - last.0 }
    }
}

fn weighted_columns(mut columns: u64) -> usize {
    let mut work = 0;
    while columns != 0 {
        work += 64 - columns.trailing_zeros() as usize;
        columns &= columns - 1;
    }
    work
}

// Factoring can expand narrow or highly correlated data. Keep the existing
// representation unless the low bit is variable, the highest bit is not known
// zero, and at least half the word consists of distinct nonconstant literals.
fn factorable_data(data: &[L]) -> bool {
    if data.len() != 64 || data[0] <= TRUE || data[63] == FALSE {
        return false;
    }
    let mut unique = [FALSE; 32];
    let mut len = 0;
    for &bit in data {
        let bit = bit & !1;
        if bit != FALSE && !unique[..len].contains(&bit) {
            unique[len] = bit;
            len += 1;
            if len == unique.len() {
                return true;
            }
        }
    }
    false
}

fn correct_product(g: &mut Aig, product: Bits, source: &[L], correction: i8) -> Bits {
    match correction {
        1 => add(g, &product, source),
        -1 => sub(g, &product, source),
        _ => product,
    }
}

fn constant_factors(constant: &[L]) -> Option<(u64, u64, i8)> {
    let width = constant.len();
    if width != 64 || constant[0] != TRUE {
        return None;
    }
    let value = constant.iter().enumerate().try_fold(0u64, |v, (i, &bit)| {
        (bit <= TRUE).then_some(v | (u64::from(bit == TRUE) << i))
    })?;
    let original = constant_work(value, width);
    if original <= 2 * width {
        return None;
    }
    let mut best = original;
    let mut factors = None;
    // Each factor * other + correction equals value modulo 2^64. A fixed
    // 381-candidate search permits two multiplication stages and one correction,
    // without recursion. Exact factorizations win ties and need no correction.
    // Newton steps double the inverse's correct bit count from one to 64.
    for factor in (3u64..256).step_by(2) {
        let mut inverse = 1u64;
        for _ in 0..6 {
            inverse = inverse.wrapping_mul(2u64.wrapping_sub(factor.wrapping_mul(inverse)));
        }
        let first_work = constant_work(factor, width);
        for correction in [0i8, 1, -1] {
            let adjusted = value.wrapping_add_signed(-i64::from(correction));
            let other = adjusted.wrapping_mul(inverse);
            let correction_work = match correction {
                // The even product's low zeros copy the source without carrying.
                1 if other != 0 => width - other.trailing_zeros() as usize,
                0 => 0,
                _ => width,
            };
            let work = first_work + constant_work(other, width) + correction_work;
            if work < best
                || (work == best
                    && correction == 0
                    && factors.is_some_and(|(_, _, previous)| previous != 0))
            {
                best = work;
                factors = Some((factor, other, correction));
            }
        }
    }
    if best * 10 <= original * 9 {
        factors
    } else {
        None
    }
}

fn mul_constant_unfactored(g: &mut Aig, a: &[L], constant: &[L]) -> Bits {
    let mut carry = false;
    let mut digits = Vec::new();
    for (i, &bit) in constant.iter().enumerate() {
        match u8::from(bit == TRUE) + u8::from(carry) {
            0 => carry = false,
            2 => carry = true,
            _ => {
                let negative = constant.get(i + 1) == Some(&TRUE);
                digits.push((i, negative));
                carry = negative;
            }
        }
    }
    // A carry out of the word vanishes modulo 2^w. The initial negative row needs a
    // negation, whereas the initial positive row is free.
    let signed = digits.len() + usize::from(digits.last().is_some_and(|&(_, neg)| neg))
        < constant.iter().filter(|&&bit| bit == TRUE).count();
    if (16..=64).contains(&a.len()) && digits.len() >= 6 {
        let variables = a.iter().filter(|&&bit| bit > TRUE).count();
        // A masked word with a dense fixed bias and just a few variable bits
        // needs only one conditional constant row per such bit, not one
        // symbolic row per coefficient digit.
        if (1..=8).contains(&variables)
            && 2 * variables <= digits.len()
            && a.iter().filter(|&&bit| bit == TRUE).count() * 2 >= a.len()
        {
            return mul_sparse_biased(g, a, constant);
        }
        // Group pairs only in the representation we would actually emit.
        if variables * 4 >= a.len() * 3 {
            if !signed {
                digits.clear();
                digits.extend(
                    constant
                        .iter()
                        .enumerate()
                        .filter_map(|(i, &bit)| (bit == TRUE).then_some((i, false))),
                );
            }
            if let Some(product) = mul_repeated_pair(g, a, &digits) {
                return product;
            }
        }
    }
    let mut acc = vec![FALSE; a.len()];
    if signed {
        for (shift, negative) in digits.into_iter().rev() {
            accumulate_product_row(g, &mut acc[shift..], a.iter().copied(), negative);
        }
    } else {
        let mut shifts = constant.iter().enumerate().filter_map(|(i, &bit)| {
            (bit == TRUE).then_some(i)
        });
        if let Some(first) = shifts.next() {
            acc[first..].copy_from_slice(&a[..a.len() - first]);
        }
        for shift in shifts {
            accumulate_product_row(g, &mut acc[shift..], a.iter().copied(), false);
        }
    }
    acc
}

// Write D = fixed + Σ bit[i]·2^i. The first variable selects between
// two constant products, so no adder is needed for either it or the bias.
// Native wrapping arithmetic also gives the right low bits for widths < 64.
fn mul_sparse_biased(g: &mut Aig, data: &[L], constant: &[L]) -> Bits {
    let fixed_word = |bits: &[L]| {
        bits.iter()
            .enumerate()
            .fold(0u64, |v, (i, &bit)| v | (u64::from(bit == TRUE) << i))
    };
    let k = fixed_word(constant);
    let bias = fixed_word(data).wrapping_mul(k);
    let mut rows = data.iter().enumerate().filter(|&(_, &bit)| bit > TRUE);
    let (first, &selector) = rows.next().expect("nonempty sparse source");
    let alternate = bias.wrapping_add(k << first);
    let mut acc: Bits = (0..data.len())
        .map(|i| {
            let low = (bias >> i & 1) as L;
            if (alternate ^ bias) >> i & 1 == 0 {
                low
            } else {
                selector ^ low
            }
        })
        .collect();
    for (shift, &selector) in rows {
        let row = constant
            .iter()
            .map(|&k| if k == TRUE { selector } else { FALSE });
        accumulate_product_row(g, &mut acc[shift..], row, false);
    }
    acc
}

// Add or subtract the row at this shift modulo the active suffix width. Bits
// below the shift stay untouched, and the carry out of its top bit is dead.
fn accumulate_product_row(
    g: &mut Aig,
    acc: &mut [L],
    row: impl Iterator<Item = L>,
    negative: bool,
) {
    let n = acc.len();
    let mask = u32::from(negative);
    let mut carry = mask;
    for (j, (sum, bit)) in acc.iter_mut().zip(row).enumerate() {
        let prev = *sum;
        let bit = bit ^ mask;
        if j + 1 == n {
            let parity = g.xor_phase(prev, bit);
            *sum = g.xor_phase(parity, carry);
        } else {
            let parity = g.xor(prev, bit);
            *sum = g.xor(parity, carry);
            carry = g.maj(prev, bit, carry);
        }
    }
}

// For a fixed gap d, adjacent digits ±2^i and ±2^(i+d) are a
// shifted copy of (2^d ± 1), with the sign of the higher digit. Find
// non-overlapping occurrences of each small pair in one pass. Its first
// use pays for forming that multiple; only later uses count as savings.
fn mul_repeated_pair(g: &mut Aig, a: &[L], digits: &[(usize, bool)]) -> Option<Bits> {
    const GAPS: usize = 8;
    let w = a.len();
    let mut pairs = [0u64; GAPS * 2];
    let mut saved = [0usize; GAPS * 2];
    for pair in digits.windows(2) {
        let (lo, neg_lo) = pair[0];
        let (hi, neg_hi) = pair[1];
        let gap = hi - lo;
        if gap > GAPS {
            continue;
        }
        let key = 2 * (gap - 1) + usize::from(neg_lo != neg_hi);
        let ends = &mut pairs[key];
        if *ends & (1 << lo) == 0 {
            if *ends != 0 {
                saved[key] += w - hi;
            }
            *ends |= 1 << hi;
        }
    }
    let (key, &savings) = saved.iter().enumerate().max_by_key(|&(_, n)| n)?;
    // Don't trade a tiny top-bit row for a change in carry topology.
    if savings < w / 2 {
        return None;
    }
    let ends = pairs[key];
    let gap = key / 2 + 1;
    let first_lo = ends.trailing_zeros() as usize - gap;
    let n = w - first_lo;
    let mut multiple = vec![FALSE; n];
    multiple[gap..].copy_from_slice(&a[..n - gap]);
    accumulate_product_row(g, &mut multiple, a.iter().copied(), key % 2 != 0);

    // Accumulate from the highest term. Only write the active suffix of a
    // row; no padded copies, and no gates for discarded high output bits.
    let mut acc = vec![FALSE; w];
    let mut i = digits.len();
    while i != 0 {
        i -= 1;
        let (hi, negative) = digits[i];
        let (shift, row) = if ends & (1 << hi) != 0 {
            i -= 1;
            (hi - gap, multiple.as_slice())
        } else {
            (hi, a)
        };
        accumulate_product_row(g, &mut acc[shift..], row.iter().copied(), negative);
    }
    Some(acc)
}

fn mul_rows(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    let w = a.len();
    let mut acc = vec![FALSE; w];
    for (i, &bi) in b.iter().enumerate() {
        if bi == FALSE {
            continue;
        }
        let mut part = vec![FALSE; w];
        for j in 0..w - i {
            part[i + j] = g.and(a[j], bi);
        }
        acc = add(g, &acc, &part);
    }
    acc
}

/// A modular product with column compression and one final carry-propagating addition.
/// Constant rows use signed digits when this reduces the number of partial products.
/// Negative rows are complemented only above their shift and receive the corresponding
/// two's-complement correction bit. Eligible constant factors use two compression stages
/// with an optional final source addition or subtraction.
/// The carry out of the word is discarded.
pub fn mul_carry_save(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    if let Some((bit, data)) = binary_factor(a, b) {
        return data.iter().map(|&value| g.and(bit, value)).collect();
    }
    let constant = if b.iter().all(|&l| l <= TRUE) {
        Some((a, b))
    } else if a.iter().all(|&l| l <= TRUE) {
        Some((b, a))
    } else {
        None
    };
    if let Some((data, constant)) = constant
        && factorable_data(data)
        && let Some((small, other, correction)) = constant_factors(constant)
    {
        let first = self::small(data.len(), small);
        let second = self::small(data.len(), other);
        let intermediate = mul_carry_save_unfactored(g, data, &first);
        let product = mul_carry_save_unfactored(g, &intermediate, &second);
        return correct_product(g, product, data, correction);
    }
    mul_carry_save_unfactored(g, a, b)
}

fn mul_carry_save_unfactored(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    let w = a.len();
    let mut columns = vec![Vec::new(); w];
    let constant = if b.iter().all(|&l| l <= TRUE) {
        Some((a, b))
    } else if a.iter().all(|&l| l <= TRUE) {
        Some((b, a))
    } else {
        None
    };
    if let Some((data, constant)) = constant {
        let mut carry = false;
        let mut digits = Vec::new();
        for (i, &bit) in constant.iter().enumerate() {
            match u8::from(bit == TRUE) + u8::from(carry) {
                0 => carry = false,
                2 => carry = true,
                _ => {
                    let negative = constant.get(i + 1) == Some(&TRUE);
                    digits.push((i, negative));
                    carry = negative;
                }
            }
        }
        if digits.len() >= constant.iter().filter(|&&l| l == TRUE).count() {
            digits = constant
                .iter()
                .enumerate()
                .filter_map(|(i, &l)| (l == TRUE).then_some((i, false)))
                .collect();
        }
        for (shift, negative) in digits {
            if negative {
                columns[shift].push(TRUE);
            }
            for j in 0..w - shift {
                let bit = data[j] ^ u32::from(negative);
                if bit != FALSE {
                    columns[shift + j].push(bit);
                }
            }
        }
    } else {
        for (i, &bi) in b.iter().enumerate() {
            for j in 0..w - i {
                let bit = g.and(a[j], bi);
                if bit != FALSE {
                    columns[i + j].push(bit);
                }
            }
        }
    }
    let mut first = vec![FALSE; w];
    let mut second = vec![FALSE; w];
    for i in 0..w {
        // Consume older rows before new sums, avoiding a linear-depth chain within a
        // column. Carries from the previous column join its original partial products.
        let mut head = 0;
        while columns[i].len() - head > 2 {
            let (x, y, z) = (columns[i][head], columns[i][head + 1], columns[i][head + 2]);
            head += 3;
            let sum = if i + 1 == w {
                let xy = g.xor_phase(x, y);
                g.xor_phase(xy, z)
            } else {
                let xy = g.xor(x, y);
                g.xor(xy, z)
            };
            if sum != FALSE {
                columns[i].push(sum);
            }
            if i + 1 < w {
                let carry = g.maj(x, y, z);
                if carry != FALSE {
                    columns[i + 1].push(carry);
                }
            }
        }
        if let Some(&l) = columns[i].get(head) {
            first[i] = l;
        }
        if let Some(&l) = columns[i].get(head + 1) {
            second[i] = l;
        }
    }
    add(g, &first, &second)
}

/// Quotient and remainder of unsigned division; by zero, all ones and `a` (restoring division
/// gives exactly that).
pub fn udivrem(g: &mut Aig, a: &[L], b: &[L]) -> (Bits, Bits) {
    let w = a.len();
    let mut r: Bits = vec![FALSE; w + 1];
    let mut bw = b.to_vec();
    bw.push(FALSE);
    let mut q = vec![FALSE; w];
    for i in (0..w).rev() {
        // r = r·2 + a_i (w + 1 bits suffice: r < b ≤ 2^w − 1 before the shift).
        let mut shifted = vec![a[i]];
        shifted.extend_from_slice(&r[..w]);
        let ge = ult(g, &shifted, &bw) ^ 1;
        let diff = sub(g, &shifted, &bw);
        r = mux(g, ge, &diff, &shifted);
        q[i] = ge;
    }
    r.truncate(w);
    (q, r)
}

/// `|a|` and whether `a` is negative.
fn abs(g: &mut Aig, a: &[L]) -> (Bits, L) {
    let s = *a.last().unwrap_or(&FALSE);
    let n = neg(g, a);
    (mux(g, s, &n, a), s)
}

/// Signed division truncating toward zero, SMT-LIB's (by zero: 1 for a negative dividend, −1
/// otherwise).
pub fn sdiv(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    let (ua, sa) = abs(g, a);
    let (ub, sb) = abs(g, b);
    let (q, _) = udivrem(g, &ua, &ub);
    let differ = g.xor(sa, sb);
    let nq = neg(g, &q);
    mux(g, differ, &nq, &q)
}

/// Signed remainder with the dividend's sign (by zero: the dividend).
pub fn srem(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    let (ua, sa) = abs(g, a);
    let (ub, _) = abs(g, b);
    let (_, r) = udivrem(g, &ua, &ub);
    let nr = neg(g, &r);
    mux(g, sa, &nr, &r)
}

/// Whether the count `s` is at least `w` (as an unsigned number).
fn at_least(g: &mut Aig, s: &[L], w: usize) -> L {
    let k = small(s.len(), w as u64);
    if s.len() < 64 && (w as u64) >> s.len() != 0 {
        return FALSE;
    }
    ult(g, s, &k) ^ 1
}

/// A shift by a variable count: `fill` for bits shifted in (`FALSE`, or the sign), `left` for
/// the direction. Counts of at least `w` give all fill.
pub fn shift(g: &mut Aig, a: &[L], s: &[L], left: bool, fill: L) -> Bits {
    let w = a.len();
    let mut cur = a.to_vec();
    let mut k = 0;
    while (1usize << k) < w && k < s.len() {
        let amt = 1usize << k;
        let moved: Bits = (0..w)
            .map(|i| {
                if left {
                    if i >= amt { cur[i - amt] } else { FALSE }
                } else if i + amt < w {
                    cur[i + amt]
                } else {
                    fill
                }
            })
            .collect();
        cur = mux(g, s[k], &moved, &cur);
        k += 1;
    }
    let over = at_least(g, s, w);
    let all = vec![if left { FALSE } else { fill }; w];
    let mut result = mux(g, over, &all, &cur);
    fold_shift_correlations(a, s, left, fill, &mut result);
    result
}

// A small shift count can share literals with the shifted word. Enumerate only the count's
// Boolean support, treating all other data bits as opaque: fold an output only when every
// count assignment makes it a constant or one of those literals. In particular, the high
// bits of (x >> j) >> (x >> m) can be zero even though a plain barrel shifter misses this.
fn fold_shift_correlations(a: &[L], s: &[L], left: bool, fill: L, result: &mut Bits) {
    let mut selectors = [FALSE; 4];
    let mut len = 0;
    for &l in s.iter().filter(|&&l| l > TRUE) {
        let base = l & !1;
        if !selectors[..len].contains(&base) {
            if len == selectors.len() {
                return;
            }
            selectors[len] = base;
            len += 1;
        }
    }
    if len == 0
        || !a
            .iter()
            .chain(core::iter::once(&fill))
            .any(|&l| l > TRUE && selectors[..len].contains(&(l & !1)))
    {
        return;
    }
    let value = |l: L, assignment: usize| -> Option<bool> {
        if l <= TRUE {
            return Some(l == TRUE);
        }
        let bit = selectors[..len].iter().position(|&s| s == l & !1)?;
        Some((assignment >> bit & 1 == 1) ^ (l & 1 != 0))
    };
    let assignments = 1usize << len;
    let mut counts = [0usize; 16];
    for (assignment, count) in counts.iter_mut().enumerate().take(assignments) {
        for (bit, &l) in s.iter().enumerate() {
            if value(l, assignment) == Some(true) {
                if bit >= usize::BITS as usize || (1usize << bit) >= a.len() {
                    *count = a.len();
                    break;
                }
                *count |= 1usize << bit;
            }
        }
    }
    let all = (1u32 << assignments) - 1;
    for (bit, output) in result.iter_mut().enumerate() {
        let mut table = 0u32;
        let mut complete = true;
        for (assignment, &count) in counts.iter().enumerate().take(assignments) {
            let source = if left {
                bit.checked_sub(count).map_or(FALSE, |i| a[i])
            } else {
                a.get(bit + count).copied().unwrap_or(fill)
            };
            let Some(v) = value(source, assignment) else {
                complete = false;
                break;
            };
            table |= u32::from(v) << assignment;
        }
        if !complete {
            continue;
        }
        if table == 0 || table == all {
            *output = if table == 0 { FALSE } else { TRUE };
        } else {
            for (i, &selector) in selectors.iter().enumerate().take(len) {
                let positive =
                    (0..assignments).fold(0u32, |mask, j| mask | (u32::from(j >> i & 1 == 1) << j));
                if table == positive || table == positive ^ all {
                    *output = selector ^ u32::from(table != positive);
                    break;
                }
            }
        }
    }
}

/// A rotation by `s mod w`.
pub fn rotate(g: &mut Aig, a: &[L], s: &[L], left: bool) -> Bits {
    let w = a.len();
    if w <= 1 {
        return a.to_vec();
    }
    // The count modulo w.
    let r = if w.is_power_of_two() {
        let k = w.trailing_zeros() as usize;
        let mut r: Bits = s.iter().copied().take(k).collect();
        r.resize(k.max(1), FALSE);
        r
    } else {
        // Maintain an accumulator in `[0, w)` of `bw + 1` bits (`w < 2^bw`, so `acc + term < 2w < 2^(bw+1)`).
        let bw = (usize::BITS - w.leading_zeros()) as usize;
        let wk = small(bw + 1, w as u64);
        let mut acc = vec![FALSE; bw + 1];
        let mut weight = 1u64 % (w as u64);
        for &si in s {
            if si != FALSE && weight != 0 {
                let term: Bits = (0..bw + 1)
                    .map(|j| if (weight >> j) & 1 == 1 { si } else { FALSE })
                    .collect();
                let sum = add(g, &acc, &term);
                let ge = ult(g, &sum, &wk) ^ 1;
                let diff = sub(g, &sum, &wk);
                acc = mux(g, ge, &diff, &sum);
            }
            weight = (weight * 2) % (w as u64);
        }
        acc.truncate(bw);
        acc
    };
    let mut cur = a.to_vec();
    for (k, &bit) in r.iter().enumerate() {
        if k >= 64 || (1u64 << k) as usize >= w {
            break;
        }
        let amt = (1usize << k) % w;
        if amt == 0 || bit == FALSE {
            continue;
        }
        let moved: Bits = (0..w)
            .map(|i| {
                if left {
                    cur[(i + w - amt) % w]
                } else {
                    cur[(i + amt) % w]
                }
            })
            .collect();
        cur = mux(g, bit, &moved, &cur);
    }
    cur
}

/// The number of set bits of `bits`, in `w` bits.
pub fn count(g: &mut Aig, bits: &[L], w: usize) -> Bits {
    // An adder tree over the single bits.
    let mut vals: Vec<Bits> = bits
        .iter()
        .map(|&b| {
            let mut v = vec![FALSE; w];
            if w > 0 {
                v[0] = b;
            }
            v
        })
        .collect();
    if vals.is_empty() {
        return vec![FALSE; w];
    }
    while vals.len() > 1 {
        let mut next = Vec::with_capacity(vals.len().div_ceil(2));
        for pair in vals.chunks(2) {
            next.push(if pair.len() == 2 {
                add(g, &pair[0], &pair[1])
            } else {
                pair[0].clone()
            });
        }
        vals = next;
    }
    vals.pop().unwrap_or_default()
}

pub fn popcnt(g: &mut Aig, a: &[L]) -> Bits {
    count(g, a, a.len())
}

/// Leading zeros: the number of prefixes (from the top) that are all zero.
pub fn clz(g: &mut Aig, a: &[L]) -> Bits {
    let mut flags = Vec::with_capacity(a.len());
    let mut all_zero = TRUE;
    for &b in a.iter().rev() {
        all_zero = g.and(all_zero, b ^ 1);
        flags.push(all_zero);
    }
    count(g, &flags, a.len())
}

pub fn ctz(g: &mut Aig, a: &[L]) -> Bits {
    let mut flags = Vec::with_capacity(a.len());
    let mut all_zero = TRUE;
    for &b in a {
        all_zero = g.and(all_zero, b ^ 1);
        flags.push(all_zero);
    }
    count(g, &flags, a.len())
}

pub fn bswap(a: &[L]) -> Bits {
    let w = a.len();
    (0..w).map(|k| a[(w / 8 - 1 - k / 8) * 8 + k % 8]).collect()
}

pub fn bitrev(a: &[L]) -> Bits {
    a.iter().rev().copied().collect()
}

/// The high half of the full product (sign or zero extended to twice the width).
pub fn mulhi(g: &mut Aig, a: &[L], b: &[L], signed: bool) -> Bits {
    mulhi_impl(g, a, b, signed, false)
}

/// [`mulhi`], compressing columns before one final carry-propagating addition.
pub fn mulhi_carry_save(g: &mut Aig, a: &[L], b: &[L], signed: bool) -> Bits {
    mulhi_impl(g, a, b, signed, true)
}

fn mulhi_impl(g: &mut Aig, a: &[L], b: &[L], signed: bool, carry_save: bool) -> Bits {
    let w = a.len();
    if w <= 1 {
        // For w = 1: unsigned 1 * 1 = 1 (high bit 0), signed (-1) * (-1) = +1 = 0b01 (high bit 0).
        return vec![FALSE; w];
    }
    // Unsigned multiplication by a constant benefits from signed-digit recoding at width 2w.
    if !signed && (a.iter().all(|&l| l <= TRUE) || b.iter().all(|&l| l <= TRUE)) {
        let mut a2 = a.to_vec();
        let mut b2 = b.to_vec();
        a2.resize(2 * w, FALSE);
        b2.resize(2 * w, FALSE);
        let p = if carry_save {
            mul_carry_save(g, &a2, &b2)
        } else {
            mul(g, &a2, &b2)
        };
        return p[w..].to_vec();
    }
    // Exact w × w partial-product array (Baugh–Wooley for signed): w² AND gates instead of 4w².
    let tw = 2 * w;
    if carry_save {
        let mut columns = vec![Vec::new(); tw];
        if signed {
            columns[w].push(TRUE);
            columns[tw - 1].push(TRUE);
        }
        for (j, &bj) in b.iter().enumerate() {
            for (i, &ai) in a.iter().enumerate() {
                let neg_term = signed && ((i == w - 1) != (j == w - 1));
                let pp = g.and(ai, bj) ^ u32::from(neg_term);
                if pp != FALSE {
                    columns[i + j].push(pp);
                }
            }
        }
        let mut first = vec![FALSE; tw];
        let mut second = vec![FALSE; tw];
        for i in 0..tw {
            let mut head = 0;
            while columns[i].len() - head > 2 {
                let (x, y, z) = (columns[i][head], columns[i][head + 1], columns[i][head + 2]);
                head += 3;
                let sum = if i + 1 == tw {
                    let xy = g.xor_phase(x, y);
                    g.xor_phase(xy, z)
                } else {
                    let xy = g.xor(x, y);
                    g.xor(xy, z)
                };
                if sum != FALSE {
                    columns[i].push(sum);
                }
                if i + 1 < tw {
                    let carry = g.maj(x, y, z);
                    if carry != FALSE {
                        columns[i + 1].push(carry);
                    }
                }
            }
            if let Some(&l) = columns[i].get(head) {
                first[i] = l;
            }
            if let Some(&l) = columns[i].get(head + 1) {
                second[i] = l;
            }
        }
        let p = add(g, &first, &second);
        return p[w..].to_vec();
    }
    let mut acc = vec![FALSE; tw];
    if signed {
        acc[w] = TRUE;
        acc[tw - 1] = TRUE;
    }
    for (j, &bj) in b.iter().enumerate() {
        if !signed && bj == FALSE {
            continue;
        }
        let mut part = vec![FALSE; tw];
        let mut any = false;
        for (i, &ai) in a.iter().enumerate() {
            let neg_term = signed && ((i == w - 1) != (j == w - 1));
            let pp = g.and(ai, bj) ^ u32::from(neg_term);
            part[i + j] = pp;
            any |= pp != FALSE;
        }
        if any {
            acc = add(g, &acc, &part);
        }
    }
    acc[w..].to_vec()
}

/// Advances the one-hot popcount state `oh` (`oh[j]` holds iff `c_i == j`) by bit `mi`.
fn step_onehot(g: &mut Aig, oh: &mut Vec<L>, mi: L, max_len: usize) {
    if mi == FALSE {
        return;
    }
    if mi == TRUE {
        if oh.len() < max_len {
            oh.insert(0, FALSE);
        } else {
            oh.rotate_right(1);
            oh[0] = FALSE;
        }
        return;
    }
    let old_len = oh.len();
    if old_len < max_len {
        let top = g.and(mi, oh[old_len - 1]);
        oh.push(top);
    }
    for j in (1..old_len).rev() {
        oh[j] = g.mux(mi, oh[j - 1], oh[j]);
    }
    oh[0] = g.and(oh[0], mi ^ 1);
}

/// Parallel bit deposit: bit `i` of the result is `m_i ∧ x_{c_i}`, `c_i` the number of set bits
/// of `m` below `i`.
pub fn pdep(g: &mut Aig, x: &[L], m: &[L]) -> Bits {
    let w = x.len();
    let mut out = Vec::with_capacity(w);
    let mut oh = Vec::with_capacity(w);
    if w > 0 {
        oh.push(TRUE);
    }
    for (i, &mi) in m.iter().take(w).enumerate() {
        if mi == FALSE {
            out.push(FALSE);
            continue;
        }
        let mut pick = FALSE;
        for (j, &at) in oh.iter().enumerate() {
            let t = g.and(at, x[j]);
            pick = g.or(pick, t);
        }
        out.push(g.and(mi, pick));
        if i + 1 < w {
            step_onehot(g, &mut oh, mi, w);
        }
    }
    out
}

/// Parallel bit extract: bit `j` of the result is the OR over `i` of `x_i ∧ m_i ∧ (c_i = j)`.
pub fn pext(g: &mut Aig, x: &[L], m: &[L]) -> Bits {
    let w = x.len();
    let mut out = vec![FALSE; w];
    let mut oh = Vec::with_capacity(w);
    if w > 0 {
        oh.push(TRUE);
    }
    for i in 0..w {
        let mi = m[i];
        if mi == FALSE {
            continue;
        }
        let src = g.and(x[i], mi);
        if src != FALSE {
            for (j, &at) in oh.iter().enumerate() {
                let t = g.and(at, src);
                out[j] = g.or(out[j], t);
            }
        }
        if i + 1 < w {
            step_onehot(g, &mut oh, mi, w);
        }
    }
    out
}

#[cfg(test)]
#[path = "tests/constant_factors.rs"]
mod constant_factors_tests;

//! Bit classes: the bit positions that every constant read by a bitwise operator treats alike.
//!
//! Two positions `j` and `j'` are in one class when every such constant has the same bit at
//! both. Inside a class every bitwise subterm applies one Boolean function at every position,
//! so a bitwise function of atoms is a truth table per class, and a linear combination of
//! bitwise functions is a combination of *masked conjunctions* `AND_S & M_c` (design §9). The
//! constants 0 and all-ones never split a class.

use crate::{BitVec, Width};

/// The class of an unmasked symbol: every position (`AND_S` itself, the sum of its masked
/// symbols over all classes).
pub(crate) const FULL: u16 = u16::MAX;

/// The partition of the positions of a width into classes, ordered by lowest position.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Classes {
    width: Width,
    /// All-ones (the mask of [`FULL`]).
    ones: BitVec,
    /// Per class: its positions.
    masks: Vec<BitVec>,
    /// Per class: its lowest position (`τ_c`).
    low: Vec<u16>,
    /// Per class: its only position, if it has one.
    single: Vec<Option<u16>>,
}

impl Classes {
    /// The classes of `consts` at `width`: `None` when there would be more than `max`, or more
    /// than 64 distinct constants that split positions.
    pub(crate) fn new(width: Width, consts: &[BitVec], max: usize) -> Option<Classes> {
        let mut splitting: Vec<BitVec> = consts
            .iter()
            .filter(|c| !c.is_zero() && !c.is_ones())
            .map(|c| BitVec::wrapping_from_limbs(width, c.limbs()))
            .collect();
        splitting.sort();
        splitting.dedup();
        if splitting.len() > 64 {
            return None;
        }
        let bits = usize::from(width.bits());
        let mut keys: Vec<u64> = Vec::new();
        let mut members: Vec<Vec<u16>> = Vec::new();
        for j in 0..bits {
            let key = splitting.iter().enumerate().fold(0u64, |k, (i, c)| {
                k | u64::from(c.bit(j as u16).unwrap_or(false)) << i
            });
            let c = match keys.iter().position(|&k| k == key) {
                Some(c) => c,
                None => {
                    keys.push(key);
                    members.push(Vec::new());
                    if keys.len() > max.max(1) {
                        return None;
                    }
                    keys.len() - 1
                }
            };
            members[c].push(j as u16);
        }
        let masks = members
            .iter()
            .map(|ps| {
                let mut limbs = [0u64; 8];
                for &j in ps {
                    limbs[usize::from(j / 64)] |= 1u64 << (j % 64);
                }
                BitVec::wrapping_from_limbs(width, &limbs)
            })
            .collect();
        Some(Classes {
            width,
            ones: BitVec::ones(width),
            masks,
            low: members.iter().map(|ps| ps[0]).collect(),
            single: members
                .iter()
                .map(|ps| (ps.len() == 1).then_some(ps[0]))
                .collect(),
        })
    }

    pub(crate) fn width(&self) -> Width {
        self.width
    }

    /// The number of classes.
    pub(crate) fn len(&self) -> usize {
        self.masks.len()
    }

    /// The positions of class `c` (all of them for [`FULL`]).
    pub(crate) fn mask(&self, c: usize) -> &BitVec {
        self.masks.get(c).unwrap_or(&self.ones)
    }

    /// The lowest position of class `c`: its symbols are multiples of `2^low`.
    pub(crate) fn low(&self, c: usize) -> u16 {
        self.low.get(c).copied().unwrap_or(0)
    }

    /// The only position of class `c`, if it has one (then `m² = 2^j·m` for its symbols).
    pub(crate) fn single(&self, c: usize) -> Option<u16> {
        match self.single.get(c) {
            Some(s) => *s,
            None => (self.width.bits() == 1).then_some(0),
        }
    }

    /// The bit constant `v` has throughout class `c`: `None` when it differs inside the class.
    pub(crate) fn bit(&self, v: &BitVec, c: usize) -> Option<bool> {
        let v = BitVec::wrapping_from_limbs(self.width, v.limbs());
        let m = &self.masks[c];
        let inside = crate::facts::known::bv_and(&v, m);
        if inside.is_zero() {
            Some(false)
        } else if inside == *m {
            Some(true)
        } else {
            None
        }
    }
}

//! The in-crate hash function.
//!
//! Structural hashes of expressions are part of the output-stability contract: the canonical
//! operand order (and therefore printed output) is derived from them. The mixer is therefore
//! specified here and versioned, never taken from a dependency whose output may change.

use core::hash::{BuildHasher, Hasher};

/// Version of the structural hash. Bumped whenever [`mix64`] or [`combine`] change.
#[allow(dead_code)]
pub(crate) const HASH_VERSION: u32 = 1;

/// The SplitMix64 finalizer: a bijective avalanche mix of one word.
#[inline]
pub(crate) const fn mix64(mut z: u64) -> u64 {
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// Folds `v` into the running hash `h`.
#[inline]
pub(crate) const fn combine(h: u64, v: u64) -> u64 {
    mix64(h.rotate_left(23) ^ v.wrapping_add(0x9e37_79b9_7f4a_7c15))
}

/// Hash of a byte string.
pub(crate) fn bytes(seed: u64, b: &[u8]) -> u64 {
    let mut h = combine(seed, b.len() as u64);
    for chunk in b.chunks(8) {
        let mut w = [0u8; 8];
        w[..chunk.len()].copy_from_slice(chunk);
        h = combine(h, u64::from_le_bytes(w));
    }
    h
}

/// A fast hasher for small integer keys (node indices) in internal side tables. Its output
/// never influences any result: it only lays out lookup tables.
#[derive(Default, Clone, Copy, Debug)]
pub(crate) struct IdHasher(u64);

impl Hasher for IdHasher {
    #[inline]
    fn finish(&self) -> u64 {
        mix64(self.0)
    }
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        self.0 = self::bytes(self.0, bytes);
    }
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.0 = combine(self.0, u64::from(i));
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.0 = combine(self.0, i);
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.0 = combine(self.0, i as u64);
    }
}

/// [`BuildHasher`] for [`IdHasher`].
#[derive(Default, Clone, Copy, Debug)]
pub(crate) struct IdBuild;

impl BuildHasher for IdBuild {
    type Hasher = IdHasher;
    #[inline]
    fn build_hasher(&self) -> IdHasher {
        IdHasher(0)
    }
}

/// A `HashMap` keyed by node indices or other small integers.
pub(crate) type IdMap<K, V> = std::collections::HashMap<K, V, IdBuild>;

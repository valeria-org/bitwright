//! A small index from hashes to entries kept elsewhere (the synthesis table's values, a
//! builder's nodes): open addressing with linear probing over slots of a hash and an entry's
//! number. The entries themselves stay with the caller, who says which of the entries with a
//! hash is meant and never adds one the index already has; so a slot is sixteen bytes
//! whatever an entry is, and growing moves slots without hashing anything again.

/// Entries by hash (see the module).
#[derive(Clone, Debug)]
pub(crate) struct Index {
    slots: Vec<(u64, u32)>,
    len: usize,
}

/// An empty slot.
const FREE: u32 = u32::MAX;

impl Index {
    /// An index with room for `n` entries before it grows.
    pub(crate) fn with_capacity(n: usize) -> Index {
        Index {
            slots: vec![(0, FREE); (2 * n).next_power_of_two().max(16)],
            len: 0,
        }
    }

    /// The number of entries.
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.len
    }

    /// The entry with hash `h` that `is` accepts.
    #[inline]
    pub(crate) fn find(&self, h: u64, is: impl Fn(u32) -> bool) -> Option<u32> {
        let mask = self.slots.len() - 1;
        let mut at = h as usize & mask;
        loop {
            let (g, i) = self.slots[at];
            if i == FREE {
                return None;
            }
            if g == h && is(i) {
                return Some(i);
            }
            at = (at + 1) & mask;
        }
    }

    /// Adds entry `i` (below `u32::MAX`) with hash `h`.
    pub(crate) fn insert(&mut self, h: u64, i: u32) {
        if 2 * (self.len + 1) > self.slots.len() {
            let old = core::mem::take(&mut self.slots);
            self.slots = vec![(0, FREE); 2 * old.len()];
            for (g, j) in old {
                if j != FREE {
                    self.place(g, j);
                }
            }
        }
        self.place(h, i);
        self.len += 1;
    }

    fn place(&mut self, h: u64, i: u32) {
        let mask = self.slots.len() - 1;
        let mut at = h as usize & mask;
        while self.slots[at].1 != FREE {
            at = (at + 1) & mask;
        }
        self.slots[at] = (h, i);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn entries_are_found_by_hash_and_identity_through_growth() {
        // Entries 0..n with clashing hashes (four entries per hash).
        let hash = |i: u32| u64::from(i / 4).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        let mut ix = Index::with_capacity(0);
        for i in 0..1000u32 {
            assert_eq!(ix.find(hash(i), |j| j == i), None);
            ix.insert(hash(i), i);
            assert_eq!(ix.len(), i as usize + 1);
        }
        for i in 0..1000u32 {
            assert_eq!(ix.find(hash(i), |j| j == i), Some(i));
            assert_eq!(ix.find(hash(i), |_| false), None);
        }
        assert_eq!(ix.find(hash(4000), |_| true), None);
    }
}

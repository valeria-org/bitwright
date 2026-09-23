//! A compact per-node cache for the linear and xor passes' forms: a constant and terms, each an
//! atom with a coefficient (a mask, for xor). A `BitVec` takes 72 bytes whatever its width, so a
//! form of width up to 64 keeps its constant and coefficients as words, the terms in one arena
//! (16 bytes a term instead of 80); a wider form is kept whole. A read rebuilds the same form.

use super::Fin;
use crate::hash::IdMap;
use crate::{BitVec, Width};

/// A form's parts: its constant, its terms in order, and its finality.
pub(crate) trait Parts: Clone {
    fn parts(&self) -> (&BitVec, &[(u32, BitVec)], Fin);
    fn from_parts(konst: BitVec, terms: Vec<(u32, BitVec)>, fin: Fin) -> Self;
}

enum Entry<F> {
    /// Width up to 64; the terms are `arena[start..start + len]`.
    Narrow {
        konst: u64,
        start: usize,
        len: u32,
        width: Width,
        fin: Fin,
    },
    Wide(Box<F>),
}

/// Forms per node.
pub(crate) struct FormCache<F> {
    map: IdMap<u32, Entry<F>>,
    arena: Vec<(u32, u64)>,
}

impl<F> Default for FormCache<F> {
    fn default() -> Self {
        FormCache {
            map: IdMap::default(),
            arena: Vec::new(),
        }
    }
}

impl<F: Parts> FormCache<F> {
    pub(super) fn contains(&self, i: u32) -> bool {
        self.map.contains_key(&i)
    }

    pub(super) fn insert(&mut self, i: u32, f: F) {
        let (konst, terms, fin) = f.parts();
        let width = konst.width();
        let e = if width.bits() <= 64 {
            let start = self.arena.len();
            self.arena
                .extend(terms.iter().map(|(a, c)| (*a, c.limbs()[0])));
            Entry::Narrow {
                konst: konst.limbs()[0],
                start,
                len: terms.len() as u32,
                width,
                fin,
            }
        } else {
            Entry::Wide(Box::new(f))
        };
        self.map.insert(i, e);
    }

    /// The form of node `i`, if cached.
    pub(super) fn get(&self, i: u32) -> Option<F> {
        Some(match self.map.get(&i)? {
            &Entry::Narrow {
                konst,
                start,
                len,
                width,
                fin,
            } => {
                let v = |x: u64| BitVec::from_canonical_u64(width, x);
                let terms = self.arena[start..start + len as usize]
                    .iter()
                    .map(|&(a, c)| (a, v(c)))
                    .collect();
                F::from_parts(v(konst), terms, fin)
            }
            Entry::Wide(f) => (**f).clone(),
        })
    }
}

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

// Work in progress from here down: sums over a pass's cap on terms, so that terms cancel
// through them. Nothing reads it yet (hence the `allow`s); the pull request's handoff says how
// the linear and xor passes are to use it.

/// The terms of a cached form.
#[allow(dead_code)]
enum Terms<'a> {
    Narrow(&'a [(u32, u64)]),
    Wide(&'a [(u32, BitVec)]),
}

#[allow(dead_code)]
impl Terms<'_> {
    fn len(&self) -> usize {
        match self {
            Terms::Narrow(t) => t.len(),
            Terms::Wide(t) => t.len(),
        }
    }

    fn atom(&self, k: usize) -> u32 {
        match self {
            Terms::Narrow(t) => t[k].0,
            Terms::Wide(t) => t[k].0,
        }
    }

    /// Whether `atom` is among the terms (they are sorted by atom).
    fn has(&self, atom: u32) -> bool {
        let (mut lo, mut hi) = (0, self.len());
        while lo < hi {
            let mid = (lo + hi) / 2;
            match self.atom(mid).cmp(&atom) {
                std::cmp::Ordering::Equal => return true,
                std::cmp::Ordering::Less => lo = mid + 1,
                std::cmp::Ordering::Greater => hi = mid,
            }
        }
        false
    }
}

#[allow(dead_code)]
impl<F: Parts> FormCache<F> {
    fn terms(&self, i: u32) -> Option<Terms<'_>> {
        Some(match self.map.get(&i)? {
            &Entry::Narrow { start, len, .. } => {
                Terms::Narrow(&self.arena[start..start + len as usize])
            }
            Entry::Wide(f) => Terms::Wide(f.parts().1),
        })
    }
}

/// How a pass's forms add up.
#[allow(dead_code)]
pub(crate) trait Sum: Parts {
    /// The coefficient of an atom two summands give the coefficients `a` and `b`.
    fn join(a: &BitVec, b: &BitVec) -> BitVec;
    /// The coefficient of an atom with the coefficient `inner` in a sum that has the
    /// coefficient `outer` (the constant of that sum is scaled the same way).
    fn scale(outer: &BitVec, inner: &BitVec) -> BitVec;
}

/// The most terms of a whole form.
#[allow(dead_code)]
pub(crate) const MAX_WHOLE_TERMS: usize = 1024;

/// The sums over a pass's cap on terms. Such a sum is an atom of the forms over it, which keeps
/// every node's form small, and so a term over it cannot meet a term inside it. Each one keeps
/// its *whole* form here: its terms with the sums over the cap among their atoms taken apart in
/// turn, up to [`MAX_WHOLE_TERMS`] terms (a larger one keeps none, and is an atom and no more).
/// A sum of two forms looks into these for terms that meet out of sight, and only then is
/// taken apart: a sum in which nothing meets costs what it did.
#[allow(dead_code)]
pub(crate) struct Whole<F> {
    forms: FormCache<F>,
    /// The sums over the cap in which terms met: the pass writes these out again.
    met: IdMap<u32, ()>,
}

impl<F> Default for Whole<F> {
    fn default() -> Self {
        Whole {
            forms: FormCache::default(),
            met: IdMap::default(),
        }
    }
}

#[allow(dead_code)]
impl<F: Sum> Whole<F> {
    /// The atoms of `form` that have a whole form.
    fn over(&self, form: &F) -> Vec<u32> {
        if self.forms.map.is_empty() {
            return Vec::new();
        }
        let atoms = form.parts().1.iter().map(|t| t.0);
        atoms.filter(|&a| self.forms.contains(a)).collect()
    }

    /// Whether some atom of `form` has a whole form.
    pub(super) fn any(&self, form: &F) -> bool {
        !self.over(form).is_empty()
    }

    /// Whether a term of one of `a` and `b` meets a term inside a sum over the cap of the
    /// other: `a + b` then has terms its form does not show together.
    pub(super) fn meet(&self, a: &F, b: &F) -> bool {
        let (oa, ob) = (self.over(a), self.over(b));
        if oa.is_empty() && ob.is_empty() {
            return false;
        }
        let inside = |over: &[u32], other: &F| {
            over.iter().any(|&o| {
                let terms = self.forms.terms(o).expect("it has a whole form");
                other.parts().1.iter().any(|t| terms.has(t.0))
            })
        };
        let shared = |o: u32, p: u32| {
            let (s, t) = (
                self.forms.terms(o).expect("it has a whole form"),
                self.forms.terms(p).expect("it has a whole form"),
            );
            let (mut i, mut j) = (0, 0);
            while i < s.len() && j < t.len() {
                match s.atom(i).cmp(&t.atom(j)) {
                    std::cmp::Ordering::Equal => return true,
                    std::cmp::Ordering::Less => i += 1,
                    std::cmp::Ordering::Greater => j += 1,
                }
            }
            false
        };
        // One sum in both operands meets itself in the forms' own sum.
        inside(&oa, b)
            || inside(&ob, a)
            || oa
                .iter()
                .any(|&o| ob.iter().any(|&p| o != p && shared(o, p)))
    }

    /// The terms taking `form` apart reads: what [`Whole::expand`] costs.
    pub(super) fn weight(&self, form: &F) -> u64 {
        let inside = |a: u32| self.forms.terms(a).map_or(1, |t| t.len() as u64);
        form.parts().1.iter().map(|t| inside(t.0)).sum()
    }

    /// `form` with every sum over the cap among its atoms taken apart (one level is all: a
    /// whole form has none), or `None` when that is over [`MAX_WHOLE_TERMS`] terms.
    pub(super) fn expand(&self, form: &F) -> Option<F> {
        let (konst, terms, fin) = form.parts();
        let (mut konst, mut fin) = (*konst, fin);
        let mut all: Vec<(u32, BitVec)> = Vec::new();
        for &(a, k) in terms {
            match self.forms.get(a) {
                Some(inner) => {
                    let (c, inside, f) = inner.parts();
                    if all.len() + inside.len() > 2 * MAX_WHOLE_TERMS {
                        return None;
                    }
                    konst = F::join(&konst, &F::scale(&k, c));
                    all.extend(inside.iter().map(|(x, c)| (*x, F::scale(&k, c))));
                    fin = fin.and(f);
                }
                None => all.push((a, k)),
            }
        }
        all.sort_by_key(|t| t.0);
        let mut out: Vec<(u32, BitVec)> = Vec::with_capacity(all.len());
        for (a, k) in all {
            match out.last_mut() {
                Some(last) if last.0 == a => last.1 = F::join(&last.1, &k),
                _ => out.push((a, k)),
            }
        }
        out.retain(|t| !t.1.is_zero());
        (out.len() <= MAX_WHOLE_TERMS).then(|| F::from_parts(konst, out, fin))
    }

    /// Keeps `whole` as the whole form of the sum `i` over the cap; terms `met` in it.
    pub(super) fn insert(&mut self, i: u32, whole: F, met: bool) {
        self.forms.insert(i, whole);
        if met {
            self.met.insert(i, ());
        }
    }

    /// The whole form of `i`, when `i` is a sum over the cap in which terms met.
    pub(super) fn met(&self, i: u32) -> Option<F> {
        self.met.get(&i).and_then(|()| self.forms.get(i))
    }
}

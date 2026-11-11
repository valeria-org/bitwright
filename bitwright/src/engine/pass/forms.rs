//! A compact per-node cache for the linear and xor passes' forms: a constant and terms, each an
//! atom with a coefficient (a mask, for xor). A `BitVec` takes 72 bytes whatever its width, so a
//! form of width up to 64 keeps its constant and coefficients as words, the terms in one arena
//! (16 bytes a term instead of 80); a wider form is kept whole. A read rebuilds the same form.
//! And the sums over a pass's cap on terms, each with all of its terms ([`Whole`]).

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

/// The terms of a cached form, as it keeps them.
enum Terms<'a> {
    Narrow(&'a [(u32, u64)], Width),
    Wide(&'a [(u32, BitVec)]),
}

impl Terms<'_> {
    fn len(&self) -> usize {
        match self {
            Terms::Narrow(t, _) => t.len(),
            Terms::Wide(t) => t.len(),
        }
    }

    fn atom(&self, k: usize) -> u32 {
        match self {
            Terms::Narrow(t, _) => t[k].0,
            Terms::Wide(t) => t[k].0,
        }
    }

    fn get(&self, k: usize) -> (u32, BitVec) {
        match self {
            Terms::Narrow(t, w) => (t[k].0, BitVec::from_canonical_u64(*w, t[k].1)),
            Terms::Wide(t) => t[k],
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

impl<F: Parts> FormCache<F> {
    /// The parts of the form of node `i`, if cached, read where they are kept.
    fn parts_of(&self, i: u32) -> Option<(BitVec, Terms<'_>, Fin)> {
        Some(match self.map.get(&i)? {
            &Entry::Narrow {
                konst,
                start,
                len,
                width,
                fin,
            } => (
                BitVec::from_canonical_u64(width, konst),
                Terms::Narrow(&self.arena[start..start + len as usize], width),
                fin,
            ),
            Entry::Wide(f) => {
                let (konst, terms, fin) = f.parts();
                (*konst, Terms::Wide(terms), fin)
            }
        })
    }
}

/// How a pass's forms add up.
pub(crate) trait Sum: Parts {
    /// The coefficient of an atom two summands give the coefficients `a` and `b`.
    fn join(a: &BitVec, b: &BitVec) -> BitVec;
    /// The coefficient of an atom with the coefficient `inner` in a sum that has the
    /// coefficient `outer` (the constant of that sum is scaled the same way).
    fn scale(outer: &BitVec, inner: &BitVec) -> BitVec;
}

/// The most terms of a whole form.
pub(crate) const MAX_WHOLE_TERMS: usize = 1024;

/// The sums over a pass's cap on terms. Such a sum is an atom of the forms over it, which keeps
/// every node's form small, and so a term over it cannot meet a term inside it. Each one keeps
/// its *whole* form here: its terms with the sums over the cap among their atoms taken apart in
/// turn, up to [`MAX_WHOLE_TERMS`] terms (a larger one keeps none, and is an atom and no more).
/// A sum of two forms looks into these for terms that meet out of sight, and only then is
/// taken apart: a sum in which nothing meets costs what it did.
///
/// What a method reads of whole forms it adds to its `read`, in terms: the pass charges a unit
/// of its work per as many terms as a form has at most (what it charges a node for its form).
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

impl<F: Sum> Whole<F> {
    /// The atoms of `form` that have a whole form.
    fn over(&self, form: &F) -> Vec<u32> {
        if self.forms.map.is_empty() {
            return Vec::new();
        }
        let atoms = form.parts().1.iter().map(|t| t.0);
        atoms.filter(|&a| self.forms.contains(a)).collect()
    }

    /// `form` with every sum over the cap among its atoms taken apart (one level is all: a
    /// whole form has none), and whether two of the terms that gives were of one atom; `None`
    /// when it is over [`MAX_WHOLE_TERMS`] terms, or twice that before they are put together.
    fn expand(&self, form: &F, read: &mut u64) -> Option<(F, bool)> {
        let (konst, terms, fin) = form.parts();
        let (mut konst, mut fin) = (*konst, fin);
        let mut all: Vec<(u32, BitVec)> = Vec::with_capacity(terms.len());
        for &(a, k) in terms {
            let Some((c, inside, f)) = self.forms.parts_of(a) else {
                all.push((a, k));
                continue;
            };
            if all.len() + inside.len() > 2 * MAX_WHOLE_TERMS {
                *read += all.len() as u64;
                return None;
            }
            konst = F::join(&konst, &F::scale(&k, &c));
            all.extend((0..inside.len()).map(|j| {
                let (x, c) = inside.get(j);
                (x, F::scale(&k, &c))
            }));
            fin = fin.and(f);
        }
        *read += all.len() as u64;
        all.sort_unstable_by_key(|t| t.0);
        let mut met = false;
        let mut out: Vec<(u32, BitVec)> = Vec::with_capacity(all.len());
        for (a, k) in all {
            match out.last_mut() {
                Some(last) if last.0 == a => {
                    last.1 = F::join(&last.1, &k);
                    met = true;
                }
                _ => out.push((a, k)),
            }
        }
        out.retain(|t| !t.1.is_zero());
        (out.len() <= MAX_WHOLE_TERMS).then(|| (F::from_parts(konst, out, fin), met))
    }

    /// `sum`, the sum of the forms `a` and `b`, taken apart where terms meet in it out of
    /// sight: a term of one operand is inside a sum over the cap that is an atom of the other,
    /// or two such sums, one of each operand, have a term of one atom. `None` when none does
    /// (or the sum taken apart is over [`MAX_WHOLE_TERMS`] terms): `sum` is the form then.
    pub(super) fn meeting(&self, a: &F, b: &F, sum: &F, read: &mut u64) -> Option<F> {
        let (oa, ob) = (self.over(a), self.over(b));
        if oa.is_empty() && ob.is_empty() {
            return None;
        }
        // A search reads about as many terms as the whole form's length has bits.
        let mut inside = |over: &[u32], other: &F| {
            over.iter().any(|&o| {
                let (_, terms, _) = self.forms.parts_of(o).expect("it has a whole form");
                let cost = u64::from(terms.len().max(1).ilog2()) + 1;
                other.parts().1.iter().any(|t| {
                    *read += cost;
                    terms.has(t.0)
                })
            })
        };
        // Two sums over the cap, one of each operand, are taken apart to see (one sum in both
        // operands meets itself in the forms' own sum).
        let may = inside(&oa, b) || inside(&ob, a) || oa.iter().any(|o| ob.iter().any(|p| o != p));
        if !may {
            return None;
        }
        let (whole, met) = self.expand(sum, read)?;
        met.then_some(whole)
    }

    /// Keeps the whole form of `i`, a sum over the cap whose form is `form`, unless it is over
    /// [`MAX_WHOLE_TERMS`] terms; terms `met` in `form`, or meet as it is taken apart.
    pub(super) fn keep(&mut self, i: u32, form: F, met: bool, read: &mut u64) {
        let (whole, met) = if self.over(&form).is_empty() {
            *read += form.parts().1.len() as u64;
            (form, met)
        } else {
            match self.expand(&form, read) {
                Some((whole, inside)) => (whole, met || inside),
                None => return,
            }
        };
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

/// A pass's forms for a call: the cache of the forms of nodes, and the whole forms of the
/// sums that are kept beyond the cap on terms.
pub(crate) struct Forms<F> {
    /// The linear pass's forms, per node.
    pub(crate) cache: FormCache<F>,
    /// The linear pass's sums over its cap on terms, whole (see `pass::forms::Whole`).
    pub(crate) whole: Whole<F>,
}

impl<F> Default for Forms<F> {
    fn default() -> Self {
        Forms {
            cache: Default::default(),
            whole: Default::default(),
        }
    }
}

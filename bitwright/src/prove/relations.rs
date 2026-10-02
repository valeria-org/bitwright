//! Root-conditioned bit relations. Only fixed XORs below asserted conjunctions contribute;
//! OR coverage bits and undecided conditions stay in the original circuit. Transitive signed
//! equalities are added as RUP lemmas, never as extra premises of a certificate.

use super::{
    aig::{Aig, Cnf, L},
    sat::{Lit, Solver},
};
use crate::hash::IdMap;

struct Classes {
    parent: Vec<usize>,
    parity: Vec<bool>,
    size: Vec<usize>,
}

impl Classes {
    fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            parity: vec![false; n],
            size: vec![1; n],
        }
    }

    fn find(&mut self, x: usize) -> (usize, bool) {
        let parent = self.parent[x];
        if parent == x {
            return (x, false);
        }
        let (root, parity) = self.find(parent);
        self.parity[x] ^= parity;
        self.parent[x] = root;
        (root, self.parity[x])
    }

    fn join(&mut self, a: usize, b: usize, opposite: bool) -> bool {
        let (mut x, px) = self.find(a);
        let (mut y, py) = self.find(b);
        let flip = px ^ py ^ opposite;
        if x == y {
            return !flip;
        }
        if self.size[x] < self.size[y] {
            core::mem::swap(&mut x, &mut y);
        }
        self.parent[y] = x;
        self.parity[y] = flip;
        self.size[x] += self.size[y];
        true
    }
}

pub(super) fn strengthen(
    graph: &Aig,
    asserted: &[L],
    cnf: &Cnf,
    solver: &mut Solver,
    lemmas: bool,
) {
    let pairs: Vec<_> = graph
        .asserted_aliases(asserted)
        .into_iter()
        .filter_map(|(a, b)| Some((cnf.mapped_lit(a)?, cnf.mapped_lit(b)?)))
        .collect();
    if pairs.len() < 2 {
        return;
    }
    let mut vertices: Vec<_> = pairs.iter().flat_map(|(a, b)| [a.var(), b.var()]).collect();
    vertices.sort_unstable();
    vertices.dedup();
    let positions: IdMap<_, _> = vertices.iter().enumerate().map(|(i, &v)| (v, i)).collect();
    let mut classes = Classes::new(vertices.len());
    let mut edges = IdMap::default();
    for (a, b) in pairs {
        if !classes.join(
            positions[&a.var()],
            positions[&b.var()],
            a.is_neg() ^ b.is_neg(),
        ) {
            // A contradictory equality cycle refutes either value of this variable.
            // The unit is RUP; propagating it establishes the root conflict and logs empty.
            solver.add_rup_clause(&[Lit::pos(a.var())]);
            return;
        }
        if lemmas {
            edges.insert((a.var().min(b.var()), a.var().max(b.var())), ());
        }
    }
    if !lemmas {
        return;
    }
    let mut groups: IdMap<usize, Vec<(u32, bool)>> = IdMap::default();
    for v in vertices {
        let (root, parity) = classes.find(positions[&v]);
        groups.entry(root).or_default().push((v, parity));
    }
    let mut groups: Vec<_> = groups.into_values().collect();
    groups.sort_unstable_by_key(|g| g[0].0);
    let mut budget = 1024usize;
    for group in groups {
        // Large components use a star, with linear construction as well as bounded output.
        let pairs: Vec<_> = if group.len() > 8 {
            let pivot = group.len() / 2;
            (0..group.len())
                .filter(|&i| i != pivot)
                .map(|i| (i.min(pivot), i.max(pivot)))
                .collect()
        } else {
            (0..group.len())
                .flat_map(|i| (i + 1..group.len()).map(move |j| (i, j)))
                .collect()
        };
        for (i, j) in pairs {
            let ((a, pa), (b, pb)) = (group[i], group[j]);
            if edges.contains_key(&(a, b)) {
                continue;
            }
            if budget < 2 {
                return;
            }
            budget -= 2;
            let (a, b) = (Lit::pos(a), Lit::new(b, !(pa ^ pb)));
            if !solver.add_rup_clause(&[!a, b]) || !solver.add_rup_clause(&[a, !b]) {
                return;
            }
        }
    }
}

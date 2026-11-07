//! The passes' reasoning for their rewrites, for [`Event::Explain`](super::Event::Explain).
//!
//! What a pass records follows how it works, which changes from release to release: the
//! variants and their fields are not covered by the crate's compatibility promises and may
//! change in any release.

use crate::BitVec;
use crate::expr::Expr;

/// A pass's reasoning for one rewrite.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Explanation {
    /// Fact folding: the node's known bits pin its value.
    Fold {
        /// The bits known to be 0.
        known_zero: BitVec,
        /// The bits known to be 1.
        known_one: BitVec,
        /// The value they pin.
        value: BitVec,
    },
    /// The linear pass read the node as `konst + Σ coeff·atom` over Z/2^W and wrote that form
    /// back.
    Linear {
        /// The constant.
        konst: BitVec,
        /// Each atom with its coefficient.
        terms: Vec<(Expr, BitVec)>,
    },
    /// The xor pass read the node as `konst ⊕ ⊕ (atom & mask)` and wrote that form back.
    Xor {
        /// The constant.
        konst: BitVec,
        /// Each atom with its mask.
        terms: Vec<(Expr, BitVec)>,
    },
    /// The bitwise pass read the node as a function of a few atoms and wrote the minimum form
    /// of its truth table.
    Bitwise {
        /// The atoms.
        atoms: Vec<Expr>,
        /// The truth table: bit `i` is the function's value where atom `k` is bit `k` of `i`
        /// (all ones or all zeros, for every bit position alike).
        table: u64,
    },
    /// The compares pass read the node as a set of the five relations two values can stand
    /// in, and wrote it as one comparison (or fewer).
    Relations {
        /// The first value.
        x: Expr,
        /// The second value.
        y: Expr,
        /// The relations, a bit each: 0 `x == y`; 1 `x <u y` and `x <s y`; 2 `x <u y` and
        /// `x >s y`; 3 `x >u y` and `x <s y`; 4 `x >u y` and `x >s y`.
        set: u8,
    },
    /// The compares pass read the node as a set of values of one operand and wrote it as one
    /// comparison or range check.
    Intervals {
        /// The operand.
        x: Expr,
        /// The values, as disjoint unsigned intervals `[lo, hi]`, ascending.
        set: Vec<(BitVec, BitVec)>,
    },
    /// The linear MBA pass read the node as a linear combination of bitwise functions of its
    /// atoms, determined by its values at the 2^t corners where each atom is all zeros or all
    /// ones.
    LinearMba {
        /// The atoms.
        atoms: Vec<Expr>,
        /// The value at each corner: entry `p` has atom `k` all ones where bit `k` of `p` is
        /// set.
        corners: Vec<BitVec>,
        /// The form it wrote: `affine`, `indicators` or `conjunctions`.
        form: &'static str,
    },
    /// The shuffle pass traced each bit of the node to the bit it comes from.
    Shuffle {
        /// Each bit's source, lowest bit first.
        bits: Vec<Source>,
    },
    /// The casts pass pushed a narrowing (`extract`, `trunc`) into the value it reads, or
    /// recognized a sign extension written with shifts.
    Casts {
        /// The value read.
        source: Expr,
        /// Its lowest bit read.
        lo: u16,
        /// How many bits are read.
        bits: u16,
        /// Whether the bits read are sign-extended back (`sext(trunc(x))` written as shifts).
        sign_extended: bool,
    },
    /// The demanded-bits pass simplified an operand under the bits its user observes.
    Demanded {
        /// The operand.
        operand: Expr,
        /// The bits of it observed.
        mask: BitVec,
    },
    /// The invert pass undid injective layers of an equality's side against a constant: from
    /// the side down to the value compared, each layer with the preimage of the constant under
    /// it.
    Invert {
        /// The layers, outermost first.
        layers: Vec<Peel>,
    },
    /// The division pass recognized a multiplication by a magic number as a division by a
    /// constant, proved exact for every value the dividend can take.
    Division {
        /// The dividend.
        dividend: Expr,
        /// The divisor.
        divisor: BitVec,
        /// Whether the division is signed.
        signed: bool,
    },
    /// The carries pass read a carry or borrow network as the affine form it computes.
    Carries {
        /// The constant.
        konst: BitVec,
        /// Each atom with its coefficient.
        terms: Vec<(Expr, BitVec)>,
        /// Whether the native prover proved the form equal (a chain of shifts of one atom is
        /// equal by construction, unproved).
        proved: bool,
    },
    /// The MBA service: the fragment was lowered over its atoms, simplified by the solver and
    /// lifted back, on this evidence.
    Mba {
        /// The atoms the fragment is a function of (the solver's variables, in order).
        atoms: Vec<Expr>,
        /// What vouched for the answer: `certificate` (bitwright's own), `prover`, `backend`
        /// (the solver's own claim), `sampled`, or `cache` (an answer found before).
        evidence: &'static str,
        /// Which test of bitwright's certificate decided, when it did (`signature`,
        /// `single_bit`, `sparse`, `grid`, `exhaustive`, `symbolic`, `carries`).
        test: Option<&'static str>,
        /// The points the certificate evaluated.
        points: u64,
    },
}

/// Where one bit of a value comes from.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Source {
    /// A constant 0.
    Zero,
    /// A constant 1.
    One,
    /// Bit `bit` of `of`.
    Bit {
        /// The value.
        of: Expr,
        /// The bit.
        bit: u16,
    },
}

/// One layer the invert pass undid.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Peel {
    /// The layer's top node.
    pub node: Expr,
    /// Its operand: the value the layer is a function of, the others fixed.
    pub inner: Expr,
    /// How it maps its operand (`v ^ k`, `v * k`, `rotl(v, k)`, `zext(v)`, `region`, …).
    pub map: &'static str,
    /// Whether it is onto (same width in and out), not only injective.
    pub bijective: bool,
    /// The value the operand must take for the layer to give the constant; `None` when no
    /// value does (then the equality is false).
    pub preimage: Option<BitVec>,
}

/// Calls `f` with every expression an explanation names.
pub(super) fn exprs(why: &Explanation, f: &mut dyn FnMut(Expr)) {
    match why {
        Explanation::Linear { terms, .. }
        | Explanation::Xor { terms, .. }
        | Explanation::Carries { terms, .. } => terms.iter().for_each(|(e, _)| f(*e)),
        Explanation::Bitwise { atoms, .. }
        | Explanation::LinearMba { atoms, .. }
        | Explanation::Mba { atoms, .. } => atoms.iter().for_each(|&e| f(e)),
        Explanation::Relations { x, y, .. } => {
            f(*x);
            f(*y);
        }
        Explanation::Intervals { x, .. } => f(*x),
        Explanation::Shuffle { bits } => {
            for b in bits {
                if let Source::Bit { of, .. } = b {
                    f(*of);
                }
            }
        }
        Explanation::Demanded { operand, .. } => f(*operand),
        Explanation::Casts { source, .. } => f(*source),
        Explanation::Invert { layers } => {
            for l in layers {
                f(l.node);
                f(l.inner);
            }
        }
        Explanation::Division { dividend, .. } => f(*dividend),
        Explanation::Fold { .. } => {}
    }
}

/// Writes an explanation as a JSON object with its `kind`, naming expressions by `id`.
pub(super) fn write(out: &mut String, why: &Explanation, id: &dyn Fn(Expr) -> u64) {
    use super::trace::{Obj, jstr, num};
    let hex = |v: &BitVec| format!("{v:#x}");
    let pairs = |o: &mut Obj<'_>, k: &str, terms: &[(Expr, BitVec)]| {
        o.key(k);
        o.out.push('[');
        for (j, (e, v)) in terms.iter().enumerate() {
            if j > 0 {
                o.out.push(',');
            }
            o.out.push('[');
            num(o.out, id(*e));
            o.out.push(',');
            jstr(o.out, &hex(v));
            o.out.push(']');
        }
        o.out.push(']');
    };
    let ids = |o: &mut Obj<'_>, k: &str, es: &[Expr]| {
        o.key(k);
        o.out.push('[');
        for (j, e) in es.iter().enumerate() {
            if j > 0 {
                o.out.push(',');
            }
            num(o.out, id(*e));
        }
        o.out.push(']');
    };
    let mut o = Obj::new(out);
    match why {
        Explanation::Fold {
            known_zero,
            known_one,
            value,
        } => {
            o.str("kind", "fold");
            o.str("zero", &hex(known_zero));
            o.str("one", &hex(known_one));
            o.str("value", &hex(value));
        }
        Explanation::Linear { konst, terms } => {
            o.str("kind", "linear");
            o.str("konst", &hex(konst));
            pairs(&mut o, "terms", terms);
        }
        Explanation::Xor { konst, terms } => {
            o.str("kind", "xor");
            o.str("konst", &hex(konst));
            pairs(&mut o, "terms", terms);
        }
        Explanation::Bitwise { atoms, table } => {
            o.str("kind", "bitwise");
            ids(&mut o, "atoms", atoms);
            o.str("table", &format!("{table:#x}"));
        }
        Explanation::Relations { x, y, set } => {
            o.str("kind", "relations");
            o.num("x", id(*x));
            o.num("y", id(*y));
            o.num("set", u64::from(*set));
        }
        Explanation::Intervals { x, set } => {
            o.str("kind", "intervals");
            o.num("x", id(*x));
            o.key("set");
            o.out.push('[');
            for (j, (lo, hi)) in set.iter().enumerate() {
                if j > 0 {
                    o.out.push(',');
                }
                o.out.push('[');
                jstr(o.out, &hex(lo));
                o.out.push(',');
                jstr(o.out, &hex(hi));
                o.out.push(']');
            }
            o.out.push(']');
        }
        Explanation::LinearMba {
            atoms,
            corners,
            form,
        } => {
            o.str("kind", "linear_mba");
            ids(&mut o, "atoms", atoms);
            o.key("corners");
            o.out.push('[');
            for (j, v) in corners.iter().enumerate() {
                if j > 0 {
                    o.out.push(',');
                }
                jstr(o.out, &hex(v));
            }
            o.out.push(']');
            o.str("form", form);
        }
        Explanation::Shuffle { bits } => {
            o.str("kind", "shuffle");
            o.key("bits");
            o.out.push('[');
            for (j, b) in bits.iter().enumerate() {
                if j > 0 {
                    o.out.push(',');
                }
                match b {
                    Source::Zero => o.out.push('0'),
                    Source::One => o.out.push('1'),
                    Source::Bit { of, bit } => {
                        o.out.push('[');
                        num(o.out, id(*of));
                        o.out.push(',');
                        num(o.out, u64::from(*bit));
                        o.out.push(']');
                    }
                }
            }
            o.out.push(']');
        }
        Explanation::Casts {
            source,
            lo,
            bits,
            sign_extended,
        } => {
            o.str("kind", "casts");
            o.num("source", id(*source));
            o.num("lo", u64::from(*lo));
            o.num("bits", u64::from(*bits));
            o.bool("sign_extended", *sign_extended);
        }
        Explanation::Demanded { operand, mask } => {
            o.str("kind", "demanded");
            o.num("operand", id(*operand));
            o.str("mask", &hex(mask));
        }
        Explanation::Invert { layers } => {
            o.str("kind", "invert");
            o.key("layers");
            o.out.push('[');
            for (k, l) in layers.iter().enumerate() {
                if k > 0 {
                    o.out.push(',');
                }
                let mut p = Obj::new(o.out);
                p.num("node", id(l.node));
                p.num("inner", id(l.inner));
                p.str("map", l.map);
                p.bool("bijective", l.bijective);
                p.key("preimage");
                match &l.preimage {
                    Some(v) => jstr(p.out, &hex(v)),
                    None => p.out.push_str("null"),
                }
                p.end();
            }
            o.out.push(']');
        }
        Explanation::Division {
            dividend,
            divisor,
            signed,
        } => {
            o.str("kind", "division");
            o.num("dividend", id(*dividend));
            o.str("divisor", &hex(divisor));
            o.bool("signed", *signed);
        }
        Explanation::Carries {
            konst,
            terms,
            proved,
        } => {
            o.str("kind", "carries");
            o.str("konst", &hex(konst));
            pairs(&mut o, "terms", terms);
            o.bool("proved", *proved);
        }
        Explanation::Mba {
            atoms,
            evidence,
            test,
            points,
        } => {
            o.str("kind", "mba");
            ids(&mut o, "atoms", atoms);
            o.str("evidence", evidence);
            if let Some(t) = test {
                o.str("test", t);
            }
            o.num("points", *points);
        }
    }
    o.end();
}

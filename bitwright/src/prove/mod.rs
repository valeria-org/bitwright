//! A native prover (feature `prove`): expressions are bit-blasted into an and-inverter graph,
//! encoded as clauses, and decided by bitwright's own CDCL SAT solver. A proof of validity comes
//! with a certificate, the clauses and a DRUP proof of their unsatisfiability, that an
//! independent checker ([`Certificate::check`]) verifies, and that any DRAT checker can read
//! ([`Certificate::dimacs`], [`Certificate::drat`]). A refutation comes with a counterexample:
//! a value for every symbol, checked by bitwright's evaluator before it is returned.
//!
//! No other solver is involved. Bit-vector operators are blasted with bitwright's total
//! semantics (SMT-LIB's); floating-point operators with IEEE 754's and bitwright's canonical
//! NaN ([`fp`]); extension operations through their [`expand`](crate::ext::ExtOp::expand)
//! definition, if they have one (otherwise the question is not decided).
//!
//! ```
//! use bitwright::prove::{Config, Outcome, equal};
//! use bitwright::{Context, ParseOptions, Width};
//!
//! let mut cx = Context::new();
//! let o = ParseOptions::width(Width::W32);
//! let (a, b) = (cx.parse("(x ^ y) + 2 * (x & y)", &o)?, cx.parse("x + y", &o)?);
//! let Outcome::Proved(Some(cert)) = equal(&mut cx, a, b, &Config::default().with_certificate(true))? else {
//!     panic!("not proved")
//! };
//! assert!(cert.check().is_ok());
//! let c = cx.parse("x | y", &o)?;
//! assert!(matches!(equal(&mut cx, a, c, &Config::default())?, Outcome::Refuted(_)));
//! # Ok::<(), bitwright::Error>(())
//! ```

pub mod aig;
pub mod blast;
pub mod drup;
mod fp;
pub mod sat;
#[cfg(test)]
mod tests;

use crate::error::Error;
use crate::expr::{Context, Expr, OpCode};
use crate::facts::Assumptions;
use crate::hash::IdMap;
use crate::{BitVec, SymbolKey, Width};

use aig::{Aig, Cnf, L};
use blast::Bits;
use sat::{Answer, Lit, Solver, Step};

/// How hard to try, and what to keep.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Config {
    /// The most conflicts the SAT solver may meet (then [`Outcome::Unknown`]).
    pub max_conflicts: u64,
    /// The most AIG nodes the question may take (then [`Outcome::Unknown`]).
    pub max_nodes: usize,
    /// Keep a [`Certificate`] for a proof.
    pub certificate: bool,
    /// Simplify the question with bitwright's own engine before blasting it (the
    /// deobfuscation strategy, with the MBA service when the `mba` feature is on): identities
    /// the engine settles at the word level (products of MBA, say, which bit-level SAT finds
    /// hard) are answered at once, and the rest is blasted smaller. Not with a certificate: a
    /// certificate is of the question as asked.
    pub simplify: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            max_conflicts: 1_000_000,
            max_nodes: 4_000_000,
            certificate: false,
            simplify: true,
        }
    }
}

setters!(Config {
    with_max_conflicts: max_conflicts: u64,
    with_max_nodes: max_nodes: usize,
    with_certificate: certificate: bool,
    with_simplify: simplify: bool,
});

/// The engine that simplifies questions (see [`Config::simplify`]).
fn simplifier() -> &'static crate::engine::Engine {
    static ENGINE: std::sync::OnceLock<crate::engine::Engine> = std::sync::OnceLock::new();
    ENGINE.get_or_init(|| {
        #[cfg(feature = "mba")]
        let strategy =
            crate::engine::Strategy::deobfuscate().with_mba(crate::mba::MbaConfig::default());
        #[cfg(not(feature = "mba"))]
        let strategy = crate::engine::Strategy::deobfuscate();
        crate::engine::Engine::builder()
            .builtin()
            .strategy(strategy)
            .build()
            .unwrap_or_else(|_| crate::engine::Engine::standard())
    })
}

/// Clauses and a DRUP proof that they are unsatisfiable.
#[derive(Clone, Debug)]
pub struct Certificate {
    /// The number of variables.
    pub vars: u32,
    /// The clauses.
    pub clauses: Vec<Vec<Lit>>,
    /// The proof.
    pub proof: Vec<Step>,
}

impl Certificate {
    /// Checks the proof with the independent checker.
    pub fn check(&self) -> Result<(), String> {
        drup::check(&self.clauses, &self.proof)
    }

    /// The clauses in DIMACS CNF.
    pub fn dimacs(&self) -> String {
        let mut s = format!("p cnf {} {}\n", self.vars, self.clauses.len());
        for c in &self.clauses {
            for l in c {
                s.push_str(&l.dimacs().to_string());
                s.push(' ');
            }
            s.push_str("0\n");
        }
        s
    }

    /// The proof in DRAT's text format (additions, and deletions prefixed `d`).
    pub fn drat(&self) -> String {
        let mut s = String::new();
        for step in &self.proof {
            let (pre, c) = match step {
                Step::Add(c) => ("", c),
                Step::Delete(c) => ("d ", c),
            };
            s.push_str(pre);
            for l in c {
                s.push_str(&l.dimacs().to_string());
                s.push(' ');
            }
            s.push_str("0\n");
        }
        s
    }
}

/// The answer to a question.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum Outcome {
    /// It holds for every value of the symbols (with a certificate, if asked for).
    Proved(Option<Certificate>),
    /// It fails at these values of the symbols (checked by evaluation).
    Refuted(Vec<(SymbolKey, BitVec)>),
    /// Not decided: why.
    Unknown(String),
}

/// The bits of expressions, blasted on demand.
pub(crate) struct Blaster<'c> {
    pub(crate) cx: &'c mut Context,
    pub(crate) g: Aig,
    bits: IdMap<u32, Bits>,
    /// Each symbol met, with its bits.
    pub(crate) symbols: Vec<(u32, Bits)>,
    max_nodes: usize,
}

impl<'c> Blaster<'c> {
    pub(crate) fn new(cx: &'c mut Context, max_nodes: usize) -> Blaster<'c> {
        Blaster {
            cx,
            g: Aig::new(),
            bits: IdMap::default(),
            symbols: Vec::new(),
            max_nodes,
        }
    }

    /// The bits of node `root`.
    pub(crate) fn blast(&mut self, root: u32) -> Result<Bits, Error> {
        let order = self.cx.post_order_ids(&[root]);
        for i in order {
            if self.bits.contains_key(&i) {
                continue;
            }
            if self.g.len() > self.max_nodes {
                return Err(Error::Unsupported("the circuit is too large".into()));
            }
            let b = self.node(i)?;
            self.bits.insert(i, b);
        }
        Ok(self.bits[&root].clone())
    }

    fn node(&mut self, i: u32) -> Result<Bits, Error> {
        use blast::*;
        let n = self.cx.node(i);
        let w = usize::from(n.width);
        let get = |s: &Self, j: u32| s.bits[&j].clone();
        let g = &mut self.g;
        Ok(match n.op {
            OpCode::Const => konst(&self.cx.const_val(i).unwrap_or(BitVec::zero(Width::W1))),
            OpCode::Sym => {
                let b: Bits = (0..w).map(|_| g.input()).collect();
                self.symbols.push((i, b.clone()));
                b
            }
            OpCode::Not => not(g, &self.bits[&n.a]),
            OpCode::Neg => {
                let a = get(self, n.a);
                neg(&mut self.g, &a)
            }
            OpCode::Popcnt => popcnt(g, &self.bits[&n.a]),
            OpCode::Clz => clz(g, &self.bits[&n.a]),
            OpCode::Ctz => ctz(g, &self.bits[&n.a]),
            OpCode::Bswap => bswap(&self.bits[&n.a]),
            OpCode::BitRev => bitrev(&self.bits[&n.a]),
            OpCode::Zext => {
                let mut a = get(self, n.a);
                a.resize(w, aig::FALSE);
                a
            }
            OpCode::Sext => {
                let mut a = get(self, n.a);
                let top = *a.last().unwrap_or(&aig::FALSE);
                a.resize(w, top);
                a
            }
            OpCode::Extract => {
                let a = get(self, n.a);
                let lo = n.b as usize;
                a[lo..lo + w].to_vec()
            }
            OpCode::Concat => {
                let (hi, mut lo) = (get(self, n.a), get(self, n.b));
                lo.extend(hi);
                lo
            }
            OpCode::Select => {
                let (c, t, e) = (get(self, n.a)[0], get(self, n.b), get(self, n.c));
                mux(&mut self.g, c, &t, &e)
            }
            OpCode::Eq | OpCode::Ne | OpCode::Ult | OpCode::Ule | OpCode::Slt | OpCode::Sle => {
                let (a, b) = (get(self, n.a), get(self, n.b));
                let g = &mut self.g;
                let r = match n.op {
                    OpCode::Eq => eq(g, &a, &b),
                    OpCode::Ne => eq(g, &a, &b) ^ 1,
                    OpCode::Ult => ult(g, &a, &b),
                    OpCode::Ule => ule(g, &a, &b),
                    OpCode::Slt => slt(g, &a, &b),
                    _ => sle(g, &a, &b),
                };
                vec![r]
            }
            op if op.as_bin().is_some() => {
                let (a, b) = (get(self, n.a), get(self, n.b));
                let g = &mut self.g;
                match op {
                    OpCode::Add => add(g, &a, &b),
                    OpCode::Sub => sub(g, &a, &b),
                    OpCode::Mul => mul(g, &a, &b),
                    OpCode::UMulHi => mulhi(g, &a, &b, false),
                    OpCode::SMulHi => mulhi(g, &a, &b, true),
                    OpCode::UDiv => udivrem(g, &a, &b).0,
                    OpCode::URem => udivrem(g, &a, &b).1,
                    OpCode::SDiv => sdiv(g, &a, &b),
                    OpCode::SRem => srem(g, &a, &b),
                    OpCode::And => and(g, &a, &b),
                    OpCode::Or => or(g, &a, &b),
                    OpCode::Xor => xor(g, &a, &b),
                    OpCode::Shl => shift(g, &a, &b, true, aig::FALSE),
                    OpCode::LShr => shift(g, &a, &b, false, aig::FALSE),
                    OpCode::AShr => {
                        let s = *a.last().unwrap_or(&aig::FALSE);
                        shift(g, &a, &b, false, s)
                    }
                    OpCode::RotL => rotate(g, &a, &b, true),
                    OpCode::RotR => rotate(g, &a, &b, false),
                    OpCode::Pdep => pdep(g, &a, &b),
                    _ => pext(g, &a, &b),
                }
            }
            op if op.as_ext().is_some() => self.ext(i)?,
            _ => fp::blast(self, i)?,
        })
    }

    /// An extension output, through the operation's expansion.
    fn ext(&mut self, i: u32) -> Result<Bits, Error> {
        let n = self.cx.node(i);
        let Some((_, k)) = n.op.as_ext() else {
            return Err(Error::Unsupported("not an extension output".into()));
        };
        let args: Vec<Expr> = n.children().map(|c| self.cx.handle(c)).collect();
        let reg = self
            .cx
            .registry
            .clone()
            .ok_or_else(|| Error::Unsupported("an extension without its registry".into()))?;
        let op = reg
            .op_at(n.aux)
            .ok_or_else(|| Error::Unsupported("an extension without its operation".into()))?;
        let Some(ex) = op.expand(self.cx, &args) else {
            return Err(Error::Unsupported(format!(
                "`{}` has no expansion to reason about",
                op.name()
            )));
        };
        let outs = ex?;
        let e = self.cx.id(outs[k])?;
        self.blast(e)
    }

    /// The counterexample a model gives: every symbol met, checked by evaluation to make `p`
    /// false (a 1-bit expression).
    fn counterexample(
        &mut self,
        cnf: &Cnf,
        model: &[bool],
    ) -> Result<Vec<(SymbolKey, BitVec)>, Error> {
        let mut out = Vec::new();
        for (s, bits) in &self.symbols {
            let w = self.cx.width_of(*s);
            let mut limbs = [0u64; 8];
            for (k, &b) in bits.iter().enumerate() {
                if cnf.value(b, model) {
                    limbs[k / 64] |= 1 << (k % 64);
                }
            }
            let h = self.cx.handle(*s);
            let key = self
                .cx
                .symbol_id(h)?
                .and_then(|id| self.cx.symbol_key(id))
                .cloned()
                .ok_or_else(|| Error::Contract("a symbol without its key".into()))?;
            out.push((key, BitVec::wrapping_from_limbs(w, &limbs)));
        }
        Ok(out)
    }
}

/// Decides whether the 1-bit `goal` (an AIG literal over `b`'s circuit) is true for every
/// input: `Proved` when its negation is unsatisfiable.
fn decide(
    b: &mut Blaster<'_>,
    goal: L,
    extra: &[L],
    root: Expr,
    cfg: &Config,
) -> Result<Outcome, Error> {
    if b.g.len() > cfg.max_nodes {
        return Ok(Outcome::Unknown("the circuit is too large".into()));
    }
    let mut solver = Solver::new();
    if cfg.certificate {
        solver.log_proof();
    }
    let mut roots = vec![goal];
    roots.extend_from_slice(extra);
    let mut cnf = Cnf::encode(&b.g, &roots, &mut solver);
    for &e in extra {
        cnf.assert(e, &mut solver);
    }
    cnf.assert(goal ^ 1, &mut solver);
    match solver.solve(cfg.max_conflicts) {
        Answer::Unsat => {
            let cert = if cfg.certificate {
                Some(Certificate {
                    vars: solver.num_vars(),
                    clauses: cnf.clauses.clone(),
                    proof: solver.take_proof().unwrap_or_default(),
                })
            } else {
                None
            };
            Ok(Outcome::Proved(cert))
        }
        Answer::Sat(model) => {
            let ce = b.counterexample(&cnf, &model)?;
            // Checked by bitwright's evaluator: a solver or blaster bug cannot produce a false
            // refutation unnoticed.
            let env =
                crate::FnEnv(|k: &SymbolKey, _| ce.iter().find(|(kk, _)| kk == k).map(|(_, v)| *v));
            let v = b.cx.eval(&[root], &env)?[0];
            if v.is_zero() {
                Ok(Outcome::Refuted(ce))
            } else {
                Err(Error::Contract(format!(
                    "the prover's counterexample does not refute {}",
                    b.cx.display(root)
                )))
            }
        }
        Answer::Unknown => Ok(Outcome::Unknown(format!(
            "no answer within {} conflicts",
            cfg.max_conflicts
        ))),
    }
}

/// Whether the 1-bit `p` is true for every value of its symbols.
pub fn valid(cx: &mut Context, p: Expr, cfg: &Config) -> Result<Outcome, Error> {
    valid_under(cx, p, None, cfg)
}

/// Whether `p` is true wherever the constraints of `assumptions` hold.
pub fn valid_under(
    cx: &mut Context,
    p: Expr,
    assumptions: Option<&Assumptions>,
    cfg: &Config,
) -> Result<Outcome, Error> {
    let pi = cx.id(p)?;
    if cx.wid(pi) != 1 {
        return Err(crate::WidthError::Mismatch {
            left: 1,
            right: cx.wid(pi),
        }
        .into());
    }
    // The constraints as 1-bit expressions: each predicate holds, or does not.
    let mut cons: Vec<u32> = Vec::new();
    if let Some(a) = assumptions {
        for (_, e, f) in a.constraints() {
            let i = cx.id(e)?;
            if let Some(v) = f.as_constant() {
                let k = cx.mk_const(&v)?;
                cons.push(cx.c_cmp(crate::CmpOp::Eq, i, k)?);
            } else {
                return Ok(Outcome::Unknown(
                    "a constraint that is not a predicate's value".into(),
                ));
            }
        }
    }
    // The root checked by evaluation: `p` where the constraints hold, as `¬(c1 ∧ …) ∨ p`.
    let mut root = pi;
    for &c in &cons {
        let nc = cx.c_un(crate::UnOp::Not, c)?;
        root = cx.c_bin(crate::BinOp::Or, nc, root)?;
    }
    let root_e = cx.handle(root);
    // The question simplified (not for a certificate, which must be of the question itself).
    let mut goal_node = pi;
    if cfg.simplify && !cfg.certificate {
        let run = match assumptions {
            Some(a) => crate::engine::Run::default().with_assumptions(a),
            None => crate::engine::Run::default(),
        };
        let out = simplifier().run(cx, &[p], run)?.roots[0];
        let s = cx.id(out.expr)?;
        if cx.const_val(s).is_some_and(|v| !v.is_zero()) {
            return Ok(Outcome::Proved(None));
        }
        // A result that relies on constraints holds where they do, which is all a proof under
        // them needs.
        goal_node = s;
    }
    let mut b = Blaster::new(cx, cfg.max_nodes);
    let goal = match b.blast(goal_node) {
        Ok(bits) => bits[0],
        Err(Error::Unsupported(why)) => return Ok(Outcome::Unknown(why)),
        Err(e) => return Err(e),
    };
    let mut extra = Vec::new();
    for &c in &cons {
        match b.blast(c) {
            Ok(bits) => extra.push(bits[0]),
            Err(Error::Unsupported(why)) => return Ok(Outcome::Unknown(why)),
            Err(e) => return Err(e),
        }
    }
    decide(&mut b, goal, &extra, root_e, cfg)
}

/// Whether `a` and `b` (of one width) are equal for every value of their symbols.
pub fn equal(cx: &mut Context, a: Expr, b: Expr, cfg: &Config) -> Result<Outcome, Error> {
    let (ai, bi) = (cx.id(a)?, cx.id(b)?);
    if cx.wid(ai) != cx.wid(bi) {
        return Err(crate::WidthError::Mismatch {
            left: cx.wid(ai),
            right: cx.wid(bi),
        }
        .into());
    }
    let p = cx.c_cmp(crate::CmpOp::Eq, ai, bi)?;
    let p = cx.handle(p);
    valid(cx, p, cfg)
}

/// Values of symbols, as a counterexample or a model gives them.
pub type Model = Vec<(SymbolKey, BitVec)>;

/// A value of the symbols that makes the 1-bit `p` true, if there is one: `Refuted` of `¬p`
/// read back as a model (`Ok(Some)`), `Ok(None)` when `p` is unsatisfiable, and `Err` with the
/// reason when not decided.
pub fn satisfy(
    cx: &mut Context,
    p: Expr,
    cfg: &Config,
) -> Result<Result<Option<Model>, String>, Error> {
    let np = cx.un(crate::UnOp::Not, p)?;
    Ok(match valid(cx, np, cfg)? {
        Outcome::Proved(_) => Ok(None),
        Outcome::Refuted(m) => Ok(Some(m)),
        Outcome::Unknown(why) => Err(why),
    })
}

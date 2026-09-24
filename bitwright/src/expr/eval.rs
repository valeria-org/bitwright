//! Concrete evaluation and substitution.

use std::collections::{BTreeMap, HashMap};
use std::hash::BuildHasher;

use super::{Context, Expr, OpCode};
use crate::error::Error;
use crate::hash::IdMap;
use crate::{BitVec, SymbolKey, Width};

/// Values for symbols, used by [`Context::eval`].
pub trait Env {
    /// The value bound to the symbol `key` of width `width`, if any.
    fn value(&self, key: &SymbolKey, width: Width) -> Option<BitVec>;
}

impl<S: BuildHasher> Env for HashMap<SymbolKey, BitVec, S> {
    fn value(&self, key: &SymbolKey, _width: Width) -> Option<BitVec> {
        self.get(key).copied()
    }
}

impl Env for BTreeMap<SymbolKey, BitVec> {
    fn value(&self, key: &SymbolKey, _width: Width) -> Option<BitVec> {
        self.get(key).copied()
    }
}

impl Env for [(SymbolKey, BitVec)] {
    fn value(&self, key: &SymbolKey, _width: Width) -> Option<BitVec> {
        self.iter().find(|(k, _)| k == key).map(|(_, v)| *v)
    }
}

/// An [`Env`] backed by a closure.
#[derive(Clone, Copy, Debug)]
pub struct FnEnv<F>(pub F);

impl<F: Fn(&SymbolKey, Width) -> Option<BitVec>> Env for FnEnv<F> {
    fn value(&self, key: &SymbolKey, width: Width) -> Option<BitVec> {
        (self.0)(key, width)
    }
}

impl Context {
    /// Evaluates `roots` under `env`. Iterative and memoized per call: a shared node is
    /// evaluated once.
    pub fn eval(
        &mut self,
        roots: &[Expr],
        env: &(impl Env + ?Sized),
    ) -> Result<Vec<BitVec>, Error> {
        let ids = self.ids(roots)?;
        self.eval_ids(&ids, env)
    }

    pub(crate) fn eval_ids(
        &mut self,
        roots: &[u32],
        env: &(impl Env + ?Sized),
    ) -> Result<Vec<BitVec>, Error> {
        let order = self.post_order_ids(roots);
        let mut vals: IdMap<u32, BitVec> = IdMap::default();
        vals.reserve(order.len());
        for i in order {
            let v = self.eval_node(i, |j| vals[&j], |key, width| env.value(key, width))?;
            vals.insert(i, v);
        }
        Ok(roots.iter().map(|r| vals[r]).collect())
    }

    /// The value of node `i` from its operands' values (`get`) and symbol values (`sym`).
    pub(crate) fn eval_node(
        &self,
        i: u32,
        get: impl Fn(u32) -> BitVec,
        sym: impl Fn(&SymbolKey, Width) -> Option<BitVec>,
    ) -> Result<BitVec, Error> {
        let n = self.node(i);
        Ok(match n.op {
            OpCode::Const => self.const_val(i).unwrap_or(BitVec::zero(Width::W1)),
            OpCode::Sym => {
                let entry = &self.symbols.entries[n.a as usize];
                let v = sym(&entry.key, entry.width).ok_or_else(|| Error::UnboundSymbol {
                    key: entry.key.clone(),
                })?;
                if v.width() != entry.width {
                    return Err(Error::EnvWidth {
                        key: entry.key.clone(),
                        expected: entry.width,
                        got: v.width(),
                    });
                }
                v
            }
            OpCode::Zext => get(n.a).zext(self.width_of(i))?,
            OpCode::Sext => get(n.a).sext(self.width_of(i))?,
            OpCode::Extract => get(n.a).extract(n.b as u16, self.width_of(i))?,
            OpCode::Concat => BitVec::concat(&get(n.a), &get(n.b))?,
            OpCode::Select => BitVec::select(&get(n.a), &get(n.b), &get(n.c))?,
            op if op.as_ext().is_some() => {
                let args: Vec<BitVec> = n.children().map(&get).collect();
                self.eval_ext(i, &args)?
            }
            op => {
                if let Some(u) = op.as_un() {
                    BitVec::apply_un(u, &get(n.a))?
                } else if let Some(b) = op.as_bin() {
                    BitVec::bin_unchecked(b, &get(n.a), &get(n.b))
                } else if let Some(c) = op.as_cmp() {
                    BitVec::from_bool(BitVec::cmp_unchecked(c, &get(n.a), &get(n.b)))
                } else if let Some(d) = self.fp_desc(i) {
                    let args: Vec<BitVec> = n.children().map(&get).collect();
                    crate::fp::eval(&d, &args)
                } else {
                    unreachable!("every opcode is covered")
                }
            }
        })
    }

    /// The value of extension node `i` for argument values `args` (validated against the
    /// operation's declared widths).
    pub(crate) fn eval_ext(&self, i: u32, args: &[BitVec]) -> Result<BitVec, Error> {
        let n = self.node(i);
        let (_, k) = n.op.as_ext().unwrap_or((1, 0));
        let op = self
            .registry
            .as_deref()
            .and_then(|r| r.op_at(n.aux))
            .ok_or_else(|| Error::Contract("an extension node without its operation".into()))?;
        let out = crate::ext::run_eval(op, args)
            .map_err(|why| Error::Contract(format!("`{}`: {why}", op.name())))?;
        out.get(k)
            .copied()
            .ok_or_else(|| Error::Contract(format!("`{}` has no output {k}", op.name())))
    }

    /// Simultaneously replaces every occurrence of each `from` by its `to` in `roots`
    /// (replacements are not substituted again), rebuilding through the canonicalizing
    /// constructors. Each pair must have equal widths.
    pub fn substitute(&mut self, roots: &[Expr], map: &[(Expr, Expr)]) -> Result<Vec<Expr>, Error> {
        let ids = self.ids(roots)?;
        let mut repl: IdMap<u32, u32> = IdMap::default();
        for &(from, to) in map {
            let (f, t) = (self.id(from)?, self.id(to)?);
            let (wf, wt) = (self.wid(f), self.wid(t));
            if wf != wt {
                return Err(crate::WidthError::Mismatch {
                    left: wf,
                    right: wt,
                }
                .into());
            }
            if repl.insert(f, t).is_some() {
                return Err(Error::DuplicateSubstitution);
            }
        }
        let out = self.substitute_ids(&ids, &repl)?;
        Ok(out.into_iter().map(|i| self.handle(i)).collect())
    }

    /// Applies the substitution `s` to `roots`, working on at most `max_visits` nodes not
    /// already in its memo. `Ok(None)` when that limit stops it first: the progress is kept in
    /// `s`, so a later call continues where this one stopped. The walk never descends below a
    /// replaced node or a node the memo already answers.
    pub fn substitute_bounded(
        &mut self,
        roots: &[Expr],
        s: &mut Substitution,
        max_visits: u64,
    ) -> Result<Option<Vec<Expr>>, Error> {
        let ids = self.ids(roots)?;
        s.check_context(self)?;
        let mut visits = 0u64;
        // Resume the walk a previous call over the same roots stopped in.
        let (mut next_root, mut stack) = match s.pending.take() {
            Some(p) if p.roots == ids => (p.next_root, p.stack),
            _ => (0, Vec::new()),
        };
        loop {
            if stack.is_empty() {
                let Some(&root) = ids.get(next_root) else {
                    break;
                };
                next_root += 1;
                if !s.done.contains_key(&root) {
                    stack.push((root, false));
                }
                continue;
            }
            let Some(&(i, expanded)) = stack.last() else {
                break;
            };
            if s.done.contains_key(&i) {
                stack.pop();
                continue;
            }
            if let Some(&t) = s.repl.get(&i) {
                stack.pop();
                s.done.insert(i, t);
                continue;
            }
            let n = self.node(i);
            if !expanded {
                if visits >= max_visits {
                    s.pending = Some(Pending {
                        roots: ids,
                        next_root,
                        stack,
                    });
                    return Ok(None);
                }
                visits += 1;
                if let Some(top) = stack.last_mut() {
                    top.1 = true;
                }
                for c in n.children() {
                    if !s.done.contains_key(&c) {
                        stack.push((c, false));
                    }
                }
                continue;
            }
            stack.pop();
            let mut kids = [n.a, n.b, n.c];
            let mut changed = false;
            for (k, c) in n.children().enumerate() {
                let nc = s.done[&c];
                changed |= nc != c;
                kids[k] = nc;
            }
            let r = if changed { self.rebuild(i, kids)? } else { i };
            s.done.insert(i, r);
        }
        Ok(Some(ids.iter().map(|r| self.handle(s.done[r])).collect()))
    }

    pub(crate) fn substitute_ids(
        &mut self,
        roots: &[u32],
        repl: &IdMap<u32, u32>,
    ) -> Result<Vec<u32>, Error> {
        let order = self.post_order_ids(roots);
        let mut new: IdMap<u32, u32> = IdMap::default();
        for i in order {
            let r = if let Some(&t) = repl.get(&i) {
                t
            } else {
                let n = self.node(i);
                let mut kids = [n.a, n.b, n.c];
                let mut changed = false;
                for (k, c) in n.children().enumerate() {
                    let nc = new[&c];
                    changed |= nc != c;
                    kids[k] = nc;
                }
                if changed { self.rebuild(i, kids)? } else { i }
            };
            new.insert(i, r);
        }
        Ok(roots.iter().map(|r| new[r]).collect())
    }
}

/// A stopped substitution walk: the roots, the next root to start, and the stack.
#[derive(Clone, Debug)]
struct Pending {
    roots: Vec<u32>,
    next_root: usize,
    stack: Vec<(u32, bool)>,
}

/// A substitution applied incrementally by [`Context::substitute_bounded`]: the replacements,
/// and the result of every node rewritten so far. Repeated calls share that work, and a caller
/// can read which new node each old one became (to carry its own metadata along).
#[derive(Clone, Debug, Default)]
pub struct Substitution {
    repl: IdMap<u32, u32>,
    done: IdMap<u32, u32>,
    /// The walk a call stopped in, resumed by the next call over the same roots.
    pending: Option<Pending>,
    /// A handle of the context the substitution belongs to (to reject another context's).
    probe: Option<Expr>,
}

impl Substitution {
    /// An empty substitution.
    pub fn new() -> Self {
        Self::default()
    }

    /// Replaces every occurrence of `from` by `to` (not substituted again). The widths must
    /// match, `from` may be given once, and no node may have been rewritten yet.
    pub fn replace(&mut self, cx: &Context, from: Expr, to: Expr) -> Result<&mut Self, Error> {
        let (f, t) = (cx.id(from)?, cx.id(to)?);
        self.check_context(cx)?;
        let (wf, wt) = (cx.wid(f), cx.wid(t));
        if wf != wt {
            return Err(crate::WidthError::Mismatch {
                left: wf,
                right: wt,
            }
            .into());
        }
        if !self.done.is_empty() {
            return Err(Error::Unsupported(
                "a replacement added after the substitution was applied".into(),
            ));
        }
        if self.repl.insert(f, t).is_some() {
            return Err(Error::DuplicateSubstitution);
        }
        self.probe.get_or_insert(from);
        Ok(self)
    }

    /// What `e` became, if the substitution has reached it.
    pub fn image(&self, cx: &Context, e: Expr) -> Result<Option<Expr>, Error> {
        let i = cx.id(e)?;
        Ok(self.done.get(&i).map(|&r| cx.handle(r)))
    }

    /// Every node reached so far that changed, with what it became, in node order.
    pub fn changed(&self, cx: &Context) -> Vec<(Expr, Expr)> {
        let mut v: Vec<(u32, u32)> = self
            .done
            .iter()
            .filter(|(a, b)| a != b)
            .map(|(&a, &b)| (a, b))
            .collect();
        v.sort_unstable();
        v.into_iter()
            .map(|(a, b)| (cx.handle(a), cx.handle(b)))
            .collect()
    }

    fn check_context(&self, cx: &Context) -> Result<(), Error> {
        if let Some(p) = self.probe {
            cx.id(p)?;
        }
        Ok(())
    }
}

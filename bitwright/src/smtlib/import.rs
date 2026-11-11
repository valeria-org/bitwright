//! SMT-LIB 2.6 import of a QF_BV subset, and of floating-point (QF_BVFP) terms.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::error::Error;
use crate::expr::{Context, Expr};
use crate::fp::{FpCmpOp, FpFormat, FpOp, FpTest, RoundingMode};
use crate::ops::{BinOp, CmpOpExt, UnOp};
use crate::text::SyntaxError;
use crate::{BitVec, SymbolKey, Width};

#[path = "int.rs"]
mod int;
#[cfg(feature = "prove")]
pub(super) use int::decimal;
#[path = "wide.rs"]
mod wide;
use wide::MAX_WIDE;
pub(super) use wide::Wide;

/// The most deeply nested list the reader accepts.
const MAX_DEPTH: usize = 512;

/// A script's declarations, definitions and assertions, in order.
#[derive(Clone, Debug, Default)]
#[non_exhaustive]
pub struct Import {
    /// Declared constants (`declare-const`, or `declare-fun` without parameters) as symbols. A
    /// `Bool` constant is a 1-bit symbol.
    pub symbols: Vec<(String, Expr)>,
    /// Definitions without parameters (`define-fun`), by name. A `Bool` is a 1-bit expression.
    pub definitions: Vec<(String, Expr)>,
    /// Asserted formulas, as 1-bit expressions.
    pub assertions: Vec<Expr>,
    /// Declared arrays, as memories (see [`crate::memory`]): a `select` is a load of their
    /// final contents' history, so a model's values for the reads' symbols
    /// ([`Memory::reads`](crate::memory::Memory::reads)) give the array's cells.
    pub arrays: Vec<(String, crate::memory::Memory)>,
}

impl Import {
    /// The definition named `name`.
    pub fn definition(&self, name: &str) -> Option<Expr> {
        self.definitions
            .iter()
            .find(|(n, _)| n == name)
            .map(|&(_, e)| e)
    }
}

/// Reads a QF_BV script into `cx`.
///
/// Accepted: `set-logic`, `set-info`, `set-option`, `declare-const`, `declare-fun` without
/// parameters, `define-fun` (one with parameters is expanded where it is applied),
/// `define-const`, `define-sort` and `declare-sort` without parameters (a declared sort is
/// read as 64-bit vectors, which a quantifier-free script cannot tell from any other set of
/// values; its values print as such), `assert`, the query commands (`check-sat`, `get-model`,
/// `get-value`, `echo`), which are ignored, and `exit`, which ends the script: no command after
/// it runs (the whole text must still be well formed). Sorts are `Bool` and `(_ BitVec n)` with
/// `1 ≤ n ≤ 512`. Terms are literals (`#b…`, `#x…`, `(_ bvN n)`), `let`, `ite`, `=`,
/// `distinct`, `(! t :named n)` (`n` names `t` from there on, as a definition), the core
/// Boolean operators, and every operator of the QF_BV theory and its
/// extensions (`bvnand`, `bvnor`, `bvxnor`, `bvcomp`, `bvsmod`, the overflow predicates
/// `bvnego`, `bvuaddo`, `bvsaddo`, `bvusubo`, `bvssubo`, `bvumulo`, `bvsmulo`, `bvsdivo`, the `u`/`s` comparisons,
/// `repeat`, `rotate_left`, `rotate_right`, `zero_extend`, `sign_extend`, `extract`).
///
/// Floats: the sorts `(_ FloatingPoint eb sb)`, `Float16`, `Float32`, `Float64`, `Float128`
/// (a float constant is a symbol of `eb + sb` bits holding its encoding) and `RoundingMode`
/// (its five constants, by either name; a declared one is a 3-bit symbol asserted below 5,
/// and a term with it as an operand is read once for each mode, the symbol choosing); `(fp s e m)`,
/// `(_ +zero eb sb)`, `-zero`, `+oo`, `-oo`, `NaN`; every operator of the FloatingPoint
/// theory, the comparisons chainable; `to_fp` from bits, a float, a signed integer or a real
/// constant (a numeral, a decimal, `(- r)`, `(/ n m)`), `to_fp_unsigned`, `fp.to_ubv` and
/// `fp.to_sbv` (saturating, as bitwright defines them), and z3's `fp.to_ieee_bv` (a NaN as the
/// canonical one). `=` on floats treats every NaN as one value. What SMT-LIB leaves open
/// (the zero `fp.min` of `+0` and `−0` returns, conversions out of range) takes bitwright's
/// definitions here; a solver session ([`run`](super::run)) leaves it open, as symbols.
///
/// Arrays (QF_ABV): the sort `(Array (_ BitVec n) (_ BitVec m))`, declared constants of it,
/// `select` and `store`, read as [`memory`](crate::memory) loads and stores; an array chosen
/// by `ite`, a constant array (`(as const …)`) and a store into either are read through
/// element by element, and an equality of arrays is a Boolean with the constraints of
/// extensionality: an index where the two differ when it is false, and agreement at every
/// index the script reads or writes when it is true.
///
/// Uninterpreted functions (`declare-fun` with parameters, over bit-vectors, Booleans and
/// floats): each application is a symbol of its own, named `f!k`, and for every two
/// applications of one function an assertion is added that their results are equal where all
/// their arguments are. Those assertions are the function's whole meaning; they are among
/// [`Import::assertions`], before the assertion whose terms made the applications.
///
/// Anything else is an error. Symbol names `#k` and `$k` (decimal `k`) read as integer and
/// fresh keys, so an [`export`](super::export)ed script reads back to the same symbols.
pub fn import(cx: &mut Context, script: &str) -> Result<Import, Error> {
    // A syntax error anywhere fails the import before any command runs.
    let mut env = Env::new(false);
    env.reserve(check(script)?);
    let mut st = State::new(cx, &mut env);
    // Then one top-level form at a time: syntax buffers are bounded by the largest command.
    let mut sx = Sx::default();
    let mut pos = 0;
    while let Some(top) = sx.read(script, &mut pos)? {
        st.command(&sx, top)?;
        if st.env.exited {
            break;
        }
    }
    Ok(env.out)
}

// ----- the reader ----------------------------------------------------------------------------

/// A token of a form: a symbol or literal borrowed from the script, or a list.
#[derive(Copy, Clone, Debug)]
pub(super) enum Tok<'s> {
    /// A symbol or keyword, bars removed.
    Sym(&'s str),
    /// A numeral, `#b`/`#x` literal, or string.
    Lit(&'s str),
    /// A list, whose elements are `kids[start..end]`.
    List(u32, u32),
}

/// A lexeme: a parenthesis or an atom.
enum Lex<'s> {
    Open,
    Close,
    Atom(Tok<'s>),
}

fn syntax(message: &str, start: usize, end: usize) -> Error {
    Error::Syntax(SyntaxError::new(message, start, end))
}

/// The lexeme at or after `*i`, skipping blanks and comments, with its span; `None` at the end.
#[inline(always)]
fn lex<'s>(src: &'s str, i: &mut usize) -> Result<Option<(Lex<'s>, usize, usize)>, Error> {
    let b = src.as_bytes();
    while *i < b.len() {
        let start = *i;
        match b[start] {
            b' ' | b'\t' | b'\r' | b'\n' => *i += 1,
            b';' => {
                while *i < b.len() && b[*i] != b'\n' {
                    *i += 1;
                }
            }
            b'(' => {
                *i += 1;
                return Ok(Some((Lex::Open, start, *i)));
            }
            b')' => {
                *i += 1;
                return Ok(Some((Lex::Close, start, *i)));
            }
            b'|' => {
                *i += 1;
                while *i < b.len() && b[*i] != b'|' {
                    if b[*i] == b'\\' {
                        return Err(syntax("'\\' in a quoted symbol", *i, *i + 1));
                    }
                    *i += 1;
                }
                if *i >= b.len() {
                    return Err(syntax("unterminated quoted symbol", start, *i));
                }
                *i += 1;
                let name = &src[start + 1..*i - 1];
                return Ok(Some((Lex::Atom(Tok::Sym(name)), start, *i)));
            }
            b'"' => {
                *i += 1;
                loop {
                    if *i >= b.len() {
                        return Err(syntax("unterminated string", start, *i));
                    }
                    if b[*i] == b'"' {
                        if b.get(*i + 1) == Some(&b'"') {
                            *i += 2;
                            continue;
                        }
                        *i += 1;
                        break;
                    }
                    *i += 1;
                }
                return Ok(Some((Lex::Atom(Tok::Lit(&src[start..*i])), start, *i)));
            }
            _ => {
                while *i < b.len()
                    && !matches!(
                        b[*i],
                        b' ' | b'\t' | b'\r' | b'\n' | b'(' | b')' | b';' | b'|' | b'"'
                    )
                {
                    *i += 1;
                }
                let s = &src[start..*i];
                let tok = if s.starts_with('#') || s.as_bytes()[0].is_ascii_digit() {
                    Tok::Lit(s)
                } else {
                    Tok::Sym(s)
                };
                return Ok(Some((Lex::Atom(tok), start, *i)));
            }
        }
    }
    Ok(None)
}

/// Checks the syntax of the whole script (balance, depth, quoted symbols and strings) without
/// building anything, reserving prefixes of numbered symbols for array reads.
pub(super) fn check(src: &str) -> Result<HashSet<&str>, Error> {
    // Every open list: its start, its depth, its elements so far, and whether it is a `let`.
    let mut open: Vec<(usize, usize, usize, bool)> = Vec::new();
    let mut i = 0;
    let mut reserved_read_prefixes = HashSet::new();
    while let Some((lexeme, start, end)) = lex(src, &mut i)? {
        match lexeme {
            Lex::Open => {
                let depth = open
                    .last()
                    .map_or(0, |&(_, d, items, is_let)| d + list_depth(items, is_let));
                if depth >= MAX_DEPTH {
                    return Err(syntax("nested too deeply", start, end));
                }
                open.push((start, depth, 0, false));
            }
            Lex::Close => {
                if open.pop().is_none() {
                    return Err(syntax("unbalanced ')'", start, end));
                }
                if let Some(parent) = open.last_mut() {
                    parent.2 += 1;
                }
            }
            Lex::Atom(tok) => {
                if let Some(list) = open.last_mut() {
                    list.3 |= list.2 == 0 && matches!(tok, Tok::Sym("let"));
                    list.2 += 1;
                }
                if let Tok::Sym(name) = tok
                    && let Some((prefix, index)) = name.rsplit_once('.')
                    && !index.is_empty()
                    && index.bytes().all(|b| b.is_ascii_digit())
                {
                    reserved_read_prefixes.insert(prefix);
                }
            }
        }
    }
    match open.last() {
        Some(&(start, ..)) => Err(syntax("unbalanced '('", start, src.len())),
        None => Ok(reserved_read_prefixes),
    }
}

/// The depth a list adds to its elements' when it has `items` before the next one: one,
/// except for a `let`'s body (its third element), which the import evaluates in a loop, not
/// nested in the `let`. So a chain of `let`s, as z3 prints a large term, is as deep as one.
fn list_depth(items: usize, is_let: bool) -> usize {
    usize::from(!(is_let && items == 2))
}

/// One top-level form: its tokens with their spans in the script. The buffers are reused from
/// one form to the next.
#[derive(Default)]
pub(super) struct Sx<'s> {
    /// The text the form was read from.
    src: &'s str,
    nodes: Vec<(Tok<'s>, usize, usize)>,
    /// The elements of every list, each list's contiguous.
    kids: Vec<u32>,
    /// While reading: the elements of the open lists read so far.
    stack: Vec<u32>,
    /// While reading: each open list's start, where its elements begin in `stack`, and its
    /// depth (see [`list_depth`]).
    open: Vec<(usize, usize, usize)>,
}

impl<'s> Sx<'s> {
    /// Reads the form at or after `*pos`, replacing the previous one: its root, or `None` at the
    /// end of the script.
    pub(super) fn read(&mut self, src: &'s str, pos: &mut usize) -> Result<Option<u32>, Error> {
        self.src = src;
        self.nodes.clear();
        self.kids.clear();
        self.stack.clear();
        self.open.clear();
        while let Some((lexeme, start, end)) = lex(src, pos)? {
            let node = match lexeme {
                Lex::Open => {
                    let depth = self.open.last().map_or(0, |&(_, base, d)| {
                        let items = self.stack.len() - base;
                        let is_let =
                            items > 0 && matches!(self.tok(self.stack[base]), Tok::Sym("let"));
                        d + list_depth(items, is_let)
                    });
                    if depth >= MAX_DEPTH {
                        return Err(syntax("nested too deeply", start, end));
                    }
                    self.open.push((start, self.stack.len(), depth));
                    continue;
                }
                Lex::Close => {
                    let Some((list_start, base, _)) = self.open.pop() else {
                        return Err(syntax("unbalanced ')'", start, end));
                    };
                    let first = self.kids.len() as u32;
                    self.kids.extend_from_slice(&self.stack[base..]);
                    self.stack.truncate(base);
                    (Tok::List(first, self.kids.len() as u32), list_start, end)
                }
                Lex::Atom(tok) => (tok, start, end),
            };
            let id = self.nodes.len() as u32;
            self.nodes.push(node);
            if self.open.is_empty() {
                return Ok(Some(id));
            }
            self.stack.push(id);
        }
        match self.open.last() {
            Some(&(start, ..)) => Err(syntax("unbalanced '('", start, src.len())),
            None => Ok(None),
        }
    }

    pub(super) fn tok(&self, id: u32) -> Tok<'s> {
        self.nodes[id as usize].0
    }

    /// The form `id` as written.
    pub(super) fn text(&self, id: u32) -> &'s str {
        let (_, s, e) = self.nodes[id as usize];
        &self.src[s..e]
    }

    pub(super) fn err(&self, id: u32, message: &str) -> Error {
        let (_, s, e) = self.nodes[id as usize];
        syntax(message, s, e)
    }

    pub(super) fn list(&self, id: u32) -> Option<&[u32]> {
        match self.tok(id) {
            Tok::List(a, b) => Some(&self.kids[a as usize..b as usize]),
            _ => None,
        }
    }

    pub(super) fn sym(&self, id: u32) -> Option<&'s str> {
        match self.tok(id) {
            Tok::Sym(s) => Some(s),
            _ => None,
        }
    }

    pub(super) fn name(&self, id: u32) -> Result<&'s str, Error> {
        self.sym(id)
            .ok_or_else(|| self.err(id, "expected a symbol"))
    }

    pub(super) fn numeral(&self, id: u32) -> Result<u32, Error> {
        match self.tok(id) {
            Tok::Lit(s) if s.bytes().all(|c| c.is_ascii_digit()) => s
                .parse::<u32>()
                .map_err(|_| self.err(id, "numeral out of range")),
            _ => Err(self.err(id, "expected a numeral")),
        }
    }

    fn width(&self, id: u32, n: u32) -> Result<Width, Error> {
        u16::try_from(n)
            .ok()
            .and_then(|n| Width::new(n).ok())
            .ok_or_else(|| self.err(id, "bit-vector widths must be 1..=512"))
    }

    fn sort(&self, id: u32, defined: &HashMap<String, Sort>) -> Result<Sort, Error> {
        if let Some(&sort) = self.sym(id).and_then(|name| defined.get(name)) {
            return Ok(sort);
        }
        match self.sym(id) {
            Some("Bool") => return Ok(Sort::Bool),
            Some("Int") => return Ok(Sort::Int),
            Some("RoundingMode") => return Ok(Sort::Rm),
            Some("Float16") => return Ok(Sort::Fp(FpFormat::F16)),
            Some("Float32") => return Ok(Sort::Fp(FpFormat::F32)),
            Some("Float64") => return Ok(Sort::Fp(FpFormat::F64)),
            Some("Float128") => return Ok(Sort::Fp(FpFormat::F128)),
            _ => {}
        }
        if let Some(k) = self.list(id)
            && k.len() == 4
            && self.sym(k[0]) == Some("_")
            && self.sym(k[1]) == Some("FloatingPoint")
        {
            let (eb, sb) = (self.numeral(k[2])?, self.numeral(k[3])?);
            return FpFormat::new(eb, sb)
                .map(Sort::Fp)
                .map_err(|e| self.err(id, &e.to_string()));
        }
        if let Some(k) = self.list(id)
            && k.len() == 3
            && self.sym(k[0]) == Some("_")
            && self.sym(k[1]) == Some("BitVec")
        {
            let n = self.numeral(k[2])?;
            if n > 512 && n <= MAX_WIDE {
                return Ok(Sort::Wide(n));
            }
            return Ok(Sort::Bv(self.width(k[2], n)?));
        }
        if let Some(k) = self.list(id)
            && k.len() == 3
            && self.sym(k[0]) == Some("Array")
        {
            return match (self.sort(k[1], defined)?, self.sort(k[2], defined)?) {
                (Sort::Bv(i), Sort::Bv(e)) => Ok(Sort::Array(i, e)),
                _ => Err(self.err(id, "arrays from bit-vectors to bit-vectors only")),
            };
        }
        Err(self.err(
            id,
            "unsupported sort (Bool, (_ BitVec n), an Array of them, a FloatingPoint sort or \
             RoundingMode)",
        ))
    }
}

// ----- terms ---------------------------------------------------------------------------------

/// A term's value: a bit-vector, a Boolean as a 1-bit expression, a float as its encoding in its
/// format, or a rounding mode (constants only).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(super) enum Val {
    Bv(Expr),
    Bool(Expr),
    Fp(Expr, FpFormat),
    Rm(RoundingMode),
    /// A rounding mode that is not a constant: a 3-bit expression, 0 to 4 for the modes in
    /// [`MODES`]' order (a declared one is constrained to that range).
    RmVar(Expr),
    /// An array: a memory of [`Import::arrays`] at a version.
    Array(u32, crate::memory::Version),
    /// An array made from others (an [`Arr`] of the environment).
    Arr(u32),
    /// A bit-vector above 512 bits (a [`Wide`] of the environment): limbs.
    Wide(u32),
    /// An integer with a range: a signed bit-vector wide enough for it (see `int`).
    Int(Expr),
}

/// An array that is not a declared one at a version.
#[derive(Copy, Clone)]
enum Arr {
    /// `(ite c a b)`.
    Ite(Expr, Val, Val),
    /// `((as const (Array I E)) v)`: the index width and the value.
    Const(Width, Expr),
    /// `(store a i v)` where `a` is not a declared array at a version.
    Store(Val, Expr, Expr),
}

impl Val {
    /// The expression of a value that has one (a rounding mode has none).
    pub(super) fn expr(self) -> Option<Expr> {
        match self {
            Val::Bv(e) | Val::Bool(e) | Val::Fp(e, _) | Val::RmVar(e) | Val::Int(e) => Some(e),
            Val::Rm(_) | Val::Array(..) | Val::Arr(_) | Val::Wide(_) => None,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub(super) enum Sort {
    Bool,
    Bv(Width),
    Fp(FpFormat),
    Rm,
    Array(Width, Width),
    /// A bit-vector above 512 bits, of this many.
    Wide(u32),
    /// The integers (read where a bit-vector bounds them).
    Int,
}

/// `let` bindings: each name's values, innermost last, and the names in binding order.
#[derive(Default)]
struct Scope<'s> {
    values: HashMap<&'s str, Vec<Val>>,
    order: Vec<&'s str>,
}

impl<'s> Scope<'s> {
    fn len(&self) -> usize {
        self.order.len()
    }

    fn bind(&mut self, name: &'s str, v: Val) {
        self.values.entry(name).or_default().push(v);
        self.order.push(name);
    }

    /// Drops the bindings after the first `len`.
    fn truncate(&mut self, len: usize) {
        while self.order.len() > len {
            let name = self.order.pop().unwrap_or_default();
            if let Some(vs) = self.values.get_mut(name) {
                vs.pop();
                if vs.is_empty() {
                    self.values.remove(name);
                }
            }
        }
    }

    fn get(&self, name: &str) -> Option<Val> {
        self.values.get(name).and_then(|vs| vs.last()).copied()
    }
}

/// What a script has declared and defined so far: all that outlives a command, none of it
/// borrowed from the script's text (so a script may arrive in pieces).
pub(super) struct Env {
    /// Declared and defined names, and whether a term has read each so far.
    pub(super) globals: HashMap<String, (Val, bool)>,
    /// Those names in the order they were bound: a scope's are the ones after its start.
    pub(super) journal: Vec<String>,
    /// Defined functions with parameters, and their names in definition order.
    funs: HashMap<String, Rc<Fun>>,
    fun_journal: Vec<String>,
    /// Declared functions with parameters (uninterpreted), their names in declaration order,
    /// and each application made so far: the symbol that stands for its result.
    ufs: HashMap<String, Rc<Uf>>,
    uf_journal: Vec<String>,
    apps: Vec<App>,
    /// Arrays made from others, the equalities of arrays read so far (the Boolean that
    /// stands for each, and its sides), and every index an array was read or written at:
    /// an equality says its sides agree at each of them.
    arrs: Vec<Arr>,
    /// The bit-vectors above 512 bits made so far, and the declared ones by name.
    pub(super) wides: Vec<Wide>,
    pub(super) wide_symbols: Vec<(String, u32)>,
    array_eqs: Vec<(Expr, Val, Val)>,
    indices: Vec<Expr>,
    index_set: HashSet<Expr>,
    /// Applications ever made: a result's symbol is numbered by it, so never reused.
    app_count: u64,
    /// Defined sorts (`define-sort` without parameters), and their names in order.
    sorts: HashMap<String, Sort>,
    sort_journal: Vec<String>,
    /// Prefixes of numbered script symbols, including declarations after an array's first read.
    reserved_read_prefixes: HashSet<String>,
    /// Whether `(exit)` ran: the commands after it are not part of the script.
    pub(super) exited: bool,
    /// A solver session reads the script (see [`super::session`]): an assertion is never read
    /// as a definition, and a name declared again after its scope closed may change sort.
    session: bool,
    pub(super) out: Import,
}

impl Env {
    pub(super) fn new(session: bool) -> Self {
        Env {
            globals: HashMap::new(),
            journal: Vec::new(),
            funs: HashMap::new(),
            fun_journal: Vec::new(),
            ufs: HashMap::new(),
            uf_journal: Vec::new(),
            apps: Vec::new(),
            arrs: Vec::new(),
            wides: Vec::new(),
            wide_symbols: Vec::new(),
            array_eqs: Vec::new(),
            indices: Vec::new(),
            index_set: HashSet::new(),
            app_count: 0,
            sorts: HashMap::new(),
            sort_journal: Vec::new(),
            reserved_read_prefixes: HashSet::new(),
            exited: false,
            session,
            out: Import::default(),
        }
    }

    /// Reserves the read prefixes [`check`] found in a piece of the script.
    pub(super) fn reserve(&mut self, prefixes: HashSet<&str>) {
        (self.reserved_read_prefixes).extend(prefixes.into_iter().map(str::to_string));
    }

    /// Where the declarations stand: what a scope opening remembers.
    #[cfg_attr(not(feature = "prove"), allow(dead_code))]
    pub(super) fn mark(&self) -> EnvMark {
        EnvMark {
            globals: self.journal.len(),
            funs: self.fun_journal.len(),
            ufs: self.uf_journal.len(),
            apps: self.apps.len(),
            wide_symbols: self.wide_symbols.len(),
            array_eqs: self.array_eqs.len(),
            indices: self.indices.len(),
            sorts: self.sort_journal.len(),
            symbols: self.out.symbols.len(),
            definitions: self.out.definitions.len(),
        }
    }

    /// Forgets what was declared and defined since `at`, and what it added to the import (a
    /// scope closing).
    #[cfg_attr(not(feature = "prove"), allow(dead_code))]
    pub(super) fn forget(&mut self, at: &EnvMark) {
        for name in self.journal.drain(at.globals..) {
            self.globals.remove(&name);
        }
        for name in self.fun_journal.drain(at.funs..) {
            self.funs.remove(&name);
        }
        for name in self.uf_journal.drain(at.ufs..) {
            self.ufs.remove(&name);
        }
        for name in self.sort_journal.drain(at.sorts..) {
            self.sorts.remove(&name);
        }
        // An application made in the scope goes with the constraints that tied its result
        // to the others (assertions of the scope): made again, it is a new one.
        self.apps.truncate(at.apps);
        self.wide_symbols.truncate(at.wide_symbols);
        // So does an equality of arrays, and an index: what they said of each other was
        // asserted in the scope.
        self.array_eqs.truncate(at.array_eqs);
        for i in self.indices.drain(at.indices.min(self.indices.len())..) {
            self.index_set.remove(&i);
        }
        self.out.symbols.truncate(at.symbols);
        self.out.definitions.truncate(at.definitions);
    }
}

/// A state of an [`Env`]'s declarations ([`Env::mark`]); the default is the empty one.
#[derive(Copy, Clone, Default)]
#[cfg_attr(not(feature = "prove"), allow(dead_code))]
pub(super) struct EnvMark {
    globals: usize,
    funs: usize,
    ufs: usize,
    apps: usize,
    wide_symbols: usize,
    array_eqs: usize,
    indices: usize,
    sorts: usize,
    symbols: usize,
    definitions: usize,
}

/// An uninterpreted function: `declare-fun` with parameters.
struct Uf {
    params: Vec<Sort>,
    result: Sort,
}

/// An application of an uninterpreted function: the symbol that stands for its result.
struct App {
    function: String,
    args: Vec<Val>,
    result: Val,
}

/// The reading of one piece of a script (a command, or a function's body) into [`Env`].
pub(super) struct State<'a, 's> {
    pub(super) cx: &'a mut Context,
    pub(super) env: &'a mut Env,
    /// How many function bodies are being expanded, one in another.
    expanding: u32,
    /// `let` bindings.
    scope: Scope<'s>,
    /// How many times the term being read is read: the product of the domains of the
    /// quantifiers around it that are expanded.
    readings: u64,
    /// Operands (terms) read as a rounding mode each, innermost last: a term for a mode
    /// that is not a constant is read once for each mode.
    forced: Vec<(u32, RoundingMode)>,
}

/// The most bits of bound variables a quantifier is expanded over (one reading of its body
/// for each value); quantifiers one in another, twice that in all.
const QUANTIFIED_BITS: u32 = 12;

/// A `define-fun` with parameters: its body is read again at each application.
struct Fun {
    params: Vec<(String, Sort)>,
    result: Sort,
    /// The body's text.
    body: String,
}

/// The most function bodies expanded one in another (a body cannot name its own function, so
/// deeper is a script error or a very long chain of definitions).
const MAX_EXPANSION: u32 = 64;

impl<'a, 's> State<'a, 's> {
    pub(super) fn new(cx: &'a mut Context, env: &'a mut Env) -> Self {
        State {
            cx,
            env,
            expanding: 0,
            scope: Scope::default(),
            readings: 1,
            forced: Vec::new(),
        }
    }

    pub(super) fn command(&mut self, sx: &Sx<'s>, id: u32) -> Result<(), Error> {
        let Some(k) = sx.list(id) else {
            return Err(sx.err(id, "expected a command"));
        };
        let Some((&head, args)) = k.split_first() else {
            return Err(sx.err(id, "empty command"));
        };
        match sx.sym(head) {
            Some(
                "set-logic" | "set-info" | "set-option" | "check-sat" | "get-model" | "get-value"
                | "echo",
            ) => Ok(()),
            Some("exit") if args.is_empty() => {
                self.env.exited = true;
                Ok(())
            }
            Some("declare-const") if args.len() == 2 => self.declare(sx, args[0], args[1]),
            Some("declare-fun") if args.len() == 3 => {
                let Some(params) = sx.list(args[1]) else {
                    return Err(sx.err(args[1], "expected a list of sorts"));
                };
                if params.is_empty() {
                    return self.declare(sx, args[0], args[2]);
                }
                // An uninterpreted function: each application is a symbol, equal to another
                // application's whenever their arguments are (see `apply_uf`).
                let name = sx.name(args[0])?;
                if self.taken(name) {
                    return Err(sx.err(args[0], "already declared"));
                }
                let scalar = |sort: Sort, at: u32| {
                    match sort {
                    Sort::Bool | Sort::Bv(_) | Sort::Fp(_) => Ok(sort),
                    Sort::Rm | Sort::Array(..) | Sort::Wide(_) | Sort::Int => Err(Error::Unsupported(
                        sx.err(
                            at,
                            "a function over rounding modes, arrays or bit-vectors above 512 bits",
                        )
                        .to_string(),
                    )),
                }
                };
                let mut sorts = Vec::with_capacity(params.len());
                for &p in params {
                    sorts.push(scalar(self.sort(sx, p)?, p)?);
                }
                let uf = Uf {
                    params: sorts,
                    result: scalar(self.sort(sx, args[2])?, args[2])?,
                };
                self.env.ufs.insert(name.to_string(), Rc::new(uf));
                self.env.uf_journal.push(name.to_string());
                Ok(())
            }
            Some("declare-sort") if (1..=2).contains(&args.len()) => {
                // An uninterpreted sort: all that matters of it is which of its values are
                // equal, and a formula without quantifiers never tells more values apart
                // than it has terms. 64-bit vectors have more than enough.
                let name = sx.name(args[0])?;
                if args.get(1).is_some_and(|&n| sx.numeral(n) != Ok(0)) {
                    return Err(Error::Unsupported("declare-sort with parameters".into()));
                }
                if self.env.sorts.contains_key(name) || sx.sort(args[0], &HashMap::new()).is_ok() {
                    return Err(sx.err(args[0], "already a sort"));
                }
                self.env
                    .sorts
                    .insert(name.to_string(), Sort::Bv(Width::W64));
                self.env.sort_journal.push(name.to_string());
                Ok(())
            }
            Some("define-sort") if args.len() == 3 => {
                let name = sx.name(args[0])?;
                if sx.list(args[1]).is_none_or(|p| !p.is_empty()) {
                    return Err(Error::Unsupported("define-sort with parameters".into()));
                }
                if self.env.sorts.contains_key(name) || sx.sort(args[0], &HashMap::new()).is_ok() {
                    return Err(sx.err(args[0], "already a sort"));
                }
                let sort = self.sort(sx, args[2])?;
                self.env.sorts.insert(name.to_string(), sort);
                self.env.sort_journal.push(name.to_string());
                Ok(())
            }
            Some("define-fun")
                if args.len() == 4 && sx.list(args[1]).is_some_and(|p| !p.is_empty()) =>
            {
                let name = sx.name(args[0])?;
                if self.taken(name) {
                    return Err(sx.err(args[0], "already declared"));
                }
                let mut params = Vec::new();
                for &p in sx.list(args[1]).unwrap_or_default() {
                    match sx.list(p) {
                        Some(&[n, sort]) => {
                            params.push((sx.name(n)?.to_string(), self.sort(sx, sort)?));
                        }
                        _ => return Err(sx.err(p, "expected (name sort)")),
                    }
                }
                let fun = Fun {
                    params,
                    result: self.sort(sx, args[2])?,
                    body: sx.text(args[3]).to_string(),
                };
                self.env.funs.insert(name.to_string(), Rc::new(fun));
                self.env.fun_journal.push(name.to_string());
                Ok(())
            }
            Some(c @ ("define-fun" | "define-const"))
                if args.len() == if c == "define-fun" { 4 } else { 3 } =>
            {
                // `define-const name sort term` is `define-fun name () sort term`.
                let (sort_at, term_at) = if c == "define-fun" {
                    if sx.list(args[1]).is_none() {
                        return Err(sx.err(args[1], "expected a parameter list"));
                    }
                    (args[2], args[3])
                } else {
                    (args[1], args[2])
                };
                let args = [args[0], sort_at, sort_at, term_at];
                let name = sx.name(args[0])?;
                let sort = self.sort(sx, args[2])?;
                let v = self.term(sx, args[3])?;
                self.check_sort(sx, args[3], v, sort)?;
                self.bind_global(sx, args[0], name, v)?;
                if let Some(e) = v.expr() {
                    self.env.out.definitions.push((name.to_string(), e));
                }
                Ok(())
            }
            Some("assert") if args.len() == 1 => {
                if !self.env.session && self.float_bits(sx, args[0])? {
                    return Ok(());
                }
                let e = self.assertion(sx, args[0], true)?;
                self.env.out.assertions.push(e);
                Ok(())
            }
            Some(c) => Err(Error::Unsupported(format!(
                "the command {c} (or its arity)"
            ))),
            None => Err(sx.err(head, "expected a command name")),
        }
    }

    /// An asserted term, or its negation's operand (`positive` false). A quantifier that
    /// only asks for a witness here (`exists` asserted, `forall` denied) binds its
    /// variables to new symbols, whatever their sorts' sizes.
    fn assertion(&mut self, sx: &Sx<'s>, id: u32, positive: bool) -> Result<Expr, Error> {
        if let Some(&[head, ref args @ ..]) = sx.list(id) {
            match (sx.sym(head), args) {
                (Some("not"), &[t]) => {
                    let e = self.assertion(sx, t, !positive)?;
                    return self.cx.un(UnOp::Not, e);
                }
                (Some(q @ ("exists" | "forall")), &[bindings, body])
                    if (q == "exists") == positive =>
                {
                    let outer = self.scope.len();
                    let bound = self.bound(sx, bindings)?;
                    for (name, sort) in bound {
                        self.env.app_count += 1;
                        let key = format!("{name}!{}", self.env.app_count);
                        let e = self.cx.symbol(SymbolKey::from(key.as_str()), sort.1)?;
                        self.scope.bind(name, sort.0(e));
                    }
                    let r = self.assertion(sx, body, positive);
                    self.scope.truncate(outer);
                    return r;
                }
                _ => {}
            }
        }
        match self.term(sx, id)? {
            Val::Bool(e) => Ok(e),
            _ => Err(sx.err(id, "an assertion must be Boolean")),
        }
    }

    /// The variables a quantifier binds: each with what makes a value of its sort from an
    /// expression, and its width.
    #[allow(clippy::type_complexity)]
    fn bound(
        &mut self,
        sx: &Sx<'s>,
        bindings: u32,
    ) -> Result<Vec<(&'s str, (Box<dyn Fn(Expr) -> Val>, Width))>, Error> {
        let Some(list) = sx.list(bindings) else {
            return Err(sx.err(bindings, "expected the bound variables"));
        };
        let mut out = Vec::with_capacity(list.len());
        for &b in list {
            let Some(&[name, sort]) = sx.list(b) else {
                return Err(sx.err(b, "expected (name sort)"));
            };
            let Some(name) = sx.sym(name) else {
                return Err(sx.err(name, "expected a name"));
            };
            let made: (Box<dyn Fn(Expr) -> Val>, Width) = match self.sort(sx, sort)? {
                Sort::Bool => (Box::new(Val::Bool), Width::W1),
                Sort::Bv(w) => (Box::new(Val::Bv), w),
                Sort::Fp(f) => (Box::new(move |e| Val::Fp(e, f)), f.width()),
                Sort::Rm | Sort::Array(..) | Sort::Wide(_) | Sort::Int => {
                    return Err(Error::Unsupported(
                        "a quantifier over rounding modes, arrays or bit-vectors above 512 bits"
                            .into(),
                    ));
                }
            };
            out.push((name, made));
        }
        Ok(out)
    }

    /// `(forall (…) t)` or `(exists (…) t)` anywhere in a term: `t` read once for every
    /// value of the variables, which is possible up to [`QUANTIFIED_BITS`] bits of them.
    fn quantifier(
        &mut self,
        sx: &Sx<'s>,
        id: u32,
        forall: bool,
        args: &[u32],
    ) -> Result<Val, Error> {
        let &[bindings, body] = args else {
            return Err(sx.err(id, "expected the bound variables and a term"));
        };
        let bound = self.bound(sx, bindings)?;
        let bits: u32 = bound.iter().map(|(_, (_, w))| u32::from(w.bits())).sum();
        self.readings = self.readings.saturating_mul(1u64 << bits.min(40));
        if bits > QUANTIFIED_BITS || self.readings > 1 << (2 * QUANTIFIED_BITS) {
            return Err(Error::Unsupported(format!(
                "a quantifier over more than {QUANTIFIED_BITS} bits, other than an asserted \
                 exists or a denied forall"
            )));
        }
        let outer = self.scope.len();
        let mut acc = self.cx.bool(forall)?;
        for point in 0..1u64 << bits {
            let mut shift = 0;
            for (name, (make, w)) in &bound {
                let v = self
                    .cx
                    .constant(&BitVec::wrapping_from_u64(*w, point >> shift))?;
                shift += u32::from(w.bits());
                self.scope.bind(name, make(v));
            }
            let r = self.term_in_scope(sx, body);
            self.scope.truncate(outer);
            let Val::Bool(e) = r? else {
                return Err(sx.err(body, "a quantified term must be Boolean"));
            };
            acc = self
                .cx
                .bin(if forall { BinOp::And } else { BinOp::Or }, acc, e)?;
        }
        self.readings >>= bits;
        Ok(Val::Bool(acc))
    }

    fn bind_global(&mut self, sx: &Sx<'s>, id: u32, name: &str, v: Val) -> Result<(), Error> {
        if self.taken(name) {
            return Err(sx.err(id, "already declared"));
        }
        self.env.globals.insert(name.to_string(), (v, false));
        self.env.journal.push(name.to_string());
        Ok(())
    }

    /// Whether `name` is declared or defined (as a constant or a function).
    fn taken(&self, name: &str) -> bool {
        self.env.globals.contains_key(name)
            || self.env.funs.contains_key(name)
            || self.env.ufs.contains_key(name)
    }

    /// The sort written at `id`, a defined one included.
    fn sort(&self, sx: &Sx<'s>, id: u32) -> Result<Sort, Error> {
        match sx.sort(id, &self.env.sorts)? {
            // (An import lists each declared name with one expression.)
            Sort::Wide(_) if !self.env.session => {
                Err(sx.err(id, "bit-vector widths must be 1..=512"))
            }
            sort => Ok(sort),
        }
    }

    /// `(f a…)` of an uninterpreted function: the symbol of this application, the same as
    /// an earlier one's when the arguments are the same terms, and otherwise asserted equal
    /// to each earlier one's wherever all the arguments are equal (the function's only
    /// property). So a function costs a constraint per pair of its applications, and none
    /// when it is applied once.
    fn apply_uf(
        &mut self,
        sx: &Sx<'s>,
        id: u32,
        op: &str,
        uf: &Uf,
        args: &[(u32, Val)],
    ) -> Result<Val, Error> {
        if uf.params.len() != args.len() {
            return Err(sx.err(id, "wrong number of operands"));
        }
        for (&sort, &(a, v)) in uf.params.iter().zip(args) {
            self.check_sort(sx, a, v, sort)?;
        }
        let vals: Vec<Val> = args.iter().map(|&(_, v)| v).collect();
        if let Some(app) = (self.env.apps.iter()).find(|app| app.function == op && app.args == vals)
        {
            return Ok(app.result);
        }
        let w = match uf.result {
            Sort::Bool => Width::W1,
            Sort::Bv(w) => w,
            Sort::Fp(f) => f.width(),
            Sort::Rm | Sort::Array(..) | Sort::Wide(_) | Sort::Int => {
                unreachable!("refused at the declaration")
            }
        };
        self.env.app_count += 1;
        let key = format!("{op}!{}", self.env.app_count);
        let e = self.cx.symbol(SymbolKey::from(key.as_str()), w)?;
        let result = match uf.result {
            Sort::Bool => Val::Bool(e),
            Sort::Fp(f) => Val::Fp(e, f),
            _ => Val::Bv(e),
        };
        for k in 0..self.env.apps.len() {
            if self.env.apps[k].function != op {
                continue;
            }
            let (other_args, other) = (self.env.apps[k].args.clone(), self.env.apps[k].result);
            let mut same = self.cx.bool(true)?;
            for (&x, &y) in vals.iter().zip(&other_args) {
                let eq = self.same_value(x, y)?;
                same = self.cx.bin(BinOp::And, same, eq)?;
            }
            let equal = self.same_value(result, other)?;
            let differ = self.cx.un(UnOp::Not, same)?;
            let constraint = self.cx.bin(BinOp::Or, differ, equal)?;
            self.env.out.assertions.push(constraint);
        }
        self.env.apps.push(App {
            function: op.to_string(),
            args: vals,
            result,
        });
        Ok(result)
    }

    /// Whether two values of one scalar sort are equal, as SMT-LIB's `=` has it: a float's
    /// NaNs are one value.
    fn same_value(&mut self, x: Val, y: Val) -> Result<Expr, Error> {
        match (x, y) {
            (Val::Fp(a, f), Val::Fp(b, _)) => {
                let bits = self.cx.cmp(CmpOpExt::Eq, a, b)?;
                let (na, nb) = (
                    self.cx.fp_test(f, FpTest::Nan, a)?,
                    self.cx.fp_test(f, FpTest::Nan, b)?,
                );
                let nans = self.cx.bin(BinOp::And, na, nb)?;
                self.cx.bin(BinOp::Or, bits, nans)
            }
            _ => match (x.expr(), y.expr()) {
                (Some(a), Some(b)) => self.cx.cmp(CmpOpExt::Eq, a, b),
                _ => Err(Error::Unsupported("equality of values without bits".into())),
            },
        }
    }

    /// The symbol a declared constant is. In a session a name may be declared again, at
    /// another width, once the scope of its first declaration closed, while the context
    /// keeps the first symbol: the later one is then a symbol of its own, `name!k`.
    fn symbol_of(&mut self, name: &str, w: Width) -> Result<Expr, Error> {
        match self.cx.symbol(key_of(name), w) {
            Err(Error::SymbolWidthConflict { .. }) if self.env.session => {
                let mut k = 1u32;
                loop {
                    let other = format!("{name}!{k}");
                    match self.cx.symbol(SymbolKey::from(other.as_str()), w) {
                        Err(Error::SymbolWidthConflict { .. }) => k += 1,
                        r => return r,
                    }
                }
            }
            r => r,
        }
    }

    /// `(f a…)` of a defined function: its body with the parameters bound, read in the
    /// function's own scope (the caller's `let`s are not visible in it).
    fn expand(
        &mut self,
        sx: &Sx<'s>,
        id: u32,
        op: &str,
        args: &[(u32, Val)],
    ) -> Result<Val, Error> {
        if let Some(uf) = self.env.ufs.get(op).cloned() {
            return self.apply_uf(sx, id, op, &uf, args);
        }
        let Some(fun) = self.env.funs.get(op).cloned() else {
            return Err(Error::Unsupported(format!("the operator {op}")));
        };
        if fun.params.len() != args.len() {
            return Err(sx.err(id, "wrong number of operands"));
        }
        for (&(_, sort), &(a, v)) in fun.params.iter().zip(args) {
            self.check_sort(sx, a, v, sort)?;
        }
        if self.expanding >= MAX_EXPANSION {
            return Err(sx.err(id, "function definitions nested too deeply"));
        }
        let mut body = Sx::default();
        let Some(root) = body.read(&fun.body, &mut 0)? else {
            return Err(sx.err(id, "the function has no body"));
        };
        // The body is its own text: read in a state of its own, the parameters its scope.
        let mut inner = State {
            cx: &mut *self.cx,
            env: &mut *self.env,
            expanding: self.expanding + 1,
            scope: Scope::default(),
            readings: self.readings,
            forced: Vec::new(),
        };
        for ((name, _), &(_, v)) in fun.params.iter().zip(args) {
            inner.scope.bind(name, v);
        }
        let v = inner.term(&body, root)?;
        inner.check_sort(&body, root, v, fun.result)?;
        Ok(v)
    }

    fn declare(&mut self, sx: &Sx<'s>, name_id: u32, sort_id: u32) -> Result<(), Error> {
        let name = sx.name(name_id)?;
        let sort = self.sort(sx, sort_id)?;
        if let Sort::Array(i, e) = sort {
            // Read symbols must not capture any script name, even one declared later.
            // Keep the usual readable prefix unless its numbered reads could collide.
            let mut read_name = name.to_string();
            let mut suffix = 0;
            while self.env.reserved_read_prefixes.contains(read_name.as_str()) {
                read_name = format!("{name}.reads{suffix}");
                suffix += 1;
            }
            let m = crate::memory::Memory::new(&read_name, i, e, crate::memory::Endian::Little);
            let v = Val::Array(self.env.out.arrays.len() as u32, m.initial());
            self.env.out.arrays.push((name.to_string(), m));
            return self.bind_global(sx, name_id, name, v);
        }
        if sort == Sort::Int {
            // An integer of any size: no bit-vector bounds it.
            return Err(Error::Unsupported(
                sx.err(
                    sort_id,
                    "a variable of sort Int (integers are read where a bit-vector bounds them)",
                )
                .to_string(),
            ));
        }
        if let Sort::Wide(bits) = sort {
            // A symbol for each limb, low first.
            let mut limbs = Vec::new();
            for k in 0..bits.div_ceil(wide::LIMB) {
                let w = Width::new(wide::LIMB.min(bits - k * wide::LIMB) as u16)
                    .map_err(|e| sx.err(sort_id, &e.to_string()))?;
                limbs.push(self.symbol_of(&format!("{name}!limb{k}"), w)?);
            }
            self.env.wides.push(Wide { limbs, bits });
            let at = self.env.wides.len() as u32 - 1;
            self.env.wide_symbols.push((name.to_string(), at));
            return self.bind_global(sx, name_id, name, Val::Wide(at));
        }
        let w = match sort {
            Sort::Bool => Width::W1,
            Sort::Bv(w) => w,
            Sort::Fp(f) => f.width(),
            Sort::Rm => {
                // A rounding mode is one of five: a 3-bit symbol below 5. An operation that
                // reads it is read once for each mode (see `over_modes`).
                let e = self.symbol_of(name, Width::new(3).unwrap_or(Width::W1))?;
                let five = self
                    .cx
                    .constant(&BitVec::wrapping_from_u64(self.cx.width(e)?, 5))?;
                let in_range = self.cx.cmp(CmpOpExt::Ult, e, five)?;
                self.env.out.assertions.push(in_range);
                self.bind_global(sx, name_id, name, Val::RmVar(e))?;
                self.env.out.symbols.push((name.to_string(), e));
                return Ok(());
            }
            Sort::Array(..) | Sort::Wide(_) | Sort::Int => unreachable!("declared above"),
        };
        let e = self.symbol_of(name, w)?;
        let v = match sort {
            Sort::Bool => Val::Bool(e),
            Sort::Fp(f) => Val::Fp(e, f),
            _ => Val::Bv(e),
        };
        self.bind_global(sx, name_id, name, v)?;
        self.env.out.symbols.push((name.to_string(), e));
        Ok(())
    }

    fn check_sort(&self, sx: &Sx<'s>, id: u32, v: Val, sort: Sort) -> Result<(), Error> {
        let ok = match (v, sort) {
            (Val::Bool(_), Sort::Bool) | (Val::Rm(_) | Val::RmVar(_), Sort::Rm) => true,
            (Val::Bv(e), Sort::Bv(w)) => self.cx.width(e)? == w,
            (Val::Fp(_, f), Sort::Fp(g)) => f == g,
            (Val::Wide(_), Sort::Wide(n)) => self.wide_bits(v) == n,
            (Val::Int(_), Sort::Int) => true,
            (Val::Array(..) | Val::Arr(_), Sort::Array(i, e)) => {
                self.array_sort(v)? == Some((i, e))
            }
            _ => false,
        };
        if ok {
            Ok(())
        } else {
            Err(sx.err(id, "the term does not have the declared sort"))
        }
    }

    /// The index and element widths of an array value.
    fn array_sort(&self, v: Val) -> Result<Option<(Width, Width)>, Error> {
        let mut v = v;
        loop {
            match v {
                Val::Array(m, _) => {
                    let mem = &self.env.out.arrays[m as usize].1;
                    return Ok(Some((mem.addr_width(), mem.cell_width())));
                }
                Val::Arr(k) => match self.env.arrs[k as usize] {
                    Arr::Const(i, e) => return Ok(Some((i, self.cx.width(e)?))),
                    Arr::Ite(_, a, _) | Arr::Store(a, ..) => v = a,
                },
                _ => return Ok(None),
            }
        }
    }

    /// The element of array `a` at index `i`.
    fn read(&mut self, a: Val, i: Expr) -> Result<Expr, Error> {
        match a {
            Val::Array(m, at) => {
                let mem = &mut self.env.out.arrays[m as usize].1;
                Ok(mem.load(self.cx, at, i, 1)?)
            }
            Val::Arr(k) => match self.env.arrs[k as usize] {
                Arr::Const(_, v) => Ok(v),
                Arr::Ite(c, x, y) => {
                    let (x, y) = (self.read(x, i)?, self.read(y, i)?);
                    Ok(self.cx.select(c, x, y)?)
                }
                Arr::Store(x, j, v) => {
                    let here = self.cx.cmp(CmpOpExt::Eq, i, j)?;
                    let below = self.read(x, i)?;
                    Ok(self.cx.select(here, v, below)?)
                }
            },
            _ => Err(Error::Unsupported("expected an array".into())),
        }
    }

    /// Notes an index an array is read or written at: every equality of arrays of that
    /// index sort read so far says its sides agree there.
    fn note_index(&mut self, i: Expr) -> Result<(), Error> {
        if !self.env.index_set.insert(i) {
            return Ok(());
        }
        self.env.indices.push(i);
        for k in 0..self.env.array_eqs.len() {
            let (e, a, b) = self.env.array_eqs[k];
            self.agree_at(e, a, b, i)?;
        }
        Ok(())
    }

    /// Asserts that `e` (an equality of the arrays `a` and `b`) implies they agree at `i`.
    fn agree_at(&mut self, e: Expr, a: Val, b: Val, i: Expr) -> Result<(), Error> {
        if self.array_sort(a)?.map(|s| s.0) != Some(self.cx.width(i)?) {
            return Ok(());
        }
        let (x, y) = (self.read(a, i)?, self.read(b, i)?);
        let same = self.cx.cmp(CmpOpExt::Eq, x, y)?;
        let not = self.cx.un(UnOp::Not, e)?;
        let constraint = self.cx.bin(BinOp::Or, not, same)?;
        self.env.out.assertions.push(constraint);
        Ok(())
    }

    /// `(= a b)` for arrays, by extensionality: a Boolean that, when false, has an index
    /// where the two differ, and when true makes them agree at every index an array is read
    /// or written at, now or later.
    fn array_equal(&mut self, a: Val, b: Val) -> Result<Expr, Error> {
        if let Some(&(e, ..)) =
            (self.env.array_eqs.iter()).find(|&&(_, x, y)| (x == a && y == b) || (x == b && y == a))
        {
            return Ok(e);
        }
        let Some((index, _)) = self.array_sort(a)? else {
            return Err(Error::Unsupported("expected an array".into()));
        };
        self.env.app_count += 1;
        let n = self.env.app_count;
        let e = self
            .cx
            .symbol(SymbolKey::from(format!("=!{n}").as_str()), Width::W1)?;
        let witness = self
            .cx
            .symbol(SymbolKey::from(format!("=!{n}!index").as_str()), index)?;
        self.note_index(witness)?;
        let (x, y) = (self.read(a, witness)?, self.read(b, witness)?);
        let differ = self.cx.cmp(CmpOpExt::Ne, x, y)?;
        let constraint = self.cx.bin(BinOp::Or, e, differ)?;
        self.env.out.assertions.push(constraint);
        self.env.array_eqs.push((e, a, b));
        for k in 0..self.env.indices.len() {
            let i = self.env.indices[k];
            self.agree_at(e, a, b, i)?;
        }
        Ok(e)
    }

    /// The value of a name, without reading it.
    fn peek(&self, name: &str) -> Option<Val> {
        (self.scope.get(name)).or_else(|| self.env.globals.get(name).map(|&(v, _)| v))
    }

    /// The term `id`, an operand of which is the rounding-mode variable `name` (the 3-bit
    /// `mode`): read with `name` standing for each of the five modes in turn, and the
    /// reading that `mode` selects. Whatever the term does with the mode (round by it,
    /// compare it, pass it on), it does with one of the five.
    fn over_modes(
        &mut self,
        sx: &Sx<'s>,
        id: u32,
        name: &'s str,
        mode: Expr,
    ) -> Result<Val, Error> {
        let outer = self.scope.len();
        let mut readings = Vec::with_capacity(MODES.len());
        for m in MODES {
            self.scope.bind(name, Val::Rm(m));
            let r = self.term_in_scope(sx, id);
            self.scope.truncate(outer);
            readings.push(r?);
        }
        self.chosen_by_mode(&readings, mode)
    }

    /// The term `id`, whose operand `operand` is a rounding mode that is not a constant (the
    /// 3-bit `mode`) and not a name: read with the operand standing for each mode in turn.
    fn over_operand_modes(
        &mut self,
        sx: &Sx<'s>,
        id: u32,
        operand: u32,
        mode: Expr,
    ) -> Result<Val, Error> {
        let mut readings = Vec::with_capacity(MODES.len());
        for m in MODES {
            self.forced.push((operand, m));
            let r = self.term_in_scope(sx, id);
            self.forced.pop();
            readings.push(r?);
        }
        self.chosen_by_mode(&readings, mode)
    }

    /// Of the readings of a term for each of the five modes, the one `mode` selects.
    fn chosen_by_mode(&mut self, readings: &[Val], mode: Expr) -> Result<Val, Error> {
        let w = self.cx.width(mode)?;
        // From the last mode back: `mode == k ? reading k : the rest`.
        let mut acc = match readings[MODES.len() - 1] {
            // A term that is itself a rounding mode: its number.
            Val::Rm(m) => Val::RmVar(self.mode_number(m, w)?),
            v => v,
        };
        for k in (0..MODES.len() - 1).rev() {
            let number = self.cx.constant(&BitVec::wrapping_from_u64(w, k as u64))?;
            let is = self.cx.cmp(CmpOpExt::Eq, mode, number)?;
            let this = match readings[k] {
                Val::Rm(m) => Val::RmVar(self.mode_number(m, w)?),
                v => v,
            };
            acc = match (this, acc) {
                (Val::Bool(a), Val::Bool(b)) => Val::Bool(self.cx.select(is, a, b)?),
                (Val::Bv(a), Val::Bv(b)) => Val::Bv(self.cx.select(is, a, b)?),
                (Val::RmVar(a), Val::RmVar(b)) => Val::RmVar(self.cx.select(is, a, b)?),
                (Val::Fp(a, f), Val::Fp(b, g)) if f == g => Val::Fp(self.cx.select(is, a, b)?, f),
                _ => {
                    return Err(Error::Unsupported(
                        "an array that depends on a rounding-mode variable".into(),
                    ));
                }
            };
        }
        Ok(acc)
    }

    /// A rounding mode as the number a variable has for it.
    fn mode_number(&mut self, m: RoundingMode, w: Width) -> Result<Expr, Error> {
        let k = MODES.iter().position(|&x| x == m).unwrap_or(0);
        self.cx.constant(&BitVec::wrapping_from_u64(w, k as u64))
    }

    /// The value of a name a term reads, marking a global as read.
    fn lookup(&mut self, name: &str) -> Option<Val> {
        if let Some(v) = self.scope.get(name) {
            return Some(v);
        }
        let (v, read) = self.env.globals.get_mut(name)?;
        *read = true;
        Some(*v)
    }

    fn bv(&self, sx: &Sx<'s>, id: u32, v: Val) -> Result<Expr, Error> {
        match v {
            Val::Bv(e) => Ok(e),
            _ => Err(sx.err(id, "expected a bit-vector")),
        }
    }

    fn boolean(&self, sx: &Sx<'s>, id: u32, v: Val) -> Result<Expr, Error> {
        match v {
            Val::Bool(e) => Ok(e),
            _ => Err(sx.err(id, "expected a Boolean")),
        }
    }

    pub(super) fn term(&mut self, sx: &Sx<'s>, id: u32) -> Result<Val, Error> {
        if let Some(&(_, m)) = self.forced.iter().rev().find(|f| f.0 == id) {
            return Ok(Val::Rm(m));
        }
        if !matches!(sx.list(id), Some(&[head, ..]) if sx.sym(head) == Some("let")) {
            return self.term_in_scope(sx, id);
        }
        let outer = self.scope.len();
        let r = self
            .let_chain(sx, id)
            .and_then(|body| self.term_in_scope(sx, body));
        self.scope.truncate(outer);
        r
    }

    /// Binds the `let`s of the chain starting at `id`, one in another's body, in a loop: the
    /// last body.
    fn let_chain(&mut self, sx: &Sx<'s>, mut id: u32) -> Result<u32, Error> {
        while let Some(&[head, ref args @ ..]) = sx.list(id)
            && sx.sym(head) == Some("let")
        {
            let [binds, body] = *args else {
                return Err(sx.err(id, "let takes bindings and a body"));
            };
            let Some(bs) = sx.list(binds) else {
                return Err(sx.err(binds, "expected let bindings"));
            };
            // Parallel: every binding is evaluated in the outer scope.
            let mut new = Vec::with_capacity(bs.len());
            for &b in bs {
                match sx.list(b) {
                    Some(&[n, t]) => {
                        let name = sx.name(n)?;
                        let v = self.term(sx, t)?;
                        new.push((name, v));
                    }
                    _ => return Err(sx.err(b, "expected (name term)")),
                }
            }
            for (name, v) in new {
                self.scope.bind(name, v);
            }
            id = body;
        }
        Ok(id)
    }

    /// A term that is not a `let`, in the current scope.
    fn term_in_scope(&mut self, sx: &Sx<'s>, id: u32) -> Result<Val, Error> {
        if let Some(&(_, m)) = self.forced.iter().rev().find(|f| f.0 == id) {
            return Ok(Val::Rm(m));
        }
        match sx.tok(id) {
            Tok::Lit(s) => self.literal(sx, id, s),
            Tok::Sym(s) => match s {
                "true" => Ok(Val::Bool(self.cx.bool(true)?)),
                "false" => Ok(Val::Bool(self.cx.bool(false)?)),
                _ => {
                    if let Some(v) = self.lookup(s) {
                        return Ok(v);
                    }
                    rounding_mode(s)
                        .map(Val::Rm)
                        .ok_or_else(|| sx.err(id, "undeclared symbol"))
                }
            },
            Tok::List(first, end) => {
                let k = &sx.kids[first as usize..end as usize];
                let Some((&head, args)) = k.split_first() else {
                    return Err(sx.err(id, "empty term"));
                };
                // An operand that names a rounding-mode variable: the term once for each
                // mode, the mode chosen by the variable.
                for &a in args {
                    if let Some(name) = sx.sym(a)
                        && let Some(Val::RmVar(e)) = self.peek(name)
                    {
                        return self.over_modes(sx, id, name, e);
                    }
                }
                // A first operand that is a term for a rounding mode, of an operator that
                // rounds: likewise, the term once for each mode.
                let rounds = match sx.list(head) {
                    Some(h) => h.get(1).and_then(|&o| sx.sym(o)).is_some_and(|o| {
                        matches!(o, "to_fp" | "to_fp_unsigned" | "fp.to_ubv" | "fp.to_sbv")
                    }),
                    None => matches!(
                        sx.sym(head),
                        Some(
                            "fp.add"
                                | "fp.sub"
                                | "fp.mul"
                                | "fp.div"
                                | "fp.fma"
                                | "fp.sqrt"
                                | "fp.roundToIntegral"
                        )
                    ),
                };
                if rounds
                    && let Some(&a) = args.first()
                    && sx.list(a).is_some()
                    && !self.forced.iter().any(|f| f.0 == a)
                    && let Val::RmVar(e) = self.term(sx, a)?
                {
                    return self.over_operand_modes(sx, id, a, e);
                }
                if let Some(h) = sx.list(head) {
                    // A constant array: `((as const (Array I E)) v)`.
                    if let [a, c, sort] = *h
                        && sx.sym(a) == Some("as")
                        && sx.sym(c) == Some("const")
                    {
                        let Sort::Array(index, element) = self.sort(sx, sort)? else {
                            return Err(sx.err(sort, "expected an array sort"));
                        };
                        let [v] = *args else {
                            return Err(sx.err(id, "wrong number of operands"));
                        };
                        let value = self.term(sx, v)?;
                        let value = self.bv(sx, v, value)?;
                        if self.cx.width(value)? != element {
                            return Err(sx.err(v, "the value is not the array's element sort"));
                        }
                        self.env.arrs.push(Arr::Const(index, value));
                        return Ok(Val::Arr(self.env.arrs.len() as u32 - 1));
                    }
                    // An indexed operator applied: `((_ extract i j) t)`.
                    return self.indexed(sx, id, h, args);
                }
                match sx.sym(head) {
                    Some("_") => self.indexed_constant(sx, id, args),
                    Some("!") => self.annotated(sx, id, args),
                    Some(q @ ("forall" | "exists")) => self.quantifier(sx, id, q == "forall", args),
                    Some(op) => {
                        let mut vals = Vec::with_capacity(args.len());
                        for &a in args {
                            vals.push((a, self.term(sx, a)?));
                        }
                        self.apply(sx, id, op, &vals)
                    }
                    None => Err(sx.err(head, "expected an operator")),
                }
            }
        }
    }

    /// `(! t :named n …)`: `t`, and `n` a name for it from here on. Other attributes are
    /// read past.
    fn annotated(&mut self, sx: &Sx<'s>, id: u32, args: &[u32]) -> Result<Val, Error> {
        let Some((&t, attrs)) = args.split_first() else {
            return Err(sx.err(id, "an annotation needs a term"));
        };
        let v = self.term(sx, t)?;
        let mut k = 0;
        while k < attrs.len() {
            if sx.sym(attrs[k]) == Some(":named") {
                let Some(&n) = attrs.get(k + 1) else {
                    return Err(sx.err(id, ":named needs a name"));
                };
                let name = sx.name(n)?;
                self.bind_global(sx, n, name, v)?;
                if let Some(e) = v.expr() {
                    self.env.out.definitions.push((name.to_string(), e));
                }
                k += 2;
            } else {
                // An attribute, and its value when the next element is not another keyword.
                let valued = (attrs.get(k + 1))
                    .is_some_and(|&a| !sx.sym(a).is_some_and(|s| s.starts_with(':')));
                k += 1 + usize::from(valued);
            }
        }
        Ok(v)
    }

    fn literal(&mut self, sx: &Sx<'s>, id: u32, s: &str) -> Result<Val, Error> {
        let (bits_per, digits) = if let Some(d) = s.strip_prefix("#b") {
            (1u32, d)
        } else if let Some(d) = s.strip_prefix("#x") {
            (4, d)
        } else {
            if !s.is_empty() && s.bytes().all(|c| c.is_ascii_digit()) {
                return self.int_literal(sx, id, s);
            }
            return Err(sx.err(id, "not a literal this reader knows"));
        };
        let n = (digits.len() as u32).saturating_mul(bits_per);
        let wide = n > 512 && n <= MAX_WIDE;
        let w = if wide { Width::W1 } else { sx.width(id, n)? };
        let mut limbs = vec![0u64; (n as usize).div_ceil(64)];
        for (k, ch) in digits.bytes().rev().enumerate() {
            let d = (ch as char)
                .to_digit(1 << bits_per)
                .ok_or_else(|| sx.err(id, "bad digit"))?;
            let bit = k * bits_per as usize;
            limbs[bit / 64] |= u64::from(d) << (bit % 64);
        }
        if wide {
            let value = self.wide_constant(&limbs, n)?;
            return self.wide_val(value);
        }
        Ok(Val::Bv(
            self.cx.constant(&BitVec::wrapping_from_limbs(w, &limbs))?,
        ))
    }

    /// `(_ bvN n)`, or a float's special value `(_ +zero eb sb)` (`-zero`, `+oo`, `-oo`, `NaN`).
    fn indexed_constant(&mut self, sx: &Sx<'s>, id: u32, args: &[u32]) -> Result<Val, Error> {
        if let [v, eb, sb] = args {
            let f = self.format(sx, id, *eb, *sb)?;
            let value = match sx.sym(*v) {
                Some("+zero") => f.zero(false),
                Some("-zero") => f.zero(true),
                Some("+oo") => f.inf(false),
                Some("-oo") => f.inf(true),
                Some("NaN") => f.nan(),
                _ => return Err(sx.err(*v, "expected +zero, -zero, +oo, -oo or NaN")),
            };
            return Ok(Val::Fp(self.cx.constant(&value)?, f));
        }
        let [v, n] = args else {
            return Err(sx.err(id, "expected (_ bvN n)"));
        };
        let Some(dec) = sx.sym(*v).and_then(|s| s.strip_prefix("bv")) else {
            return Err(sx.err(*v, "expected bvN"));
        };
        if dec.is_empty() || !dec.bytes().all(|c| c.is_ascii_digit()) {
            return Err(sx.err(*v, "expected bvN"));
        }
        let nn = sx.numeral(*n)?;
        let wide = nn > 512 && nn <= MAX_WIDE;
        let w = if wide { Width::W1 } else { sx.width(*n, nn)? };
        let bits = if wide {
            nn as usize
        } else {
            usize::from(w.bits())
        };
        // Decimal into limbs, refusing a value that does not fit.
        let mut limbs = vec![0u64; bits.div_ceil(64) + 1];
        for d in dec.bytes() {
            let mut carry = u128::from(d - b'0');
            for l in &mut limbs {
                let x = u128::from(*l) * 10 + carry;
                *l = x as u64;
                carry = x >> 64;
            }
            if carry != 0 {
                return Err(sx.err(*v, "value does not fit the width"));
            }
        }
        let fits = limbs.iter().enumerate().all(|(k, &l)| {
            let lo = k * 64;
            if lo >= bits {
                l == 0
            } else if lo + 64 > bits {
                l >> (bits - lo) == 0
            } else {
                true
            }
        });
        if !fits {
            return Err(sx.err(*v, "value does not fit the width"));
        }
        if wide {
            let value = self.wide_constant(&limbs, nn)?;
            return self.wide_val(value);
        }
        Ok(Val::Bv(
            self.cx.constant(&BitVec::wrapping_from_limbs(w, &limbs))?,
        ))
    }

    /// `((_ op i …) t …)`.
    fn indexed(&mut self, sx: &Sx<'s>, id: u32, head: &[u32], args: &[u32]) -> Result<Val, Error> {
        let Some((&u, idx)) = head.split_first() else {
            return Err(sx.err(id, "expected an indexed operator"));
        };
        if sx.sym(u) != Some("_") || idx.is_empty() {
            return Err(sx.err(id, "expected an indexed operator"));
        }
        let op = sx.name(idx[0])?;
        // No indexed operator takes more than two indices.
        let mut buf = [0u32; 2];
        let Some(nums) = buf.get_mut(..idx.len() - 1) else {
            return Err(sx.err(id, "too many indices"));
        };
        for (n, &i) in nums.iter_mut().zip(&idx[1..]) {
            *n = sx.numeral(i)?;
        }
        let nums = &*nums;
        if matches!(op, "to_fp" | "to_fp_unsigned" | "fp.to_ubv" | "fp.to_sbv") {
            return self.indexed_float(sx, id, op, nums, args);
        }
        let [a] = args else {
            return Err(sx.err(id, "an indexed operator takes one operand"));
        };
        let v = self.term(sx, *a)?;
        // A wide operand, or a result that is wide.
        let grows = match (v, op, nums) {
            (Val::Wide(_), ..) => true,
            (Val::Bv(e), "zero_extend" | "sign_extend", &[k]) => {
                u32::from(self.cx.width(e)?.bits()).saturating_add(k) > 512
            }
            (Val::Bv(e), "repeat", &[k]) => {
                u32::from(self.cx.width(e)?.bits()).saturating_mul(k) > 512
            }
            _ => false,
        };
        if grows && let Some(x) = self.wide_of(v)? {
            return self.indexed_wide(sx, id, op, nums, x);
        }
        if let (Val::Int(i), "int2bv" | "int_to_bv", &[n]) = (v, op, nums) {
            return self.int_to_bv(i, n);
        }
        let x = self.bv(sx, *a, v)?;
        let w = u32::from(self.cx.width(x)?.bits());
        let e = match (op, nums) {
            ("extract", &[hi, lo]) => {
                if lo > hi || hi >= w {
                    return Err(sx.err(id, "extract out of range"));
                }
                let len = sx.width(id, hi - lo + 1)?;
                self.cx.extract(x, lo as u16, len)?
            }
            ("zero_extend" | "sign_extend", &[k]) => {
                if k == 0 {
                    x
                } else {
                    let to = sx.width(id, w.saturating_add(k))?;
                    if op == "zero_extend" {
                        self.cx.zext(x, to)?
                    } else {
                        self.cx.sext(x, to)?
                    }
                }
            }
            ("repeat", &[k]) => {
                if k == 0 {
                    return Err(sx.err(id, "repeat 0"));
                }
                sx.width(id, w.saturating_mul(k))?;
                let mut acc = x;
                for _ in 1..k {
                    acc = self.cx.concat(acc, x)?;
                }
                acc
            }
            ("rotate_left" | "rotate_right", &[k]) => {
                let width = self.cx.width(x)?;
                let c = self.cx.constant_u64(width, u64::from(k % w))?;
                let op = if op == "rotate_left" {
                    BinOp::RotL
                } else {
                    BinOp::RotR
                };
                self.cx.bin(op, x, c)?
            }
            _ => return Err(Error::Unsupported(format!("the indexed operator {op}"))),
        };
        Ok(Val::Bv(e))
    }

    fn apply(&mut self, sx: &Sx<'s>, id: u32, op: &str, args: &[(u32, Val)]) -> Result<Val, Error> {
        let n = args.len();
        let arity = |ok: bool| {
            if ok {
                Ok(())
            } else {
                Err(sx.err(id, "wrong number of operands"))
            }
        };
        if op.starts_with("fp") && (op == "fp" || op.starts_with("fp.")) {
            return self.apply_float(sx, id, op, args);
        }
        if self.int_case(op, args) {
            return self.apply_int(sx, id, op, args);
        }
        if self.wide_case(op, args)? {
            return self.apply_wide(sx, id, op, args);
        }
        if op == "select" || op == "store" {
            arity(n == if op == "select" { 2 } else { 3 })?;
            let array = args[0].1;
            let Some((index, element)) = self.array_sort(array)? else {
                return Err(sx.err(args[0].0, "expected an array"));
            };
            let i = self.bv(sx, args[1].0, args[1].1)?;
            if self.cx.width(i)? != index {
                return Err(sx.err(args[1].0, "the index is not the array's index sort"));
            }
            self.note_index(i)?;
            if op == "select" {
                return Ok(Val::Bv(self.read(array, i)?));
            }
            let v = self.bv(sx, args[2].0, args[2].1)?;
            if self.cx.width(v)? != element {
                return Err(sx.err(
                    args[2].0,
                    "the stored value is not the array's element sort",
                ));
            }
            return Ok(match array {
                Val::Array(m, at) => {
                    let mem = &mut self.env.out.arrays[m as usize].1;
                    Val::Array(m, mem.store(self.cx, at, i, v)?)
                }
                _ => {
                    self.env.arrs.push(Arr::Store(array, i, v));
                    Val::Arr(self.env.arrs.len() as u32 - 1)
                }
            });
        }
        // Operators over bit-vectors.
        let bin = match op {
            "bvadd" => Some((BinOp::Add, true)),
            "bvmul" => Some((BinOp::Mul, true)),
            "bvand" => Some((BinOp::And, true)),
            "bvor" => Some((BinOp::Or, true)),
            "bvxor" => Some((BinOp::Xor, true)),
            "bvsub" => Some((BinOp::Sub, false)),
            "bvudiv" => Some((BinOp::UDiv, false)),
            "bvurem" => Some((BinOp::URem, false)),
            "bvsdiv" => Some((BinOp::SDiv, false)),
            "bvsrem" => Some((BinOp::SRem, false)),
            "bvshl" => Some((BinOp::Shl, false)),
            "bvlshr" => Some((BinOp::LShr, false)),
            "bvashr" => Some((BinOp::AShr, false)),
            // z3's rotations by a term (as it prints them), by the count modulo the width.
            "ext_rotate_left" => Some((BinOp::RotL, false)),
            "ext_rotate_right" => Some((BinOp::RotR, false)),
            _ => None,
        };
        if let Some((b, left_assoc)) = bin {
            arity(n == 2 || (left_assoc && n > 2))?;
            let mut acc = self.bv(sx, args[0].0, args[0].1)?;
            for &(a, v) in &args[1..] {
                let x = self.bv(sx, a, v)?;
                acc = self.cx.bin(b, acc, x)?;
            }
            return Ok(Val::Bv(acc));
        }
        let cmp = match op {
            "bvult" => Some(CmpOpExt::Ult),
            "bvule" => Some(CmpOpExt::Ule),
            "bvugt" => Some(CmpOpExt::Ugt),
            "bvuge" => Some(CmpOpExt::Uge),
            "bvslt" => Some(CmpOpExt::Slt),
            "bvsle" => Some(CmpOpExt::Sle),
            "bvsgt" => Some(CmpOpExt::Sgt),
            "bvsge" => Some(CmpOpExt::Sge),
            _ => None,
        };
        if let Some(c) = cmp {
            arity(n == 2)?;
            let (a, b) = (
                self.bv(sx, args[0].0, args[0].1)?,
                self.bv(sx, args[1].0, args[1].1)?,
            );
            return Ok(Val::Bool(self.cx.cmp(c, a, b)?));
        }
        match op {
            "bvnot" | "bvneg" => {
                arity(n == 1)?;
                let a = self.bv(sx, args[0].0, args[0].1)?;
                let u = if op == "bvnot" { UnOp::Not } else { UnOp::Neg };
                Ok(Val::Bv(self.cx.un(u, a)?))
            }
            "bvnand" | "bvnor" | "bvxnor" => {
                arity(n == 2)?;
                let (a, b) = (
                    self.bv(sx, args[0].0, args[0].1)?,
                    self.bv(sx, args[1].0, args[1].1)?,
                );
                let inner = match op {
                    "bvnand" => BinOp::And,
                    "bvnor" => BinOp::Or,
                    _ => BinOp::Xor,
                };
                let t = self.cx.bin(inner, a, b)?;
                Ok(Val::Bv(self.cx.un(UnOp::Not, t)?))
            }
            "bvnego" => {
                arity(n == 1)?;
                let a = self.bv(sx, args[0].0, args[0].1)?;
                let w = self.cx.width(a)?;
                let smin = self.cx.constant(&BitVec::smin(w))?;
                Ok(Val::Bool(self.cx.cmp(CmpOpExt::Eq, a, smin)?))
            }
            "bvuaddo" | "bvsaddo" | "bvusubo" | "bvssubo" | "bvumulo" | "bvsmulo" | "bvsdivo" => {
                arity(n == 2)?;
                let (a, b) = (
                    self.bv(sx, args[0].0, args[0].1)?,
                    self.bv(sx, args[1].0, args[1].1)?,
                );
                Ok(Val::Bool(overflows(self.cx, op, a, b)?))
            }
            "bvcomp" => {
                arity(n == 2)?;
                let (a, b) = (
                    self.bv(sx, args[0].0, args[0].1)?,
                    self.bv(sx, args[1].0, args[1].1)?,
                );
                Ok(Val::Bv(self.cx.cmp(CmpOpExt::Eq, a, b)?))
            }
            "bvsmod" => {
                arity(n == 2)?;
                let (s, t) = (
                    self.bv(sx, args[0].0, args[0].1)?,
                    self.bv(sx, args[1].0, args[1].1)?,
                );
                Ok(Val::Bv(smod(self.cx, s, t)?))
            }
            "concat" => {
                arity(n >= 2)?;
                let mut acc = self.bv(sx, args[0].0, args[0].1)?;
                for &(a, v) in &args[1..] {
                    let x = self.bv(sx, a, v)?;
                    acc = self.cx.concat(acc, x)?;
                }
                Ok(Val::Bv(acc))
            }
            "not" => {
                arity(n == 1)?;
                let a = self.boolean(sx, args[0].0, args[0].1)?;
                Ok(Val::Bool(self.cx.un(UnOp::Not, a)?))
            }
            "and" | "or" | "xor" => {
                arity(n >= 2)?;
                let b = match op {
                    "and" => BinOp::And,
                    "or" => BinOp::Or,
                    _ => BinOp::Xor,
                };
                let mut acc = self.boolean(sx, args[0].0, args[0].1)?;
                for &(a, v) in &args[1..] {
                    let x = self.boolean(sx, a, v)?;
                    acc = self.cx.bin(b, acc, x)?;
                }
                Ok(Val::Bool(acc))
            }
            "=>" => {
                // Right-associative: `a => (b => c)`.
                arity(n >= 2)?;
                let mut acc = self.boolean(sx, args[n - 1].0, args[n - 1].1)?;
                for &(a, v) in args[..n - 1].iter().rev() {
                    let x = self.boolean(sx, a, v)?;
                    let nx = self.cx.un(UnOp::Not, x)?;
                    acc = self.cx.bin(BinOp::Or, nx, acc)?;
                }
                Ok(Val::Bool(acc))
            }
            "=" | "distinct" => {
                arity(n >= 2)?;
                let kind = |v: Val| match v {
                    Val::Bool(_) => 0,
                    Val::Bv(_) => 1,
                    Val::Fp(..) => 2,
                    Val::Rm(_) | Val::RmVar(_) => 3,
                    Val::Array(..) | Val::Arr(_) => 4,
                    Val::Wide(_) => 5,
                    Val::Int(_) => 6,
                };
                if args.iter().any(|&(_, v)| kind(v) != kind(args[0].1)) {
                    return Err(sx.err(id, "operands of different sorts"));
                }
                if kind(args[0].1) == 4 {
                    let sort = self.array_sort(args[0].1)?;
                    for &(a, v) in &args[1..] {
                        if self.array_sort(v)? != sort {
                            return Err(sx.err(a, "operands of different sorts"));
                        }
                    }
                    // `=` chains; `distinct` is pairwise.
                    let mut acc = self.cx.bool(true)?;
                    for i in 0..n {
                        let others = if op == "=" {
                            i + 1..(i + 2).min(n)
                        } else {
                            i + 1..n
                        };
                        for j in others {
                            let mut e = self.array_equal(args[i].1, args[j].1)?;
                            if op == "distinct" {
                                e = self.cx.un(UnOp::Not, e)?;
                            }
                            acc = self.cx.bin(BinOp::And, acc, e)?;
                        }
                    }
                    return Ok(Val::Bool(acc));
                }
                if let Val::Fp(_, f) = args[0].1 {
                    return self.float_equality(sx, id, op, f, args);
                }
                // Modes of which one is not a constant: by their numbers.
                let numbered: Vec<(u32, Val)>;
                let mut args = args;
                if kind(args[0].1) == 3 && args.iter().any(|&(_, v)| matches!(v, Val::RmVar(_))) {
                    let w = Width::new(3).unwrap_or(Width::W1);
                    let mut out = Vec::with_capacity(n);
                    for &(a, v) in args {
                        out.push((
                            a,
                            match v {
                                Val::Rm(m) => Val::RmVar(self.mode_number(m, w)?),
                                v => v,
                            },
                        ));
                    }
                    numbered = out;
                    args = &numbered;
                }
                if let Val::Rm(_) = args[0].1 {
                    let all_same = args.iter().all(|&(_, v)| v == args[0].1);
                    let distinct = (0..n).all(|i| (i + 1..n).all(|j| args[i].1 != args[j].1));
                    return Ok(Val::Bool(self.cx.bool(if op == "=" {
                        all_same
                    } else {
                        distinct
                    })?));
                }
                let mut pairs = Vec::new();
                if op == "=" {
                    pairs.extend((1..n).map(|k| (k - 1, k)));
                } else {
                    for i in 0..n {
                        pairs.extend((i + 1..n).map(|j| (i, j)));
                    }
                }
                let c = if op == "=" {
                    CmpOpExt::Eq
                } else {
                    CmpOpExt::Ne
                };
                let mut acc: Option<Expr> = None;
                for (i, j) in pairs {
                    let (Some(a), Some(b)) = (args[i].1.expr(), args[j].1.expr()) else {
                        return Err(sx.err(id, "operands without a value"));
                    };
                    let t = self.cx.cmp(c, a, b)?;
                    acc = Some(match acc {
                        Some(x) => self.cx.bin(BinOp::And, x, t)?,
                        None => t,
                    });
                }
                acc.map(Val::Bool)
                    .ok_or_else(|| sx.err(id, "wrong number of operands"))
            }
            "ite" => {
                arity(n == 3)?;
                let c = self.boolean(sx, args[0].0, args[0].1)?;
                let (t, f) = (args[1].1, args[2].1);
                match (t, f) {
                    (Val::Bv(a), Val::Bv(b)) => Ok(Val::Bv(self.cx.select(c, a, b)?)),
                    (Val::Bool(a), Val::Bool(b)) => Ok(Val::Bool(self.cx.select(c, a, b)?)),
                    (Val::Fp(a, fa), Val::Fp(b, fb)) if fa == fb => {
                        Ok(Val::Fp(self.cx.select(c, a, b)?, fa))
                    }
                    (Val::Rm(a), Val::Rm(b)) if a == b => Ok(Val::Rm(a)),
                    (Val::Rm(_) | Val::RmVar(_), Val::Rm(_) | Val::RmVar(_)) => {
                        // A mode chosen by a condition: the number of the one chosen.
                        let w = Width::new(3).unwrap_or(Width::W1);
                        let mut number = |v: Val| match v {
                            Val::Rm(m) => self.mode_number(m, w),
                            Val::RmVar(e) => Ok(e),
                            _ => unreachable!("matched above"),
                        };
                        let (a, b) = (number(t)?, number(f)?);
                        Ok(Val::RmVar(self.cx.select(c, a, b)?))
                    }
                    (Val::Array(..) | Val::Arr(_), Val::Array(..) | Val::Arr(_)) => {
                        if self.array_sort(t)? != self.array_sort(f)? {
                            return Err(sx.err(id, "ite arms of different sorts"));
                        }
                        self.env.arrs.push(Arr::Ite(c, t, f));
                        Ok(Val::Arr(self.env.arrs.len() as u32 - 1))
                    }
                    _ => Err(sx.err(id, "ite arms of different sorts")),
                }
            }
            _ => self.expand(sx, id, op, args),
        }
    }
}

// ----- floating point ------------------------------------------------------------------------

/// The float `±2^k` of a format, or `None` when it is beyond the largest finite value.
fn power_of_two(f: FpFormat, k: u32, negative: bool) -> Option<BitVec> {
    let bias = (1u32 << (f.eb() - 1)) - 1;
    if k > bias {
        return None;
    }
    let w = f.width();
    // The exponent field `k + bias` above a zero fraction of `sb - 1` bits, and the sign.
    let mut limbs = vec![0u64; usize::from(w.bits()).div_ceil(64)];
    let mut set = |bit: u32| limbs[(bit / 64) as usize] |= 1 << (bit % 64);
    (0..f.eb())
        .filter(|i| (k + bias) >> i & 1 == 1)
        .for_each(|i| set(f.sb() - 1 + i));
    if negative {
        set(u32::from(w.bits()) - 1);
    }
    Some(BitVec::wrapping_from_limbs(w, &limbs))
}

/// The rounding modes, in the order of the numbers a rounding-mode variable has for them.
pub(super) const MODES: [RoundingMode; 5] = [
    RoundingMode::Rne,
    RoundingMode::Rna,
    RoundingMode::Rtp,
    RoundingMode::Rtn,
    RoundingMode::Rtz,
];

/// A rounding mode by one of SMT-LIB's names for it.
fn rounding_mode(s: &str) -> Option<RoundingMode> {
    Some(match s {
        "RNE" | "roundNearestTiesToEven" => RoundingMode::Rne,
        "RNA" | "roundNearestTiesToAway" => RoundingMode::Rna,
        "RTP" | "roundTowardPositive" => RoundingMode::Rtp,
        "RTN" | "roundTowardNegative" => RoundingMode::Rtn,
        "RTZ" | "roundTowardZero" => RoundingMode::Rtz,
        _ => return None,
    })
}

/// Whether two forms are the same text (up to blanks and comments).
fn same(sx: &Sx<'_>, a: u32, b: u32) -> bool {
    match (sx.tok(a), sx.tok(b)) {
        (Tok::Sym(x), Tok::Sym(y)) | (Tok::Lit(x), Tok::Lit(y)) => x == y,
        (Tok::List(..), Tok::List(..)) => match (sx.list(a), sx.list(b)) {
            (Some(ka), Some(kb)) => {
                ka.len() == kb.len() && ka.iter().zip(kb).all(|(&x, &y)| same(sx, x, y))
            }
            _ => false,
        },
        _ => false,
    }
}

/// Little-endian limbs of a decimal digit string (at most 1,280 bits).
fn decimal_limbs(digits: &str) -> Option<Vec<u64>> {
    let mut limbs = vec![0u64; 21];
    for d in digits.bytes() {
        if !d.is_ascii_digit() {
            return None;
        }
        let mut carry = u128::from(d - b'0');
        for l in &mut limbs {
            let x = u128::from(*l) * 10 + carry;
            *l = x as u64;
            carry = x >> 64;
        }
        if carry != 0 || limbs[20] != 0 {
            return None;
        }
    }
    limbs.truncate(20);
    Some(limbs)
}

/// A real constant as `(negative, numerator, denominator)`: a numeral, a decimal, `(- r)`, or
/// `(/ n m)` of numerals.
fn real_value(sx: &Sx<'_>, id: u32) -> Option<(bool, Vec<u64>, Vec<u64>)> {
    match sx.tok(id) {
        Tok::Lit(s) => {
            let (int, frac) = s.split_once('.').unwrap_or((s, ""));
            if int.is_empty() || !int.bytes().all(|c| c.is_ascii_digit()) {
                return None;
            }
            let num = decimal_limbs(&format!("{int}{frac}"))?;
            let den = decimal_limbs(&format!("1{}", "0".repeat(frac.len())))?;
            Some((false, num, den))
        }
        Tok::List(..) => {
            let k = sx.list(id)?;
            match (sx.sym(*k.first()?), k.len()) {
                (Some("-"), 2) => {
                    let (neg, n, d) = real_value(sx, k[1])?;
                    Some((!neg, n, d))
                }
                (Some("/"), 3) => {
                    let (na, a, one_a) = real_value(sx, k[1])?;
                    let (nb, b, one_b) = real_value(sx, k[2])?;
                    // Numerals only (a denominator of 1).
                    let is_one = |v: &[u64]| v[0] == 1 && v[1..].iter().all(|&l| l == 0);
                    if !is_one(&one_a) || !is_one(&one_b) {
                        return None;
                    }
                    Some((na != nb, a, b))
                }
                _ => None,
            }
        }
        Tok::Sym(_) => None,
    }
}

impl<'s> State<'_, 's> {
    fn format(&self, sx: &Sx<'s>, id: u32, eb: u32, sb: u32) -> Result<FpFormat, Error> {
        let (eb, sb) = (sx.numeral(eb)?, sx.numeral(sb)?);
        FpFormat::new(eb, sb).map_err(|e| sx.err(id, &e.to_string()))
    }

    fn rm(&mut self, sx: &Sx<'s>, id: u32) -> Result<RoundingMode, Error> {
        match self.term(sx, id)? {
            Val::Rm(m) => Ok(m),
            _ => Err(sx.err(id, "expected a rounding mode")),
        }
    }

    fn float(&self, sx: &Sx<'s>, id: u32, v: Val) -> Result<(Expr, FpFormat), Error> {
        match v {
            Val::Fp(e, f) => Ok((e, f)),
            _ => Err(sx.err(id, "expected a float")),
        }
    }

    /// The floats of `args`, which must share one format.
    fn floats(&self, sx: &Sx<'s>, args: &[(u32, Val)]) -> Result<(Vec<Expr>, FpFormat), Error> {
        let mut out = Vec::with_capacity(args.len());
        let mut format = None;
        for &(a, v) in args {
            let (e, f) = self.float(sx, a, v)?;
            if format.is_some_and(|g| g != f) {
                return Err(sx.err(a, "floats of different formats"));
            }
            format = Some(f);
            out.push(e);
        }
        let f = format.ok_or_else(|| Error::Unsupported("no operands".into()))?;
        Ok((out, f))
    }

    /// `((_ to_fp eb sb) …)` (from bits, a float, a signed integer or a real constant),
    /// `((_ to_fp_unsigned eb sb) rm x)`, `((_ fp.to_ubv m) rm x)` and `((_ fp.to_sbv m) rm x)`.
    fn indexed_float(
        &mut self,
        sx: &Sx<'s>,
        id: u32,
        op: &str,
        nums: &[u32],
        args: &[u32],
    ) -> Result<Val, Error> {
        let fmt = |eb: u32, sb: u32| FpFormat::new(eb, sb).map_err(|e| sx.err(id, &e.to_string()));
        match (op, nums, args) {
            ("to_fp", &[eb, sb], &[x]) => {
                let f = fmt(eb, sb)?;
                let v = self.term(sx, x)?;
                let e = self.bv(sx, x, v)?;
                if self.cx.width(e)? != f.width() {
                    return Err(sx.err(x, "the bit-vector is not the format's width"));
                }
                Ok(Val::Fp(e, f))
            }
            ("to_fp" | "to_fp_unsigned", &[eb, sb], &[m, x]) => {
                let f = fmt(eb, sb)?;
                let rm = self.rm(sx, m)?;
                if op == "to_fp"
                    && let Some((negative, num, den)) = real_value(sx, x)
                {
                    let v = f.round_rational(rm, negative, &num, &den).ok_or_else(|| {
                        Error::Unsupported("a real constant too large to round exactly".into())
                    })?;
                    return Ok(Val::Fp(self.cx.constant(&v)?, f));
                }
                let v = self.term(sx, x)?;
                let e = match (op, v) {
                    ("to_fp", Val::Fp(e, from)) => {
                        self.cx.fp(FpOp::Convert { to: f, rm }, from, &[e])?
                    }
                    ("to_fp", Val::Bv(e)) => self.cx.fp(FpOp::FromSInt(rm), f, &[e])?,
                    ("to_fp_unsigned", Val::Bv(e)) => self.cx.fp(FpOp::FromUInt(rm), f, &[e])?,
                    _ => return Err(sx.err(x, "expected a float, a bit-vector or a real")),
                };
                Ok(Val::Fp(e, f))
            }
            ("fp.to_ubv" | "fp.to_sbv", &[m], &[r, x]) => {
                let w = sx.width(id, m)?;
                let rm = self.rm(sx, r)?;
                let v = self.term(sx, x)?;
                let (e, f) = self.float(sx, x, v)?;
                let op = if op == "fp.to_sbv" {
                    FpOp::ToSInt(rm, w)
                } else {
                    FpOp::ToUInt(rm, w)
                };
                let bits = self.cx.fp(op, f, &[e])?;
                if !self.env.session {
                    return Ok(Val::Bv(bits));
                }
                // SMT-LIB leaves the conversion of a NaN, an infinity or a value out of the
                // target's range open: any value, here a symbol of this application's own.
                let signed = matches!(op, FpOp::ToSInt(..));
                let rounded = self.cx.fp(FpOp::RoundToIntegral(rm), f, &[e])?;
                let n = u32::from(w.bits());
                let mut ok = {
                    let nan = self.cx.fp_test(f, FpTest::Nan, e)?;
                    let inf = self.cx.fp_test(f, FpTest::Infinite, e)?;
                    let either = self.cx.bin(BinOp::Or, nan, inf)?;
                    self.cx.un(UnOp::Not, either)?
                };
                let low = if signed {
                    power_of_two(f, n - 1, true)
                } else {
                    Some(f.zero(false))
                };
                let bounds = [
                    (low, FpCmpOp::Ge),
                    (
                        power_of_two(f, if signed { n - 1 } else { n }, false),
                        FpCmpOp::Lt,
                    ),
                ];
                for (bound, cmp) in bounds {
                    // A bound beyond the format's largest finite value holds of every one.
                    let Some(bound) = bound else { continue };
                    let bound = self.cx.constant(&bound)?;
                    let within = self.cx.fp_cmp(f, cmp, rounded, bound)?;
                    ok = self.cx.bin(BinOp::And, ok, within)?;
                }
                let open = format!("{}!unspecified!{}", sx.text(id), bits.index());
                let any = self.cx.symbol(SymbolKey::from(open.as_str()), w)?;
                Ok(Val::Bv(self.cx.select(ok, bits, any)?))
            }
            _ => Err(sx.err(id, "wrong operands of a floating-point conversion")),
        }
    }

    /// The FloatingPoint theory's operators (and z3's `fp.to_ieee_bv`).
    fn apply_float(
        &mut self,
        sx: &Sx<'s>,
        id: u32,
        op: &str,
        args: &[(u32, Val)],
    ) -> Result<Val, Error> {
        let wrong = || sx.err(id, "wrong operands");
        if op == "fp" {
            let [(a0, v0), (a1, v1), (a2, v2)] = args else {
                return Err(wrong());
            };
            let (s, e, m) = (
                self.bv(sx, *a0, *v0)?,
                self.bv(sx, *a1, *v1)?,
                self.bv(sx, *a2, *v2)?,
            );
            let (ws, we, wm) = (
                self.cx.width(s)?.bits(),
                self.cx.width(e)?.bits(),
                self.cx.width(m)?.bits(),
            );
            if ws != 1 {
                return Err(sx.err(*a0, "the sign is 1 bit"));
            }
            let f = FpFormat::new(u32::from(we), u32::from(wm) + 1)
                .map_err(|er| sx.err(id, &er.to_string()))?;
            let se = self.cx.concat(s, e)?;
            return Ok(Val::Fp(self.cx.concat(se, m)?, f));
        }
        let rounding = matches!(
            op,
            "fp.add" | "fp.sub" | "fp.mul" | "fp.div" | "fp.fma" | "fp.sqrt" | "fp.roundToIntegral"
        );
        let (rm, rest) = if rounding {
            let Some((&(r, v), rest)) = args.split_first() else {
                return Err(wrong());
            };
            match v {
                Val::Rm(m) => (m, rest),
                _ => return Err(sx.err(r, "expected a rounding mode")),
            }
        } else {
            (RoundingMode::Rne, args)
        };
        let (xs, f) = self.floats(sx, rest)?;
        let n = xs.len();
        let float = |cx: &mut Context, o: FpOp, xs: &[Expr]| cx.fp(o, f, xs).map(|e| Val::Fp(e, f));
        match (op, n) {
            ("fp.abs", 1) => Ok(Val::Fp(self.cx.fp_abs(f, xs[0])?, f)),
            ("fp.neg", 1) => Ok(Val::Fp(self.cx.fp_neg(f, xs[0])?, f)),
            ("fp.add", 2) => float(self.cx, FpOp::Add(rm), &xs),
            ("fp.sub", 2) => Ok(Val::Fp(self.cx.fp_sub(f, rm, xs[0], xs[1])?, f)),
            ("fp.mul", 2) => float(self.cx, FpOp::Mul(rm), &xs),
            ("fp.div", 2) => float(self.cx, FpOp::Div(rm), &xs),
            ("fp.fma", 3) => float(self.cx, FpOp::Fma(rm), &xs),
            ("fp.sqrt", 1) => float(self.cx, FpOp::Sqrt(rm), &xs),
            ("fp.roundToIntegral", 1) => float(self.cx, FpOp::RoundToIntegral(rm), &xs),
            ("fp.rem", 2) => float(self.cx, FpOp::Rem, &xs),
            // SMT-LIB leaves the zero of min(+0, −0) open: bitwright's −0 < +0 is one choice.
            ("fp.min" | "fp.max", 2) => {
                let o = if op == "fp.min" { FpOp::Min } else { FpOp::Max };
                let r = self.cx.fp(o, f, &xs)?;
                if !self.env.session {
                    return Ok(Val::Fp(r, f));
                }
                // A solver must leave it open: of zeros of different signs either may be
                // the result, one choice for each order of the signs (the operation is a
                // function), which two symbols per operation and format stand for.
                let zeros = {
                    let (a, b) = (
                        self.cx.fp_test(f, FpTest::Zero, xs[0])?,
                        self.cx.fp_test(f, FpTest::Zero, xs[1])?,
                    );
                    self.cx.bin(BinOp::And, a, b)?
                };
                let (na, nb) = (
                    self.cx.fp_test(f, FpTest::Negative, xs[0])?,
                    self.cx.fp_test(f, FpTest::Negative, xs[1])?,
                );
                let differ = self.cx.bin(BinOp::Xor, na, nb)?;
                let mixed = self.cx.bin(BinOp::And, zeros, differ)?;
                let mut choice = |order: &str| {
                    let name = format!("{op}!unspecified!{}.{}!{order}", f.eb(), f.sb());
                    self.cx.symbol(SymbolKey::from(name.as_str()), Width::W1)
                };
                let (neg_first, pos_first) = (choice("-+")?, choice("+-")?);
                let negative = self.cx.select(na, neg_first, pos_first)?;
                let (minus, plus) = (
                    self.cx.constant(&f.zero(true))?,
                    self.cx.constant(&f.zero(false))?,
                );
                let zero = self.cx.select(negative, minus, plus)?;
                Ok(Val::Fp(self.cx.select(mixed, zero, r)?, f))
            }
            ("fp.leq" | "fp.lt" | "fp.geq" | "fp.gt" | "fp.eq", 2..) => {
                // Chainable: every adjacent pair.
                let c = match op {
                    "fp.leq" => FpCmpOp::Le,
                    "fp.lt" => FpCmpOp::Lt,
                    "fp.geq" => FpCmpOp::Ge,
                    "fp.gt" => FpCmpOp::Gt,
                    _ => FpCmpOp::Eq,
                };
                let mut acc: Option<Expr> = None;
                for pair in xs.windows(2) {
                    let t = self.cx.fp_cmp(f, c, pair[0], pair[1])?;
                    acc = Some(match acc {
                        Some(a) => self.cx.bin(BinOp::And, a, t)?,
                        None => t,
                    });
                }
                acc.map(Val::Bool).ok_or_else(wrong)
            }
            (
                "fp.isNormal" | "fp.isSubnormal" | "fp.isZero" | "fp.isInfinite" | "fp.isNaN"
                | "fp.isNegative" | "fp.isPositive",
                1,
            ) => {
                let t = match op {
                    "fp.isNormal" => FpTest::Normal,
                    "fp.isSubnormal" => FpTest::Subnormal,
                    "fp.isZero" => FpTest::Zero,
                    "fp.isInfinite" => FpTest::Infinite,
                    "fp.isNaN" => FpTest::Nan,
                    "fp.isNegative" => FpTest::Negative,
                    _ => FpTest::Positive,
                };
                Ok(Val::Bool(self.cx.fp_test(f, t, xs[0])?))
            }
            ("fp.to_ieee_bv", 1) => {
                // Every NaN reads as the canonical one.
                let nan = self.cx.fp_test(f, FpTest::Nan, xs[0])?;
                let canonical = self.cx.constant(&f.nan())?;
                Ok(Val::Bv(self.cx.select(nan, canonical, xs[0])?))
            }
            _ => Err(Error::Unsupported(format!(
                "the floating-point operator {op} with {n} operand(s)"
            ))),
        }
    }

    /// SMT-LIB's `=` and `distinct` on floats: equal values, all NaNs being one value.
    fn float_equality(
        &mut self,
        sx: &Sx<'s>,
        id: u32,
        op: &str,
        f: FpFormat,
        args: &[(u32, Val)],
    ) -> Result<Val, Error> {
        let (xs, g) = self.floats(sx, args)?;
        if g != f {
            return Err(sx.err(id, "floats of different formats"));
        }
        let n = xs.len();
        let pairs: Vec<(usize, usize)> = if op == "=" {
            (1..n).map(|k| (k - 1, k)).collect()
        } else {
            (0..n)
                .flat_map(|i| (i + 1..n).map(move |j| (i, j)))
                .collect()
        };
        let mut acc: Option<Expr> = None;
        for (i, j) in pairs {
            let same_bits = self.cx.cmp(CmpOpExt::Eq, xs[i], xs[j])?;
            let na = self.cx.fp_test(f, FpTest::Nan, xs[i])?;
            let nb = self.cx.fp_test(f, FpTest::Nan, xs[j])?;
            let both_nan = self.cx.bin(BinOp::And, na, nb)?;
            let equal = self.cx.bin(BinOp::Or, same_bits, both_nan)?;
            let t = if op == "=" {
                equal
            } else {
                self.cx.un(UnOp::Not, equal)?
            };
            acc = Some(match acc {
                Some(a) => self.cx.bin(BinOp::And, a, t)?,
                None => t,
            });
        }
        acc.map(Val::Bool)
            .ok_or_else(|| sx.err(id, "wrong number of operands"))
    }

    /// The exporter's naming of a float result's bits,
    /// `(ite (fp.isNaN T) (= c NAN) (= ((_ to_fp eb sb) c) T))` with `c` a declared bit-vector
    /// constant no term has read yet, `T` and `NAN` included: read as the definition of `c` (the
    /// bits of `T`, a NaN as
    /// `NAN`), so an exported script reads back to its expressions. Returns whether it was one.
    fn float_bits(&mut self, sx: &Sx<'s>, id: u32) -> Result<bool, Error> {
        let Some(&[ite, cond, then, els]) = sx.list(id) else {
            return Ok(false);
        };
        let (Some(&[isnan, t1]), Some(&[eq1, c1, nan]), Some(&[eq2, conv, t2])) =
            (sx.list(cond), sx.list(then), sx.list(els))
        else {
            return Ok(false);
        };
        if sx.sym(ite) != Some("ite")
            || sx.sym(isnan) != Some("fp.isNaN")
            || sx.sym(eq1) != Some("=")
            || sx.sym(eq2) != Some("=")
            || !same(sx, t1, t2)
        {
            return Ok(false);
        }
        let Some(name) = sx.sym(c1) else {
            return Ok(false);
        };
        let Some(&[head, c2]) = sx.list(conv) else {
            return Ok(false);
        };
        let Some(&[u, to_fp, _, _]) = sx.list(head) else {
            return Ok(false);
        };
        if sx.sym(u) != Some("_") || sx.sym(to_fp) != Some("to_fp") || sx.sym(c2) != Some(name) {
            return Ok(false);
        }
        let Some(&(Val::Bv(symbol), read)) = self.env.globals.get(name) else {
            return Ok(false);
        };
        if read || self.scope.get(name).is_some() {
            return Ok(false);
        }
        let Val::Fp(e, f) = self.term(sx, t1)? else {
            return Ok(false);
        };
        let nan_v = self.term(sx, nan)?;
        let Val::Bv(nan_e) = nan_v else {
            return Ok(false);
        };
        if self.cx.width(symbol)? != f.width() || self.cx.width(nan_e)? != f.width() {
            return Ok(false);
        }
        // `T` or `NAN` may themselves read `c`: then the assertion constrains `c` and does not
        // define it, and reading it as a definition would drop the constraint.
        if self.env.globals.get(name).is_none_or(|&(_, read)| read) {
            return Ok(false);
        }
        // A floating-point operation's NaN is already the canonical one.
        let canonical = self.cx.as_const(nan_e)? == Some(f.nan())
            && (self.cx.as_const(e)?.is_some()
                || matches!(self.cx.view(e)?, crate::View::Fp { .. }));
        let bits = if canonical {
            e
        } else {
            let t = self.cx.fp_test(f, FpTest::Nan, e)?;
            self.cx.select(t, nan_e, e)?
        };
        (self.env.globals).insert(name.to_string(), (Val::Bv(bits), false));
        self.env.out.symbols.retain(|(n, _)| n != name);
        Ok(true)
    }
}

/// SMT-LIB's overflow predicates of two operands: whether the exact result of the operation
/// is outside the range of the width, unsigned (`u`) or two's complement (`s`).
fn overflows(cx: &mut Context, op: &str, a: Expr, b: Expr) -> Result<Expr, Error> {
    let w = cx.width(a)?;
    let zero = cx.constant(&BitVec::zero(w))?;
    // The sign bit of `e`, as a Boolean.
    let negative = |cx: &mut Context, e: Expr| cx.cmp(CmpOpExt::Slt, e, zero);
    match op {
        // The sum wrapped below an operand.
        "bvuaddo" => {
            let sum = cx.bin(BinOp::Add, a, b)?;
            cx.cmp(CmpOpExt::Ult, sum, a)
        }
        "bvusubo" => cx.cmp(CmpOpExt::Ult, a, b),
        // Operands of one sign, a sum of the other.
        "bvsaddo" => {
            let sum = cx.bin(BinOp::Add, a, b)?;
            let (x, y) = (cx.bin(BinOp::Xor, a, sum)?, cx.bin(BinOp::Xor, b, sum)?);
            let both = cx.bin(BinOp::And, x, y)?;
            negative(cx, both)
        }
        // Operands of different signs, a difference of the subtrahend's.
        "bvssubo" => {
            let diff = cx.bin(BinOp::Sub, a, b)?;
            let (x, y) = (cx.bin(BinOp::Xor, a, b)?, cx.bin(BinOp::Xor, a, diff)?);
            let both = cx.bin(BinOp::And, x, y)?;
            negative(cx, both)
        }
        // The high half of the product is not the extension of its low half.
        "bvumulo" => {
            let hi = cx.bin(BinOp::UMulHi, a, b)?;
            cx.cmp(CmpOpExt::Ne, hi, zero)
        }
        "bvsmulo" => {
            let (hi, lo) = (cx.bin(BinOp::SMulHi, a, b)?, cx.bin(BinOp::Mul, a, b)?);
            let sign = cx.constant(&BitVec::wrapping_from_u64(w, u64::from(w.bits() - 1)))?;
            let ext = cx.bin(BinOp::AShr, lo, sign)?;
            cx.cmp(CmpOpExt::Ne, hi, ext)
        }
        // The one quotient out of range: the least value by -1.
        _ => {
            let (smin, ones) = (
                cx.constant(&BitVec::smin(w))?,
                cx.constant(&BitVec::ones(w))?,
            );
            let (x, y) = (
                cx.cmp(CmpOpExt::Eq, a, smin)?,
                cx.cmp(CmpOpExt::Eq, b, ones)?,
            );
            cx.bin(BinOp::And, x, y)
        }
    }
}

/// SMT-LIB's `bvsmod`: the remainder taking the divisor's sign.
fn smod(cx: &mut Context, s: Expr, t: Expr) -> Result<Expr, Error> {
    let w = cx.width(s)?;
    let zero = cx.zero(w)?;
    let ms = cx.cmp(CmpOpExt::Slt, s, zero)?;
    let mt = cx.cmp(CmpOpExt::Slt, t, zero)?;
    let ns = cx.un(UnOp::Neg, s)?;
    let nt = cx.un(UnOp::Neg, t)?;
    let abs_s = cx.select(ms, ns, s)?;
    let abs_t = cx.select(mt, nt, t)?;
    let u = cx.bin(BinOp::URem, abs_s, abs_t)?;
    let nu = cx.un(UnOp::Neg, u)?;
    let u_is_0 = cx.cmp(CmpOpExt::Eq, u, zero)?;
    let neg_u_plus_t = cx.bin(BinOp::Add, nu, t)?;
    let u_plus_t = cx.bin(BinOp::Add, u, t)?;
    // (ms, mt): (0,0) u; (1,0) −u + t; (0,1) u + t; (1,1) −u.
    let if_ms = cx.select(mt, nu, neg_u_plus_t)?;
    let if_not_ms = cx.select(mt, u_plus_t, u)?;
    let r = cx.select(ms, if_ms, if_not_ms)?;
    cx.select(u_is_0, u, r)
}

/// The symbol key for an SMT-LIB name: `#k` and `$k` are integer and fresh keys.
pub(super) fn key_of(name: &str) -> SymbolKey {
    let num = |s: &str| {
        (!s.is_empty()
            && s.bytes().all(|c| c.is_ascii_digit())
            && (s == "0" || !s.starts_with('0')))
        .then(|| s.parse::<u64>().ok())
        .flatten()
    };
    if let Some(k) = name.strip_prefix('#').and_then(num) {
        SymbolKey::U64(k)
    } else if let Some(k) = name.strip_prefix('$').and_then(num) {
        SymbolKey::Fresh(k)
    } else {
        SymbolKey::from(name)
    }
}

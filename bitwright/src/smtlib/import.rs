//! SMT-LIB 2.6 import of a QF_BV subset, and of floating-point (QF_BVFP) terms.

use std::collections::HashMap;

use crate::error::Error;
use crate::expr::{Context, Expr};
use crate::fp::{FpCmpOp, FpFormat, FpOp, FpTest, RoundingMode};
use crate::ops::{BinOp, CmpOpExt, UnOp};
use crate::text::SyntaxError;
use crate::{BitVec, SymbolKey, Width};

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
/// Accepted: `set-logic`, `set-info`, `set-option`, `declare-const`, `declare-fun` and
/// `define-fun` without parameters, `assert`, and the query commands (`check-sat`, `get-model`,
/// `get-value`, `exit`, `echo`), which are ignored. Sorts are `Bool` and `(_ BitVec n)` with
/// `1 ≤ n ≤ 512`. Terms are literals (`#b…`, `#x…`, `(_ bvN n)`), `let`, `ite`, `=`,
/// `distinct`, the core Boolean operators, and every operator of the QF_BV theory and its
/// extensions (`bvnand`, `bvnor`, `bvxnor`, `bvcomp`, `bvsmod`, the `u`/`s` comparisons,
/// `repeat`, `rotate_left`, `rotate_right`, `zero_extend`, `sign_extend`, `extract`).
///
/// Floats: the sorts `(_ FloatingPoint eb sb)`, `Float16`, `Float32`, `Float64`, `Float128`
/// (a float constant is a symbol of `eb + sb` bits holding its encoding) and `RoundingMode`
/// (its five constants, by either name; rounding-mode variables are refused); `(fp s e m)`,
/// `(_ +zero eb sb)`, `-zero`, `+oo`, `-oo`, `NaN`; every operator of the FloatingPoint
/// theory, the comparisons chainable; `to_fp` from bits, a float, a signed integer or a real
/// constant (a numeral, a decimal, `(- r)`, `(/ n m)`), `to_fp_unsigned`, `fp.to_ubv` and
/// `fp.to_sbv` (saturating, as bitwright defines them), and z3's `fp.to_ieee_bv` (a NaN as the
/// canonical one). `=` on floats treats every NaN as one value. What SMT-LIB leaves open
/// (the zero `fp.min` of `+0` and `−0` returns, conversions out of range) takes bitwright's
/// definitions.
///
/// Arrays (QF_ABV): the sort `(Array (_ BitVec n) (_ BitVec m))`, declared constants of it,
/// `select` and `store`, read as [`memory`](crate::memory) loads and stores (equality of
/// arrays, and arrays chosen by `ite`, are refused).
///
/// Anything else is an error. Symbol names `#k` and `$k` (decimal `k`) read as integer and
/// fresh keys, so an [`export`](super::export)ed script reads back to the same symbols.
pub fn import(cx: &mut Context, script: &str) -> Result<Import, Error> {
    // A syntax error anywhere fails the import before any command runs.
    check(script)?;
    let mut st = State {
        cx,
        globals: HashMap::new(),
        scope: Vec::new(),
        out: Import::default(),
    };
    // Then one top-level form at a time: memory is bounded by the largest command, not by the
    // script.
    let mut sx = Sx::default();
    let mut pos = 0;
    while let Some(top) = sx.read(script, &mut pos)? {
        st.command(&sx, top)?;
    }
    Ok(st.out)
}

// ----- the reader ----------------------------------------------------------------------------

/// A token of a form: a symbol or literal borrowed from the script, or a list.
#[derive(Copy, Clone, Debug)]
enum Tok<'s> {
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
/// building anything.
fn check(src: &str) -> Result<(), Error> {
    // The start of every open list.
    let mut open: Vec<usize> = Vec::new();
    let mut i = 0;
    while let Some((lexeme, start, end)) = lex(src, &mut i)? {
        match lexeme {
            Lex::Open => {
                if open.len() >= MAX_DEPTH {
                    return Err(syntax("nested too deeply", start, end));
                }
                open.push(start);
            }
            Lex::Close => {
                if open.pop().is_none() {
                    return Err(syntax("unbalanced ')'", start, end));
                }
            }
            Lex::Atom(_) => {}
        }
    }
    match open.last() {
        Some(&start) => Err(syntax("unbalanced '('", start, src.len())),
        None => Ok(()),
    }
}

/// One top-level form: its tokens with their spans in the script. The buffers are reused from
/// one form to the next.
#[derive(Default)]
struct Sx<'s> {
    nodes: Vec<(Tok<'s>, usize, usize)>,
    /// The elements of every list, each list's contiguous.
    kids: Vec<u32>,
    /// While reading: the elements of the open lists read so far.
    stack: Vec<u32>,
    /// While reading: each open list's start, and where its elements begin in `stack`.
    open: Vec<(usize, usize)>,
}

impl<'s> Sx<'s> {
    /// Reads the form at or after `*pos`, replacing the previous one: its root, or `None` at the
    /// end of the script.
    fn read(&mut self, src: &'s str, pos: &mut usize) -> Result<Option<u32>, Error> {
        self.nodes.clear();
        self.kids.clear();
        self.stack.clear();
        self.open.clear();
        while let Some((lexeme, start, end)) = lex(src, pos)? {
            let node = match lexeme {
                Lex::Open => {
                    if self.open.len() >= MAX_DEPTH {
                        return Err(syntax("nested too deeply", start, end));
                    }
                    self.open.push((start, self.stack.len()));
                    continue;
                }
                Lex::Close => {
                    let Some((list_start, base)) = self.open.pop() else {
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
            Some(&(start, _)) => Err(syntax("unbalanced '('", start, src.len())),
            None => Ok(None),
        }
    }

    fn tok(&self, id: u32) -> Tok<'s> {
        self.nodes[id as usize].0
    }

    fn err(&self, id: u32, message: &str) -> Error {
        let (_, s, e) = self.nodes[id as usize];
        syntax(message, s, e)
    }

    fn list(&self, id: u32) -> Option<&[u32]> {
        match self.tok(id) {
            Tok::List(a, b) => Some(&self.kids[a as usize..b as usize]),
            _ => None,
        }
    }

    fn sym(&self, id: u32) -> Option<&'s str> {
        match self.tok(id) {
            Tok::Sym(s) => Some(s),
            _ => None,
        }
    }

    fn name(&self, id: u32) -> Result<&'s str, Error> {
        self.sym(id)
            .ok_or_else(|| self.err(id, "expected a symbol"))
    }

    fn numeral(&self, id: u32) -> Result<u32, Error> {
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

    fn sort(&self, id: u32) -> Result<Sort, Error> {
        match self.sym(id) {
            Some("Bool") => return Ok(Sort::Bool),
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
            return Ok(Sort::Bv(self.width(k[2], n)?));
        }
        if let Some(k) = self.list(id)
            && k.len() == 3
            && self.sym(k[0]) == Some("Array")
        {
            return match (self.sort(k[1])?, self.sort(k[2])?) {
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
enum Val {
    Bv(Expr),
    Bool(Expr),
    Fp(Expr, FpFormat),
    Rm(RoundingMode),
    /// An array: a memory of [`Import::arrays`] at a version.
    Array(u32, crate::memory::Version),
}

impl Val {
    /// The expression of a value that has one (a rounding mode has none).
    fn expr(self) -> Option<Expr> {
        match self {
            Val::Bv(e) | Val::Bool(e) | Val::Fp(e, _) => Some(e),
            Val::Rm(_) | Val::Array(..) => None,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum Sort {
    Bool,
    Bv(Width),
    Fp(FpFormat),
    Rm,
    Array(Width, Width),
}

struct State<'a, 's> {
    cx: &'a mut Context,
    /// Declared and defined names, and whether a term has read each so far.
    globals: HashMap<&'s str, (Val, bool)>,
    /// `let` bindings, innermost last.
    scope: Vec<(&'s str, Val)>,
    out: Import,
}

impl<'s> State<'_, 's> {
    fn command(&mut self, sx: &Sx<'s>, id: u32) -> Result<(), Error> {
        let Some(k) = sx.list(id) else {
            return Err(sx.err(id, "expected a command"));
        };
        let Some((&head, args)) = k.split_first() else {
            return Err(sx.err(id, "empty command"));
        };
        match sx.sym(head) {
            Some(
                "set-logic" | "set-info" | "set-option" | "check-sat" | "get-model" | "get-value"
                | "exit" | "echo",
            ) => Ok(()),
            Some("declare-const") if args.len() == 2 => self.declare(sx, args[0], args[1]),
            Some("declare-fun") if args.len() == 3 => {
                if sx.list(args[1]).is_none_or(|p| !p.is_empty()) {
                    return Err(Error::Unsupported(
                        "declare-fun with parameters (uninterpreted functions)".into(),
                    ));
                }
                self.declare(sx, args[0], args[2])
            }
            Some("define-fun") if args.len() == 4 => {
                if sx.list(args[1]).is_none_or(|p| !p.is_empty()) {
                    return Err(Error::Unsupported("define-fun with parameters".into()));
                }
                let name = sx.name(args[0])?;
                let sort = sx.sort(args[2])?;
                let v = self.term(sx, args[3])?;
                self.check_sort(sx, args[3], v, sort)?;
                self.bind_global(sx, args[0], name, v)?;
                if let Some(e) = v.expr() {
                    self.out.definitions.push((name.to_string(), e));
                }
                Ok(())
            }
            Some("assert") if args.len() == 1 => {
                if self.float_bits(sx, args[0])? {
                    return Ok(());
                }
                let v = self.term(sx, args[0])?;
                let Val::Bool(e) = v else {
                    return Err(sx.err(args[0], "an assertion must be Boolean"));
                };
                self.out.assertions.push(e);
                Ok(())
            }
            Some(c) => Err(Error::Unsupported(format!(
                "the command {c} (or its arity)"
            ))),
            None => Err(sx.err(head, "expected a command name")),
        }
    }

    fn bind_global(&mut self, sx: &Sx<'s>, id: u32, name: &'s str, v: Val) -> Result<(), Error> {
        if self.globals.contains_key(name) {
            return Err(sx.err(id, "already declared"));
        }
        self.globals.insert(name, (v, false));
        Ok(())
    }

    fn declare(&mut self, sx: &Sx<'s>, name_id: u32, sort_id: u32) -> Result<(), Error> {
        let name = sx.name(name_id)?;
        let sort = sx.sort(sort_id)?;
        if let Sort::Array(i, e) = sort {
            let m = crate::memory::Memory::new(name, i, e, crate::memory::Endian::Little);
            let v = Val::Array(self.out.arrays.len() as u32, m.initial());
            self.out.arrays.push((name.to_string(), m));
            return self.bind_global(sx, name_id, name, v);
        }
        let key = key_of(name);
        let w = match sort {
            Sort::Bool => Width::W1,
            Sort::Bv(w) => w,
            Sort::Fp(f) => f.width(),
            Sort::Rm => {
                return Err(Error::Unsupported(
                    "rounding-mode variables (bitwright's rounding modes are constants)".into(),
                ));
            }
            Sort::Array(..) => unreachable!("declared above"),
        };
        let e = self.cx.symbol(key, w)?;
        let v = match sort {
            Sort::Bool => Val::Bool(e),
            Sort::Fp(f) => Val::Fp(e, f),
            _ => Val::Bv(e),
        };
        self.bind_global(sx, name_id, name, v)?;
        self.out.symbols.push((name.to_string(), e));
        Ok(())
    }

    fn check_sort(&self, sx: &Sx<'s>, id: u32, v: Val, sort: Sort) -> Result<(), Error> {
        let ok = match (v, sort) {
            (Val::Bool(_), Sort::Bool) | (Val::Rm(_), Sort::Rm) => true,
            (Val::Bv(e), Sort::Bv(w)) => self.cx.width(e)? == w,
            (Val::Fp(_, f), Sort::Fp(g)) => f == g,
            (Val::Array(m, _), Sort::Array(i, e)) => {
                let mem = &self.out.arrays[m as usize].1;
                mem.addr_width() == i && mem.cell_width() == e
            }
            _ => false,
        };
        if ok {
            Ok(())
        } else {
            Err(sx.err(id, "the term does not have the declared sort"))
        }
    }

    /// The value of a name a term reads, marking a global as read.
    fn lookup(&mut self, name: &str) -> Option<Val> {
        if let Some(&(_, v)) = self.scope.iter().rev().find(|(n, _)| *n == name) {
            return Some(v);
        }
        let (v, read) = self.globals.get_mut(name)?;
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

    fn term(&mut self, sx: &Sx<'s>, id: u32) -> Result<Val, Error> {
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
                if let Some(h) = sx.list(head) {
                    // An indexed operator applied: `((_ extract i j) t)`.
                    return self.indexed(sx, id, h, args);
                }
                match sx.sym(head) {
                    Some("_") => self.indexed_constant(sx, id, args),
                    Some("let") => self.let_(sx, id, args),
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

    fn let_(&mut self, sx: &Sx<'s>, id: u32, args: &[u32]) -> Result<Val, Error> {
        let [binds, body] = args else {
            return Err(sx.err(id, "let takes bindings and a body"));
        };
        let Some(bs) = sx.list(*binds) else {
            return Err(sx.err(*binds, "expected let bindings"));
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
        let depth = self.scope.len();
        self.scope.extend(new);
        let r = self.term(sx, *body);
        self.scope.truncate(depth);
        r
    }

    fn literal(&mut self, sx: &Sx<'s>, id: u32, s: &str) -> Result<Val, Error> {
        let (bits_per, digits) = if let Some(d) = s.strip_prefix("#b") {
            (1u32, d)
        } else if let Some(d) = s.strip_prefix("#x") {
            (4, d)
        } else {
            return Err(sx.err(id, "bare numerals are not bit-vectors (use (_ bvN n))"));
        };
        let n = (digits.len() as u32).saturating_mul(bits_per);
        let w = sx.width(id, n)?;
        let mut limbs = vec![0u64; (n as usize).div_ceil(64)];
        for (k, ch) in digits.bytes().rev().enumerate() {
            let d = (ch as char)
                .to_digit(1 << bits_per)
                .ok_or_else(|| sx.err(id, "bad digit"))?;
            let bit = k * bits_per as usize;
            limbs[bit / 64] |= u64::from(d) << (bit % 64);
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
        let w = sx.width(*n, nn)?;
        // Decimal into limbs, refusing a value that does not fit.
        let mut limbs = vec![0u64; usize::from(w.bits()).div_ceil(64) + 1];
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
        let bits = usize::from(w.bits());
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
        if op == "select" || op == "store" {
            arity(n == if op == "select" { 2 } else { 3 })?;
            let Val::Array(m, at) = args[0].1 else {
                return Err(sx.err(args[0].0, "expected an array"));
            };
            let i = self.bv(sx, args[1].0, args[1].1)?;
            if op == "select" {
                let mem = &mut self.out.arrays[m as usize].1;
                return Ok(Val::Bv(mem.load(self.cx, at, i, 1)?));
            }
            let v = self.bv(sx, args[2].0, args[2].1)?;
            let mem = &mut self.out.arrays[m as usize].1;
            if self.cx.width(v)? != mem.cell_width() {
                return Err(sx.err(
                    args[2].0,
                    "the stored value is not the array's element sort",
                ));
            }
            return Ok(Val::Array(m, mem.store(self.cx, at, i, v)?));
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
                    Val::Rm(_) => 3,
                    Val::Array(..) => 4,
                };
                if matches!(args[0].1, Val::Array(..)) {
                    return Err(Error::Unsupported("equality of arrays".into()));
                }
                if args.iter().any(|&(_, v)| kind(v) != kind(args[0].1)) {
                    return Err(sx.err(id, "operands of different sorts"));
                }
                if let Val::Fp(_, f) = args[0].1 {
                    return self.float_equality(sx, id, op, f, args);
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
                    (Val::Rm(_), Val::Rm(_)) => Err(Error::Unsupported(
                        "a rounding mode chosen by a condition".into(),
                    )),
                    (Val::Array(..), Val::Array(..)) => {
                        Err(Error::Unsupported("an array chosen by a condition".into()))
                    }
                    _ => Err(sx.err(id, "ite arms of different sorts")),
                }
            }
            _ => Err(Error::Unsupported(format!("the operator {op}"))),
        }
    }
}

// ----- floating point ------------------------------------------------------------------------

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
                Ok(Val::Bv(self.cx.fp(op, f, &[e])?))
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
            ("fp.min", 2) => float(self.cx, FpOp::Min, &xs),
            ("fp.max", 2) => float(self.cx, FpOp::Max, &xs),
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
    /// constant no term has read yet: read as the definition of `c` (the bits of `T`, a NaN as
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
        let Some(&(Val::Bv(symbol), read)) = self.globals.get(name) else {
            return Ok(false);
        };
        if read || self.scope.iter().any(|(n, _)| *n == name) {
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
        self.globals.insert(name, (Val::Bv(bits), false));
        self.out.symbols.retain(|(n, _)| n != name);
        Ok(true)
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
fn key_of(name: &str) -> SymbolKey {
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

//! SMT-LIB 2.6 import of a QF_BV subset.

use std::collections::HashMap;

use crate::error::Error;
use crate::expr::{Context, Expr};
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
        if self.sym(id) == Some("Bool") {
            return Ok(Sort::Bool);
        }
        if let Some(k) = self.list(id)
            && k.len() == 3
            && self.sym(k[0]) == Some("_")
            && self.sym(k[1]) == Some("BitVec")
        {
            let n = self.numeral(k[2])?;
            return Ok(Sort::Bv(self.width(k[2], n)?));
        }
        Err(self.err(id, "unsupported sort (Bool or (_ BitVec n))"))
    }
}

// ----- terms ---------------------------------------------------------------------------------

/// A term's value: a bit-vector, or a Boolean as a 1-bit expression.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Val {
    Bv(Expr),
    Bool(Expr),
}

impl Val {
    fn expr(self) -> Expr {
        match self {
            Val::Bv(e) | Val::Bool(e) => e,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum Sort {
    Bool,
    Bv(Width),
}

struct State<'a, 's> {
    cx: &'a mut Context,
    /// Declared and defined names.
    globals: HashMap<&'s str, Val>,
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
                self.out.definitions.push((name.to_string(), v.expr()));
                Ok(())
            }
            Some("assert") if args.len() == 1 => {
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
        self.globals.insert(name, v);
        Ok(())
    }

    fn declare(&mut self, sx: &Sx<'s>, name_id: u32, sort_id: u32) -> Result<(), Error> {
        let name = sx.name(name_id)?;
        let sort = sx.sort(sort_id)?;
        let key = key_of(name);
        let (w, wrap): (Width, fn(Expr) -> Val) = match sort {
            Sort::Bool => (Width::W1, Val::Bool),
            Sort::Bv(w) => (w, Val::Bv),
        };
        let e = self.cx.symbol(key, w)?;
        self.bind_global(sx, name_id, name, wrap(e))?;
        self.out.symbols.push((name.to_string(), e));
        Ok(())
    }

    fn check_sort(&self, sx: &Sx<'s>, id: u32, v: Val, sort: Sort) -> Result<(), Error> {
        let ok = match (v, sort) {
            (Val::Bool(_), Sort::Bool) => true,
            (Val::Bv(e), Sort::Bv(w)) => self.cx.width(e)? == w,
            _ => false,
        };
        if ok {
            Ok(())
        } else {
            Err(sx.err(id, "the term does not have the declared sort"))
        }
    }

    fn lookup(&self, name: &str) -> Option<Val> {
        self.scope
            .iter()
            .rev()
            .find(|(n, _)| *n == name)
            .map(|&(_, v)| v)
            .or_else(|| self.globals.get(name).copied())
    }

    fn bv(&self, sx: &Sx<'s>, id: u32, v: Val) -> Result<Expr, Error> {
        match v {
            Val::Bv(e) => Ok(e),
            Val::Bool(_) => Err(sx.err(id, "expected a bit-vector")),
        }
    }

    fn boolean(&self, sx: &Sx<'s>, id: u32, v: Val) -> Result<Expr, Error> {
        match v {
            Val::Bool(e) => Ok(e),
            Val::Bv(_) => Err(sx.err(id, "expected a Boolean")),
        }
    }

    fn term(&mut self, sx: &Sx<'s>, id: u32) -> Result<Val, Error> {
        match sx.tok(id) {
            Tok::Lit(s) => self.literal(sx, id, s),
            Tok::Sym(s) => match s {
                "true" => Ok(Val::Bool(self.cx.bool(true)?)),
                "false" => Ok(Val::Bool(self.cx.bool(false)?)),
                _ => self
                    .lookup(s)
                    .ok_or_else(|| sx.err(id, "undeclared symbol")),
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

    /// `(_ bvN n)`.
    fn indexed_constant(&mut self, sx: &Sx<'s>, id: u32, args: &[u32]) -> Result<Val, Error> {
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
        let nums: Vec<u32> = idx[1..]
            .iter()
            .map(|&i| sx.numeral(i))
            .collect::<Result<_, _>>()?;
        let [a] = args else {
            return Err(sx.err(id, "an indexed operator takes one operand"));
        };
        let v = self.term(sx, *a)?;
        let x = self.bv(sx, *a, v)?;
        let w = u32::from(self.cx.width(x)?.bits());
        let e = match (op, nums.as_slice()) {
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
                let kind = |v: Val| matches!(v, Val::Bool(_));
                if args.iter().any(|&(_, v)| kind(v) != kind(args[0].1)) {
                    return Err(sx.err(id, "operands of different sorts"));
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
                    let (a, b) = (args[i].1.expr(), args[j].1.expr());
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
                    _ => Err(sx.err(id, "ite arms of different sorts")),
                }
            }
            _ => Err(Error::Unsupported(format!("the operator {op}"))),
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

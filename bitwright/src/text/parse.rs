//! Parser for the expression syntax, with width inference.
//!
//! Parsing builds a flat, width-annotated tree first (children before parents; `let` bindings
//! make it a DAG), infers every width by unification, and only then builds nodes through the
//! canonicalizing constructors. Nesting is limited, so untrusted input cannot exhaust the stack.

use std::collections::HashMap;

use super::SyntaxError;
use super::lex::{Tok, Token, lex};
use crate::error::Error;
use crate::expr::{Context, Expr};
use crate::ops::{BinOp, CmpOpExt, UnOp};
use crate::{BitVec, SymbolKey, Width};

/// Options for [`Context::parse`].
#[derive(Clone, Debug, Default)]
#[non_exhaustive]
pub struct ParseOptions {
    /// Width for symbols and literals whose width cannot be inferred. `None` makes such an
    /// expression an error.
    pub default_width: Option<Width>,
    /// Only resolve symbols that already exist in the context (never create new ones).
    pub existing_symbols_only: bool,
}

impl ParseOptions {
    /// Options with a default width.
    pub fn width(w: Width) -> Self {
        ParseOptions {
            default_width: Some(w),
            existing_symbols_only: false,
        }
    }

    /// Sets [`existing_symbols_only`](Self::existing_symbols_only).
    pub fn with_existing_symbols_only(mut self, yes: bool) -> Self {
        self.existing_symbols_only = yes;
        self
    }
}

const MAX_DEPTH: u32 = 128;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Derived {
    UMin,
    UMax,
    SMin,
    SMax,
    AndN,
    OrN,
    XNor,
    Abs,
    AddCarry,
    SubBorrow,
    SAddOverflow,
    SSubOverflow,
    AddSatU,
    AddSatS,
    SubSatU,
    SubSatS,
}

#[derive(Clone, Debug)]
enum Kind {
    Lit(Vec<u64>),
    /// `-<literal>`: range-checked as a signed value.
    NegLit(Vec<u64>),
    Bool(bool),
    Sym(SymbolKey),
    Un(UnOp, usize),
    Bin(BinOp, usize, usize),
    Cmp(CmpOpExt, usize, usize),
    Zext(usize),
    Sext(usize),
    Extract(u16, usize),
    Concat(usize, usize),
    Select(usize, usize, usize),
    Derived(Derived, usize, usize),
    /// Output `k` of an extension operation on 1 to 3 arguments.
    Ext(crate::ext::ExtId, u8, Vec<usize>),
}

struct PNode {
    kind: Kind,
    var: usize,
    span: (usize, usize),
}

/// Union-find over width variables, each optionally fixed to a width.
struct Widths {
    parent: Vec<usize>,
    value: Vec<Option<u16>>,
}

impl Widths {
    fn fresh(&mut self) -> usize {
        self.parent.push(self.parent.len());
        self.value.push(None);
        self.parent.len() - 1
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }

    fn get(&mut self, x: usize) -> Option<u16> {
        let r = self.find(x);
        self.value[r]
    }

    /// Returns false on a conflict.
    fn unify(&mut self, a: usize, b: usize) -> bool {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return true;
        }
        let v = match (self.value[ra], self.value[rb]) {
            (Some(x), Some(y)) if x != y => return false,
            (x, y) => x.or(y),
        };
        self.parent[rb] = ra;
        self.value[ra] = v;
        true
    }

    fn fix(&mut self, a: usize, w: u16) -> bool {
        let r = self.find(a);
        match self.value[r] {
            Some(x) => x == w,
            None => {
                self.value[r] = Some(w);
                true
            }
        }
    }
}

struct Parser<'a> {
    toks: Vec<Token>,
    pos: usize,
    nodes: Vec<PNode>,
    widths: Widths,
    lets: HashMap<LetKey, usize>,
    sym_vars: HashMap<SymbolKey, usize>,
    cx: &'a Context,
    opts: &'a ParseOptions,
    depth: u32,
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum LetKey {
    Num(u32),
    Name(String),
}

type PResult<T> = Result<T, SyntaxError>;

impl<'a> Parser<'a> {
    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }

    fn span(&self) -> (usize, usize) {
        let t = &self.toks[self.pos];
        (t.start, t.end)
    }

    fn bump(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }

    fn error<T>(&self, msg: &str) -> PResult<T> {
        let (s, e) = self.span();
        Err(SyntaxError::new(msg, s, e))
    }

    fn expect(&mut self, t: Tok, what: &str) -> PResult<Token> {
        if *self.peek() == t {
            Ok(self.bump())
        } else {
            self.error(&format!("expected {what}"))
        }
    }

    fn node(&mut self, kind: Kind, span: (usize, usize)) -> usize {
        let var = self.widths.fresh();
        self.nodes.push(PNode { kind, var, span });
        self.nodes.len() - 1
    }

    fn var(&self, n: usize) -> usize {
        self.nodes[n].var
    }

    fn unify(&mut self, a: usize, b: usize, span: (usize, usize)) -> PResult<()> {
        let (va, vb) = (self.var(a), self.var(b));
        if self.widths.unify(va, vb) {
            Ok(())
        } else {
            let (wa, wb) = (self.widths.get(va), self.widths.get(vb));
            Err(SyntaxError::new(
                &format!(
                    "operand widths differ ({} vs {}); insert an explicit zext/sext/trunc",
                    wa.unwrap_or(0),
                    wb.unwrap_or(0)
                ),
                span.0,
                span.1,
            ))
        }
    }

    fn fix(&mut self, n: usize, w: u16, span: (usize, usize)) -> PResult<()> {
        let v = self.var(n);
        if self.widths.fix(v, w) {
            Ok(())
        } else {
            let have = self.widths.get(v).unwrap_or(0);
            Err(SyntaxError::new(
                &format!("width {w} conflicts with inferred width {have}"),
                span.0,
                span.1,
            ))
        }
    }

    fn enter(&mut self) -> PResult<()> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return self.error("expression nested too deeply; use `let` bindings");
        }
        Ok(())
    }

    // ----- grammar --------------------------------------------------------------------------

    fn top(&mut self) -> PResult<usize> {
        while matches!(self.peek(), Tok::Ident(s) if s == "let") {
            self.bump();
            let key = match self.bump().tok {
                Tok::LetName(k) => LetKey::Num(k),
                Tok::Ident(s) if !super::is_reserved(&s) => LetKey::Name(s),
                _ => return self.error("expected a name after `let`"),
            };
            self.expect(Tok::Assign, "`=`")?;
            let e = self.expr()?;
            self.expect(Tok::Semi, "`;`")?;
            if self.lets.insert(key, e).is_some() {
                return self.error("this name is already bound by an earlier `let`");
            }
        }
        let e = self.expr()?;
        if *self.peek() != Tok::Eof {
            return self.error("unexpected input after expression");
        }
        Ok(e)
    }

    fn expr(&mut self) -> PResult<usize> {
        self.enter()?;
        let start = self.span().0;
        let lhs = self.binary(0)?;
        let op = match self.peek() {
            Tok::Eq => CmpOpExt::Eq,
            Tok::Ne => CmpOpExt::Ne,
            Tok::Ult => CmpOpExt::Ult,
            Tok::Ule => CmpOpExt::Ule,
            Tok::Ugt => CmpOpExt::Ugt,
            Tok::Uge => CmpOpExt::Uge,
            Tok::Slt => CmpOpExt::Slt,
            Tok::Sle => CmpOpExt::Sle,
            Tok::Sgt => CmpOpExt::Sgt,
            Tok::Sge => CmpOpExt::Sge,
            _ => {
                self.depth -= 1;
                return Ok(lhs);
            }
        };
        self.bump();
        let rhs = self.binary(0)?;
        let span = (start, self.toks[self.pos.saturating_sub(1)].end);
        self.unify(lhs, rhs, span)?;
        let n = self.node(Kind::Cmp(op, lhs, rhs), span);
        self.fix(n, 1, span)?;
        if matches!(
            self.peek(),
            Tok::Eq
                | Tok::Ne
                | Tok::Ult
                | Tok::Ule
                | Tok::Ugt
                | Tok::Uge
                | Tok::Slt
                | Tok::Sle
                | Tok::Sgt
                | Tok::Sge
        ) {
            return self.error("comparisons do not chain; add parentheses");
        }
        self.depth -= 1;
        Ok(n)
    }

    /// The binary operator at the cursor and its precedence (higher binds tighter).
    fn binary_op(&self) -> Option<(BinOp, u8)> {
        Some(match self.peek() {
            Tok::Pipe => (BinOp::Or, 2),
            Tok::Caret => (BinOp::Xor, 3),
            Tok::Amp => (BinOp::And, 4),
            Tok::Shl => (BinOp::Shl, 5),
            Tok::LShr => (BinOp::LShr, 5),
            Tok::AShr => (BinOp::AShr, 5),
            Tok::Plus => (BinOp::Add, 6),
            Tok::Minus => (BinOp::Sub, 6),
            Tok::Star => (BinOp::Mul, 7),
            _ => return None,
        })
    }

    /// Precedence climbing over the left-associative binary operators.
    fn binary(&mut self, min_prec: u8) -> PResult<usize> {
        let start = self.span().0;
        let mut lhs = self.unary()?;
        while let Some((op, prec)) = self.binary_op() {
            if prec < min_prec {
                break;
            }
            self.bump();
            let rhs = self.binary(prec + 1)?;
            let span = (start, self.toks[self.pos.saturating_sub(1)].end);
            self.unify(lhs, rhs, span)?;
            let n = self.node(Kind::Bin(op, lhs, rhs), span);
            self.unify(n, lhs, span)?;
            lhs = n;
        }
        Ok(lhs)
    }

    fn unary(&mut self) -> PResult<usize> {
        let op = match self.peek() {
            Tok::Tilde => UnOp::Not,
            Tok::Minus => UnOp::Neg,
            _ => return self.postfix(),
        };
        self.enter()?;
        let start = self.bump().start;
        let a = self.unary()?;
        let span = (start, self.toks[self.pos.saturating_sub(1)].end);
        if op == UnOp::Neg
            && a + 1 == self.nodes.len()
            && let Kind::Lit(limbs) = &self.nodes[a].kind
        {
            self.nodes[a].kind = Kind::NegLit(limbs.clone());
            self.nodes[a].span = span;
            self.depth -= 1;
            return Ok(a);
        }
        let n = self.node(Kind::Un(op, a), span);
        self.unify(n, a, span)?;
        self.depth -= 1;
        Ok(n)
    }

    fn postfix(&mut self) -> PResult<usize> {
        let e = self.primary()?;
        if *self.peek() == Tok::Colon {
            self.bump();
            let span = self.span();
            let w = self.width_literal()?;
            self.fix(e, w, span)?;
        }
        Ok(e)
    }

    fn width_literal(&mut self) -> PResult<u16> {
        let span = self.span();
        match self.bump().tok {
            Tok::Int(d, 10) => d
                .parse::<u16>()
                .ok()
                .filter(|w| Width::new(*w).is_ok())
                .ok_or_else(|| SyntaxError::new("width must be in 1..=512", span.0, span.1)),
            _ => Err(SyntaxError::new("expected a decimal width", span.0, span.1)),
        }
    }

    fn primary(&mut self) -> PResult<usize> {
        let span = self.span();
        let t = self.bump();
        match t.tok {
            Tok::Int(digits, radix) => {
                let limbs = parse_limbs(&digits, radix)
                    .ok_or_else(|| SyntaxError::new("literal exceeds 512 bits", span.0, span.1))?;
                Ok(self.node(Kind::Lit(limbs), span))
            }
            Tok::LParen => {
                let e = self.expr()?;
                self.expect(Tok::RParen, "`)`")?;
                Ok(e)
            }
            Tok::LetName(k) => self
                .lets
                .get(&LetKey::Num(k))
                .copied()
                .ok_or_else(|| SyntaxError::new(&format!("unbound name %{k}"), span.0, span.1)),
            Tok::HashKey(k) => self.symbol(SymbolKey::U64(k), span),
            Tok::FreshKey(k) => self.symbol(SymbolKey::Fresh(k), span),
            Tok::Str(s) => self.symbol(SymbolKey::from(s), span),
            Tok::Ext(name, k) => {
                let op = self
                    .cx
                    .registry()
                    .and_then(|r| r.id(&name))
                    .ok_or_else(|| {
                        SyntaxError::new(
                            &format!("no extension operation `{name}` in this context"),
                            span.0,
                            span.1,
                        )
                    })?;
                self.enter()?;
                self.expect(Tok::LParen, "`(`")?;
                let mut args = vec![self.expr()?];
                while *self.peek() == Tok::Comma {
                    self.bump();
                    args.push(self.expr()?);
                }
                self.expect(Tok::RParen, "`)`")?;
                self.depth -= 1;
                let end = self.toks[self.pos.saturating_sub(1)].end;
                if args.len() > crate::ext::MAX_ARGS {
                    return Err(SyntaxError::new(
                        &format!("`{name}` takes at most {} arguments", crate::ext::MAX_ARGS),
                        span.0,
                        end,
                    ));
                }
                Ok(self.node(Kind::Ext(op, k, args), (span.0, end)))
            }
            Tok::Ident(name) => {
                if name == "true" || name == "false" {
                    let n = self.node(Kind::Bool(name == "true"), span);
                    self.fix(n, 1, span)?;
                    return Ok(n);
                }
                if let Some(&e) = self.lets.get(&LetKey::Name(name.clone())) {
                    return Ok(e);
                }
                if super::FUNCTIONS.contains(&name.as_str()) {
                    return self.call(&name, span);
                }
                if super::is_reserved(&name) {
                    return Err(SyntaxError::new(
                        &format!("`{name}` is reserved"),
                        span.0,
                        span.1,
                    ));
                }
                self.symbol(SymbolKey::from(name), span)
            }
            _ => Err(SyntaxError::new("expected an expression", span.0, span.1)),
        }
    }

    fn symbol(&mut self, key: SymbolKey, span: (usize, usize)) -> PResult<usize> {
        let existing = self
            .cx
            .find_symbol(&key)
            .and_then(|e| self.cx.width(e).ok());
        if existing.is_none() && self.opts.existing_symbols_only {
            return Err(SyntaxError::new(
                &format!("unknown symbol {key}"),
                span.0,
                span.1,
            ));
        }
        let n = self.node(Kind::Sym(key.clone()), span);
        if let Some(&v) = self.sym_vars.get(&key) {
            let nv = self.var(n);
            if !self.widths.unify(nv, v) {
                return Err(SyntaxError::new("symbol width conflict", span.0, span.1));
            }
        } else {
            self.sym_vars.insert(key, self.var(n));
        }
        if let Some(w) = existing {
            self.fix(n, w.bits(), span)?;
        }
        Ok(n)
    }

    fn generics(&mut self, count: usize) -> PResult<Vec<u16>> {
        self.expect(Tok::LAngle, "`<`")?;
        let mut out = Vec::new();
        for k in 0..count {
            if k > 0 {
                self.expect(Tok::Comma, "`,`")?;
            }
            let span = self.span();
            match self.bump().tok {
                Tok::Int(d, 10) => out.push(
                    d.parse::<u16>()
                        .map_err(|_| SyntaxError::new("number too large", span.0, span.1))?,
                ),
                _ => return Err(SyntaxError::new("expected a number", span.0, span.1)),
            }
        }
        self.expect(Tok::RAngle, "`>`")?;
        Ok(out)
    }

    fn args(&mut self, count: usize) -> PResult<Vec<usize>> {
        self.expect(Tok::LParen, "`(`")?;
        let mut out = Vec::new();
        for k in 0..count {
            if k > 0 {
                self.expect(Tok::Comma, "`,`")?;
            }
            out.push(self.expr()?);
        }
        self.expect(Tok::RParen, "`)`")?;
        Ok(out)
    }

    fn call(&mut self, name: &str, start: (usize, usize)) -> PResult<usize> {
        self.enter()?;
        let un = |n: &str| {
            Some(match n {
                "popcnt" => UnOp::Popcnt,
                "clz" => UnOp::Clz,
                "ctz" => UnOp::Ctz,
                "bswap" => UnOp::Bswap,
                "bitrev" => UnOp::BitRev,
                _ => return None,
            })
        };
        let bin = |n: &str| {
            Some(match n {
                "udiv" => BinOp::UDiv,
                "urem" => BinOp::URem,
                "sdiv" => BinOp::SDiv,
                "srem" => BinOp::SRem,
                "rotl" => BinOp::RotL,
                "rotr" => BinOp::RotR,
                "umulhi" => BinOp::UMulHi,
                "smulhi" => BinOp::SMulHi,
                "pdep" => BinOp::Pdep,
                "pext" => BinOp::Pext,
                _ => return None,
            })
        };
        let derived = |n: &str| {
            Some(match n {
                "umin" => Derived::UMin,
                "umax" => Derived::UMax,
                "smin" => Derived::SMin,
                "smax" => Derived::SMax,
                "andn" => Derived::AndN,
                "orn" => Derived::OrN,
                "xnor" => Derived::XNor,
                "abs" => Derived::Abs,
                "add_carry" => Derived::AddCarry,
                "sub_borrow" => Derived::SubBorrow,
                "sadd_overflow" => Derived::SAddOverflow,
                "ssub_overflow" => Derived::SSubOverflow,
                "add_sat_u" => Derived::AddSatU,
                "add_sat_s" => Derived::AddSatS,
                "sub_sat_u" => Derived::SubSatU,
                "sub_sat_s" => Derived::SubSatS,
                _ => return None,
            })
        };
        let span = |p: &Self| (start.0, p.toks[p.pos.saturating_sub(1)].end);
        let n = if let Some(op) = un(name) {
            let a = self.args(1)?[0];
            let sp = span(self);
            let n = self.node(Kind::Un(op, a), sp);
            self.unify(n, a, sp)?;
            n
        } else if let Some(op) = bin(name) {
            let a = self.args(2)?;
            let sp = span(self);
            self.unify(a[0], a[1], sp)?;
            let n = self.node(Kind::Bin(op, a[0], a[1]), sp);
            self.unify(n, a[0], sp)?;
            n
        } else if let Some(d) = derived(name) {
            let unary = d == Derived::Abs;
            let a = self.args(if unary { 1 } else { 2 })?;
            let (x, y) = (a[0], if unary { a[0] } else { a[1] });
            let sp = span(self);
            self.unify(x, y, sp)?;
            let n = self.node(Kind::Derived(d, x, y), sp);
            if matches!(
                d,
                Derived::AddCarry
                    | Derived::SubBorrow
                    | Derived::SAddOverflow
                    | Derived::SSubOverflow
            ) {
                self.fix(n, 1, sp)?;
            } else {
                self.unify(n, x, sp)?;
            }
            n
        } else {
            match name {
                "zext" | "sext" | "trunc" => {
                    let g = self.generics(1)?;
                    let a = self.args(1)?[0];
                    let sp = span(self);
                    let to = g[0];
                    if Width::new(to).is_err() {
                        return Err(SyntaxError::new("width must be in 1..=512", sp.0, sp.1));
                    }
                    let kind = match name {
                        "zext" => Kind::Zext(a),
                        "sext" => Kind::Sext(a),
                        _ => Kind::Extract(0, a),
                    };
                    let n = self.node(kind, sp);
                    self.fix(n, to, sp)?;
                    n
                }
                "extract" => {
                    let g = self.generics(2)?;
                    let a = self.args(1)?[0];
                    let sp = span(self);
                    if Width::new(g[1]).is_err() {
                        return Err(SyntaxError::new("width must be in 1..=512", sp.0, sp.1));
                    }
                    let n = self.node(Kind::Extract(g[0], a), sp);
                    self.fix(n, g[1], sp)?;
                    n
                }
                "concat" => {
                    let a = self.args(2)?;
                    let sp = span(self);
                    self.node(Kind::Concat(a[0], a[1]), sp)
                }
                "select" => {
                    let a = self.args(3)?;
                    let sp = span(self);
                    self.fix(a[0], 1, sp)?;
                    self.unify(a[1], a[2], sp)?;
                    let n = self.node(Kind::Select(a[0], a[1], a[2]), sp);
                    self.unify(n, a[1], sp)?;
                    n
                }
                _ => return self.error("unknown function"),
            }
        };
        self.depth -= 1;
        Ok(n)
    }
}

/// Parses digits into little-endian limbs (at most 512 bits).
fn parse_limbs(digits: &str, radix: u32) -> Option<Vec<u64>> {
    let mut acc = vec![0u64; 9];
    for ch in digits.chars() {
        let d = ch.to_digit(radix)?;
        let mut carry = u128::from(d);
        for x in acc.iter_mut() {
            let t = u128::from(*x) * u128::from(radix) + carry;
            *x = t as u64;
            carry = t >> 64;
        }
        if carry != 0 || acc[8] != 0 {
            return None;
        }
    }
    acc.truncate(8);
    Some(acc)
}

/// One pass of concatenation-width propagation in the given node order; returns whether
/// anything changed.
fn concat_pass(p: &mut Parser<'_>, order: &[usize]) -> PResult<bool> {
    let mut changed = false;
    for &i in order {
        if matches!(p.nodes[i].kind, Kind::Ext(..)) {
            changed |= ext_pass(p, i)?;
            continue;
        }
        let Kind::Concat(h, l) = p.nodes[i].kind else {
            continue;
        };
        let (vn, vh, vl) = (p.nodes[i].var, p.nodes[h].var, p.nodes[l].var);
        let (wn, wh, wl) = (p.widths.get(vn), p.widths.get(vh), p.widths.get(vl));
        let span = p.nodes[i].span;
        let bad = || SyntaxError::new("concatenation widths do not fit", span.0, span.1);
        match (wn, wh, wl) {
            (None, Some(a), Some(b)) => {
                let t = u32::from(a) + u32::from(b);
                if t > u32::from(Width::MAX_BITS) {
                    return Err(bad());
                }
                p.widths.fix(vn, t as u16);
                changed = true;
            }
            (Some(t), Some(a), None) => {
                if t <= a {
                    return Err(bad());
                }
                p.widths.fix(vl, t - a);
                changed = true;
            }
            (Some(t), None, Some(b)) => {
                if t <= b {
                    return Err(bad());
                }
                p.widths.fix(vh, t - b);
                changed = true;
            }
            (Some(t), Some(a), Some(b)) if u32::from(t) != u32::from(a) + u32::from(b) => {
                return Err(bad());
            }
            _ => {}
        }
    }
    Ok(changed)
}

/// Propagates concatenation widths bottom-up and top-down until nothing changes.
fn concat_fixpoint(p: &mut Parser<'_>) -> PResult<()> {
    let concats: Vec<usize> = (0..p.nodes.len())
        .filter(|&i| matches!(p.nodes[i].kind, Kind::Concat(..) | Kind::Ext(..)))
        .collect();
    if concats.is_empty() {
        return Ok(());
    }
    let rev: Vec<usize> = concats.iter().rev().copied().collect();
    loop {
        let up = concat_pass(p, &concats)?;
        let down = concat_pass(p, &rev)?;
        if !up && !down {
            return Ok(());
        }
    }
}

/// The operand nodes of a parsed node.
fn operands(k: &Kind) -> Vec<usize> {
    match k {
        Kind::Lit(_) | Kind::NegLit(_) | Kind::Bool(_) | Kind::Sym(_) => Vec::new(),
        Kind::Un(_, a) | Kind::Zext(a) | Kind::Sext(a) | Kind::Extract(_, a) => vec![*a],
        Kind::Bin(_, a, b) | Kind::Cmp(_, a, b) | Kind::Concat(a, b) | Kind::Derived(_, a, b) => {
            vec![*a, *b]
        }
        Kind::Select(a, b, c) => vec![*a, *b, *c],
        Kind::Ext(_, _, args) => args.clone(),
    }
}

/// An extension call's output width from its arguments' widths (once they are all known).
fn ext_pass(p: &mut Parser<'_>, i: usize) -> PResult<bool> {
    let Kind::Ext(op, k, args) = &p.nodes[i].kind else {
        return Ok(false);
    };
    let span = p.nodes[i].span;
    let err = |m: String| SyntaxError::new(&m, span.0, span.1);
    let mut widths = Vec::with_capacity(args.len());
    for &a in args {
        match p.widths.get(p.nodes[a].var) {
            Some(w) => widths.push(Width::new(w).map_err(|e| err(e.to_string()))?),
            None => return Ok(false),
        }
    }
    let o =
        p.cx.registry()
            .and_then(|r| r.op(*op))
            .ok_or_else(|| err("no such extension operation".into()))?;
    let sig = o
        .signature(&widths)
        .map_err(|why| err(format!("`{}`: {why}", o.name())))?;
    if sig.is_empty() || sig.len() > crate::ext::MAX_OUTPUTS {
        return Err(err(format!(
            "`{}` declares {} outputs (1 to {})",
            o.name(),
            sig.len(),
            crate::ext::MAX_OUTPUTS
        )));
    }
    let w = sig
        .width(usize::from(*k))
        .ok_or_else(|| err(format!("`{}` has no output {k}", o.name())))?;
    let v = p.nodes[i].var;
    match p.widths.get(v) {
        None => {
            p.widths.fix(v, w.bits());
            Ok(true)
        }
        Some(have) if have != w.bits() => Err(err(format!(
            "`{}` output {k} has {} bits, not {have}",
            o.name(),
            w.bits()
        ))),
        Some(_) => Ok(false),
    }
}

/// Resolves every width: concatenations, then the default for every still-unknown leaf at
/// once, then concatenations again. Linear in the input apart from the (rare) alternation
/// between nested concatenations.
fn resolve(p: &mut Parser<'_>) -> PResult<Vec<u16>> {
    concat_fixpoint(p)?;
    // Leaves take the default width in stages: first those below an extension call's arguments
    // (a call's output width follows from them), then the other symbols, then literals, with the
    // widths propagated after each stage. So a leaf next to a call's output takes that output's
    // width, not the default.
    let mut under_ext = vec![false; p.nodes.len()];
    for i in (0..p.nodes.len()).rev() {
        if let Kind::Ext(_, _, args) = &p.nodes[i].kind {
            let mut stack = args.clone();
            while let Some(j) = stack.pop() {
                if under_ext[j] {
                    continue;
                }
                under_ext[j] = true;
                stack.extend(operands(&p.nodes[j].kind));
            }
        }
    }
    for stage in 0..3 {
        let mut defaulted = false;
        for (i, &under) in under_ext.iter().enumerate() {
            let is_leaf = matches!(
                p.nodes[i].kind,
                Kind::Sym(_) | Kind::Lit(_) | Kind::NegLit(_)
            );
            let leaf = is_leaf
                && match stage {
                    0 => under,
                    1 => matches!(p.nodes[i].kind, Kind::Sym(_)),
                    _ => true,
                };
            let v = p.nodes[i].var;
            if leaf && p.widths.get(v).is_none() {
                match p.opts.default_width {
                    Some(w) => {
                        p.widths.fix(v, w.bits());
                        defaulted = true;
                    }
                    None => {
                        let span = p.nodes[i].span;
                        return Err(SyntaxError::new(
                            "cannot infer this width; write `:W` (for example `1:32`)",
                            span.0,
                            span.1,
                        ));
                    }
                }
            }
        }
        if defaulted {
            concat_fixpoint(p)?;
        }
    }
    let mut out = Vec::with_capacity(p.nodes.len());
    for i in 0..p.nodes.len() {
        let v = p.nodes[i].var;
        match p.widths.get(v) {
            Some(w) => out.push(w),
            None => {
                let span = p.nodes[i].span;
                return Err(SyntaxError::new("cannot infer this width", span.0, span.1));
            }
        }
    }
    validate(&p.nodes, &out)?;
    Ok(out)
}

/// Checks everything the builder would reject, before any node or symbol is created, so a
/// failed parse leaves the context unchanged.
fn validate(nodes: &[PNode], widths: &[u16]) -> PResult<()> {
    for (i, n) in nodes.iter().enumerate() {
        let w = widths[i];
        let err = |m: &str| Err(SyntaxError::new(m, n.span.0, n.span.1));
        match &n.kind {
            Kind::Lit(limbs) => {
                let width =
                    Width::new(w).map_err(|_| SyntaxError::new("bad width", n.span.0, n.span.1))?;
                if BitVec::from_limbs(width, limbs).is_err() {
                    return err(&format!("literal does not fit in {w} bits"));
                }
            }
            Kind::NegLit(limbs) => {
                let width =
                    Width::new(w).map_err(|_| SyntaxError::new("bad width", n.span.0, n.span.1))?;
                let fits = BitVec::from_limbs(width, limbs)
                    .is_ok_and(|m| m.is_zero() || m == BitVec::smin(width) || !m.msb());
                if !fits {
                    return err(&format!(
                        "negative literal does not fit in {w} bits (signed)"
                    ));
                }
            }
            Kind::Un(UnOp::Bswap, _) if !w.is_multiple_of(8) => {
                return err("bswap needs a width that is a multiple of 8");
            }
            Kind::Zext(a) | Kind::Sext(a) if widths[*a] > w => {
                return err(&format!("cannot extend {} bits to {w} bits", widths[*a]));
            }
            Kind::Extract(lo, a) if u32::from(*lo) + u32::from(w) > u32::from(widths[*a]) => {
                return err(&format!(
                    "extract of bits [{lo}, {lo}+{w}) does not fit in {} bits",
                    widths[*a]
                ));
            }
            _ => {}
        }
    }
    Ok(())
}

impl Context {
    /// Parses an expression in the text syntax (see `docs/design.md` §7.1), creating symbols
    /// as needed, and builds it through the canonicalizing constructors.
    ///
    /// ```
    /// use bitwright::{Context, ParseOptions, Width};
    /// let mut cx = Context::new();
    /// let e = cx.parse("(y | x) + (y & x)", &ParseOptions::width(Width::W64))?;
    /// // Built canonically: operands of commutative operators in one order.
    /// assert_eq!(cx.display(e).to_string(), "(x & y) + (x | y)");
    /// # Ok::<(), bitwright::Error>(())
    /// ```
    pub fn parse(&mut self, src: &str, opts: &ParseOptions) -> Result<Expr, Error> {
        let toks = lex(src).map_err(Error::Syntax)?;
        let (nodes, widths, root) = {
            let mut p = Parser {
                toks,
                pos: 0,
                nodes: Vec::new(),
                widths: Widths {
                    parent: Vec::new(),
                    value: Vec::new(),
                },
                lets: HashMap::new(),
                sym_vars: HashMap::new(),
                cx: self,
                opts,
                depth: 0,
            };
            let root = p.top().map_err(Error::Syntax)?;
            let widths = resolve(&mut p).map_err(Error::Syntax)?;
            (p.nodes, widths, root)
        };
        let mut built: Vec<Expr> = Vec::with_capacity(nodes.len());
        for (i, n) in nodes.iter().enumerate() {
            let w = Width::new(widths[i]).map_err(Error::Width)?;
            let at = |j: usize| built[j];
            let spanned = |e: Error| match e {
                Error::Width(we) => {
                    Error::Syntax(SyntaxError::new(&we.to_string(), n.span.0, n.span.1))
                }
                Error::Value(_) => Error::Syntax(SyntaxError::new(
                    &format!("literal does not fit in {} bits", w.bits()),
                    n.span.0,
                    n.span.1,
                )),
                other => other,
            };
            let e = match &n.kind {
                Kind::Lit(limbs) => BitVec::from_limbs(w, limbs)
                    .map_err(Error::Value)
                    .and_then(|v| self.constant(&v)),
                Kind::NegLit(limbs) => BitVec::from_limbs(w, limbs)
                    .map_err(Error::Value)
                    .and_then(|v| self.constant(&BitVec::un_unchecked(UnOp::Neg, &v))),
                Kind::Bool(b) => self.bool(*b),
                Kind::Sym(key) => self.symbol(key.clone(), w),
                Kind::Un(op, a) => self.un(*op, at(*a)),
                Kind::Bin(op, a, b) => self.bin(*op, at(*a), at(*b)),
                Kind::Cmp(op, a, b) => self.cmp(*op, at(*a), at(*b)),
                Kind::Zext(a) => self.zext(at(*a), w),
                Kind::Sext(a) => self.sext(at(*a), w),
                Kind::Extract(lo, a) => self.extract(at(*a), *lo, w),
                Kind::Concat(h, l) => self.concat(at(*h), at(*l)),
                Kind::Select(c, t, f) => self.select(at(*c), at(*t), at(*f)),
                Kind::Ext(op, k, args) => {
                    let args: Vec<Expr> = args.iter().map(|&a| at(a)).collect();
                    self.ext_output(*op, usize::from(*k), &args)
                }
                Kind::Derived(d, a, b) => {
                    let (a, b) = (at(*a), at(*b));
                    match d {
                        Derived::UMin => self.umin(a, b),
                        Derived::UMax => self.umax(a, b),
                        Derived::SMin => self.smin(a, b),
                        Derived::SMax => self.smax(a, b),
                        Derived::AndN => self.andn(a, b),
                        Derived::OrN => self.orn(a, b),
                        Derived::XNor => self.xnor(a, b),
                        Derived::Abs => self.abs(a),
                        Derived::AddCarry => self.add_carry(a, b),
                        Derived::SubBorrow => self.sub_borrow(a, b),
                        Derived::SAddOverflow => self.sadd_overflow(a, b),
                        Derived::SSubOverflow => self.ssub_overflow(a, b),
                        Derived::AddSatU => self.add_sat_u(a, b),
                        Derived::AddSatS => self.add_sat_s(a, b),
                        Derived::SubSatU => self.sub_sat_u(a, b),
                        Derived::SubSatS => self.sub_sat_s(a, b),
                    }
                }
            }
            .map_err(spanned)?;
            built.push(e);
        }
        Ok(built[root])
    }
}

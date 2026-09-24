//! The rule compiler: parsing, width inference, static checks, rule identity.

use std::collections::HashMap;

use super::diag::{CompileError, Diagnostic, Level};
use super::ir::{
    ConstPred, FactPred, FloatLit, FpNode, Group, LetDef, Literal, NodeId, Param, ParamKind, RNode,
    Rounding, Rule, RuleId, RuleKind, Sort, WCmp, WCons, WExpr,
};
use super::order::kbo_greater;
use crate::fp::syntax::Base;
use crate::fp::{FpFormat, FpKind, FpTest, RoundingMode};
use crate::hash::combine;
use crate::ops::{BinOp, CmpOpExt, UnOp};
use crate::text::lex::{Tok, Token, lex_mode};

/// Limits for compiling untrusted rule text.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct CompileLimits {
    /// Maximum source length in bytes.
    pub max_source: usize,
    /// Maximum number of rules.
    pub max_rules: usize,
    /// Maximum nodes per rule.
    pub max_nodes: usize,
    /// Maximum total work (node visits) spent validating rules at their width assignments.
    pub max_work: u64,
    /// Maximum number of diagnostics before compilation stops.
    pub max_diagnostics: usize,
}

impl Default for CompileLimits {
    fn default() -> Self {
        CompileLimits {
            max_source: 4 << 20,
            max_rules: 10_000,
            max_nodes: 256,
            max_work: 1 << 28,
            max_diagnostics: 100,
        }
    }
}

setters!(CompileLimits {
    with_max_source: max_source: usize,
    with_max_rules: max_rules: usize,
    with_max_nodes: max_nodes: usize,
    with_max_work: max_work: u64,
    with_max_diagnostics: max_diagnostics: usize,
});

type R<T> = Result<T, Diagnostic>;

// ----- sort inference ------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
enum SV {
    Bv(WExpr),
    Bool,
}

struct Sorts {
    parent: Vec<usize>,
    value: Vec<Option<SV>>,
}

impl Sorts {
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
    fn get(&mut self, x: usize) -> Option<SV> {
        let r = self.find(x);
        self.value[r].clone()
    }
    fn unify(&mut self, a: usize, b: usize) -> bool {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return true;
        }
        let v = match (self.value[ra].take(), self.value[rb].take()) {
            (Some(x), Some(y)) if x != y => {
                self.value[ra] = Some(x);
                self.value[rb] = Some(y);
                return false;
            }
            (x, y) => x.or(y),
        };
        self.parent[rb] = ra;
        self.value[ra] = v;
        true
    }
    fn fix(&mut self, a: usize, s: SV) -> bool {
        let r = self.find(a);
        match &self.value[r] {
            Some(x) => *x == s,
            None => {
                self.value[r] = Some(s);
                true
            }
        }
    }
}

// ----- the parser ------------------------------------------------------------------------------

/// A `let` while parsing: name, value node (once parsed), width, span.
type PendingLet = (String, Option<NodeId>, WExpr, (usize, usize));

/// The lints `#[allow(..)]` may suppress: warnings and notes only.
const ALLOWABLE: &[&str] = &["BW0402", "BW0407"];

/// Attributes of an item: `#[example]` pairs, `#[allow]` codes, doc text.
type Attrs = (Vec<(String, String)>, Vec<String>, String);

/// A compiled program: groups, rules, and non-error diagnostics.
pub(crate) type Compiled = (Vec<Group>, Vec<Rule>, Vec<Diagnostic>);

struct RuleBuilder {
    width_vars: Vec<String>,
    /// Rounding-mode variables (`r: rm`).
    modes: Vec<String>,
    params: Vec<Param>,
    param_index: HashMap<String, u16>,
    lets: Vec<PendingLet>,
    nodes: Vec<RNode>,
    spans: Vec<(usize, usize)>,
    vars: Vec<usize>,
    sorts: Sorts,
    /// Forward references to `let` names: node index -> name.
    pending: Vec<(NodeId, String)>,
}

impl RuleBuilder {
    fn node(&mut self, n: RNode, span: (usize, usize)) -> R<NodeId> {
        if self.nodes.len() >= u16::MAX as usize {
            return Err(Diagnostic::error("BW0100", "rule too large", span));
        }
        self.nodes.push(n);
        self.spans.push(span);
        let v = self.sorts.fresh();
        self.vars.push(v);
        Ok((self.nodes.len() - 1) as NodeId)
    }

    fn fix(&mut self, n: NodeId, s: SV, span: (usize, usize)) -> R<()> {
        let v = self.vars[n as usize];
        if self.sorts.fix(v, s.clone()) {
            Ok(())
        } else {
            let have = self.sorts.get(v);
            Err(Diagnostic::error(
                "BW0101",
                format!(
                    "type mismatch: expected {}, found {}",
                    self.show(&Some(s)),
                    self.show(&have)
                ),
                span,
            ))
        }
    }

    fn unify(&mut self, a: NodeId, b: NodeId, span: (usize, usize)) -> R<()> {
        let (va, vb) = (self.vars[a as usize], self.vars[b as usize]);
        if self.sorts.unify(va, vb) {
            Ok(())
        } else {
            let (x, y) = (self.sorts.get(va), self.sorts.get(vb));
            Err(Diagnostic::error(
                "BW0101",
                format!(
                    "operand widths differ: {} vs {}",
                    self.show(&x),
                    self.show(&y)
                ),
                span,
            ))
        }
    }

    fn show(&self, s: &Option<SV>) -> String {
        match s {
            None => "an unknown width".into(),
            Some(SV::Bool) => "a guard condition".into(),
            Some(SV::Bv(w)) => format!("bv<{}>", w.display(&self.width_vars)),
        }
    }
}

struct Parser<'a> {
    src: &'a str,
    toks: Vec<Token>,
    pos: usize,
    diags: Vec<Diagnostic>,
    limits: CompileLimits,
    /// Nesting of parenthesized width expressions.
    wdepth: u32,
    /// Validation work spent so far (see `CompileLimits::max_work`).
    work: u64,
}

const MAX_DEPTH: u32 = 64;

impl Parser<'_> {
    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }
    fn peek2(&self) -> &Tok {
        &self.toks[(self.pos + 1).min(self.toks.len() - 1)].tok
    }
    fn span(&self) -> (usize, usize) {
        let t = &self.toks[self.pos];
        (t.start, t.end)
    }
    fn prev_end(&self) -> usize {
        self.toks[self.pos.saturating_sub(1)].end
    }
    fn bump(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }
    fn err<T>(&self, code: &'static str, msg: &str) -> R<T> {
        Err(Diagnostic::error(code, msg, self.span()))
    }
    fn expect(&mut self, t: Tok, what: &str) -> R<Token> {
        if *self.peek() == t {
            Ok(self.bump())
        } else {
            self.err("BW0001", &format!("expected {what}"))
        }
    }
    fn ident(&mut self, what: &str) -> R<(String, (usize, usize))> {
        let sp = self.span();
        match self.bump().tok {
            Tok::Ident(s) => Ok((s, sp)),
            _ => Err(Diagnostic::error("BW0001", format!("expected {what}"), sp)),
        }
    }
    fn is_ident(&self, s: &str) -> bool {
        matches!(self.peek(), Tok::Ident(x) if x == s)
    }

    /// Skips to the end of the current rule after an error, so later rules are still checked.
    fn recover(&mut self) {
        let mut depth = 0i32;
        loop {
            match self.peek() {
                Tok::Eof => return,
                Tok::LBrace => depth += 1,
                Tok::RBrace => {
                    depth -= 1;
                    if depth <= 0 {
                        self.bump();
                        return;
                    }
                }
                Tok::Ident(s) if depth == 0 && (s == "rule" || s == "identity") => return,
                _ => {}
            }
            self.bump();
        }
    }

    // ----- width expressions ----------------------------------------------------------------

    fn wprimary(&mut self, b: &RuleBuilder) -> R<WExpr> {
        let sp = self.span();
        match self.bump().tok {
            Tok::Int(d, 10) => d
                .parse::<i64>()
                .ok()
                .filter(|&v| v <= 1 << 20)
                .map(WExpr::konst)
                .ok_or_else(|| Diagnostic::error("BW0102", "width constant too large", sp)),
            Tok::Ident(name) => match b.width_vars.iter().position(|v| *v == name) {
                Some(i) => Ok(WExpr::var(i as u8)),
                None => Err(Diagnostic::error(
                    "BW0102",
                    format!("`{name}` is not a width variable of this rule"),
                    sp,
                )),
            },
            Tok::LParen => {
                if self.wdepth >= MAX_DEPTH {
                    return Err(Diagnostic::error(
                        "BW0100",
                        "width expression nested too deeply",
                        sp,
                    ));
                }
                self.wdepth += 1;
                let e = self.wexpr(b);
                self.wdepth -= 1;
                let e = e?;
                self.expect(Tok::RParen, "`)`")?;
                Ok(e)
            }
            _ => Err(Diagnostic::error("BW0102", "expected a width", sp)),
        }
    }

    fn wterm(&mut self, b: &RuleBuilder) -> R<WExpr> {
        let sp = self.span();
        let too_big = || Diagnostic::error("BW0102", "width expression too large", sp);
        let mut e = self.wprimary(b)?;
        while *self.peek() == Tok::Star {
            self.bump();
            let f = self.wprimary(b)?;
            e = match (e.as_konst(), f.as_konst()) {
                (Some(k), _) => f.scale(k).ok_or_else(too_big)?,
                (_, Some(k)) => e.scale(k).ok_or_else(too_big)?,
                _ => {
                    return Err(Diagnostic::error(
                        "BW0102",
                        "width expressions must be linear",
                        sp,
                    ));
                }
            };
        }
        Ok(e)
    }

    fn wexpr(&mut self, b: &RuleBuilder) -> R<WExpr> {
        let mut e = self.wterm(b)?;
        loop {
            let sign = match self.peek() {
                Tok::Plus => 1,
                Tok::Minus => -1,
                _ => return Ok(e),
            };
            self.bump();
            let sp = self.span();
            let t = self.wterm(b)?;
            e = e
                .add(&t, sign)
                .ok_or_else(|| Diagnostic::error("BW0102", "width expression too large", sp))?;
        }
    }

    fn wcons(&mut self, b: &RuleBuilder) -> R<WCons> {
        let lhs = self.wexpr(b)?;
        if *self.peek() == Tok::Percent {
            self.bump();
            let sp = self.span();
            let m = match self.bump().tok {
                Tok::Int(d, 10) => d.parse::<u16>().ok().filter(|&m| m > 0),
                _ => None,
            }
            .ok_or_else(|| Diagnostic::error("BW0102", "expected a modulus", sp))?;
            self.expect(Tok::Eq, "`==`")?;
            let sp = self.span();
            let r = match self.bump().tok {
                Tok::Int(d, 10) => d.parse::<u16>().ok().filter(|&r| r < m),
                _ => None,
            }
            .ok_or_else(|| Diagnostic::error("BW0102", "expected a remainder", sp))?;
            return Ok(WCons::Mod(lhs, m, r));
        }
        let op = match self.peek() {
            Tok::Eq => WCmp::Eq,
            Tok::Ne => WCmp::Ne,
            Tok::LAngle => WCmp::Lt,
            Tok::RAngle => WCmp::Gt,
            Tok::Le => WCmp::Le,
            Tok::Ge => WCmp::Ge,
            _ => return self.err("BW0102", "expected `==`, `!=`, `<`, `>`, `<=` or `>=`"),
        };
        self.bump();
        let rhs = self.wexpr(b)?;
        Ok(WCons::Cmp(lhs, op, rhs))
    }

    // ----- value and guard expressions ------------------------------------------------------

    fn expr(&mut self, b: &mut RuleBuilder, depth: u32) -> R<NodeId> {
        if depth > MAX_DEPTH {
            return self.err("BW0001", "expression nested too deeply");
        }
        self.or_expr(b, depth)
    }

    fn or_expr(&mut self, b: &mut RuleBuilder, depth: u32) -> R<NodeId> {
        let start = self.span().0;
        let mut l = self.and_expr(b, depth)?;
        while *self.peek() == Tok::OrOr {
            self.bump();
            let r = self.and_expr(b, depth)?;
            let sp = (start, self.prev_end());
            l = b.node(RNode::Or(l, r), sp)?;
            b.fix(l, SV::Bool, sp)?;
        }
        Ok(l)
    }

    fn and_expr(&mut self, b: &mut RuleBuilder, depth: u32) -> R<NodeId> {
        let start = self.span().0;
        let mut l = self.cmp_expr(b, depth)?;
        while *self.peek() == Tok::AndAnd {
            self.bump();
            let r = self.cmp_expr(b, depth)?;
            let sp = (start, self.prev_end());
            l = b.node(RNode::And(l, r), sp)?;
            b.fix(l, SV::Bool, sp)?;
        }
        Ok(l)
    }

    fn cmp_expr(&mut self, b: &mut RuleBuilder, depth: u32) -> R<NodeId> {
        let start = self.span().0;
        let l = self.binary(b, depth, 0)?;
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
            _ => return Ok(l),
        };
        self.bump();
        let r = self.binary(b, depth, 0)?;
        let sp = (start, self.prev_end());
        b.unify(l, r, sp)?;
        let n = b.node(RNode::Cmp(op, l, r), sp)?;
        b.fix(n, SV::Bv(WExpr::konst(1)), sp)?;
        Ok(n)
    }

    fn binary(&mut self, b: &mut RuleBuilder, depth: u32, min_prec: u8) -> R<NodeId> {
        let start = self.span().0;
        let mut l = self.unary(b, depth)?;
        loop {
            let (op, prec) = match self.peek() {
                Tok::Pipe => (BinOp::Or, 2),
                Tok::Caret => (BinOp::Xor, 3),
                Tok::Amp => (BinOp::And, 4),
                Tok::Shl => (BinOp::Shl, 5),
                Tok::LShr => (BinOp::LShr, 5),
                Tok::AShr => (BinOp::AShr, 5),
                Tok::Plus => (BinOp::Add, 6),
                Tok::Minus => (BinOp::Sub, 6),
                Tok::Star => (BinOp::Mul, 7),
                _ => return Ok(l),
            };
            if prec < min_prec {
                return Ok(l);
            }
            self.bump();
            let r = self.binary(b, depth, prec + 1)?;
            let sp = (start, self.prev_end());
            b.unify(l, r, sp)?;
            let n = b.node(RNode::Bin(op, l, r), sp)?;
            b.unify(n, l, sp)?;
            l = n;
        }
    }

    fn unary(&mut self, b: &mut RuleBuilder, depth: u32) -> R<NodeId> {
        if depth > MAX_DEPTH {
            return self.err("BW0100", "expression nested too deeply");
        }
        let start = self.span().0;
        match self.peek() {
            Tok::Tilde | Tok::Minus => {
                let op = if *self.peek() == Tok::Tilde {
                    UnOp::Not
                } else {
                    UnOp::Neg
                };
                self.bump();
                let a = self.unary(b, depth + 1)?;
                let sp = (start, self.prev_end());
                // `-<literal>` is a negative literal.
                if op == UnOp::Neg
                    && a as usize + 1 == b.nodes.len()
                    && let RNode::Lit(Literal::Int {
                        limbs,
                        negative: false,
                    }) = &b.nodes[a as usize]
                {
                    b.nodes[a as usize] = RNode::Lit(Literal::Int {
                        limbs: limbs.clone(),
                        negative: true,
                    });
                    b.spans[a as usize] = sp;
                    return Ok(a);
                }
                let n = b.node(RNode::Un(op, a), sp)?;
                b.unify(n, a, sp)?;
                Ok(n)
            }
            Tok::Bang => {
                self.bump();
                let a = self.unary(b, depth + 1)?;
                let sp = (start, self.prev_end());
                let n = b.node(RNode::Not(a), sp)?;
                b.fix(n, SV::Bool, sp)?;
                Ok(n)
            }
            _ => self.postfix(b, depth),
        }
    }

    fn postfix(&mut self, b: &mut RuleBuilder, depth: u32) -> R<NodeId> {
        let e = self.primary(b, depth)?;
        if *self.peek() == Tok::Colon {
            self.bump();
            let sp = self.span();
            let w = self.wexpr(b)?;
            b.fix(e, SV::Bv(w), sp)?;
        }
        Ok(e)
    }

    fn primary(&mut self, b: &mut RuleBuilder, depth: u32) -> R<NodeId> {
        let sp = self.span();
        let t = self.bump();
        match t.tok {
            Tok::Int(digits, radix) => {
                let limbs = parse_limbs(&digits, radix)
                    .ok_or_else(|| Diagnostic::error("BW0103", "literal exceeds 512 bits", sp))?;
                b.node(
                    RNode::Lit(Literal::Int {
                        limbs,
                        negative: false,
                    }),
                    sp,
                )
            }
            Tok::LParen => {
                let e = self.expr(b, depth + 1)?;
                self.expect(Tok::RParen, "`)`")?;
                Ok(e)
            }
            Tok::Ident(name) => self.name(b, depth, name, sp),
            _ => Err(Diagnostic::error("BW0001", "expected an expression", sp)),
        }
    }

    fn name(
        &mut self,
        b: &mut RuleBuilder,
        depth: u32,
        name: String,
        sp: (usize, usize),
    ) -> R<NodeId> {
        let lit = |b: &mut RuleBuilder, l: Literal| b.node(RNode::Lit(l), sp);
        match name.as_str() {
            "true" | "false" => {
                let n = lit(
                    b,
                    Literal::Int {
                        limbs: vec![u64::from(name == "true")],
                        negative: false,
                    },
                )?;
                b.fix(n, SV::Bv(WExpr::konst(1)), sp)?;
                return Ok(n);
            }
            "ones" => return lit(b, Literal::Ones),
            "zero" => {
                return lit(
                    b,
                    Literal::Int {
                        limbs: vec![0],
                        negative: false,
                    },
                );
            }
            "one" => {
                return lit(
                    b,
                    Literal::Int {
                        limbs: vec![1],
                        negative: false,
                    },
                );
            }
            "smin_lit" => return lit(b, Literal::SMin),
            "smax_lit" => return lit(b, Literal::SMax),
            _ => {}
        }
        if name.starts_with("fp.") {
            return self.fp_call(b, depth, &name, sp);
        }
        if *self.peek() == Tok::LParen || *self.peek() == Tok::LAngle {
            return self.call(b, depth, &name, sp);
        }
        if b.modes.contains(&name) {
            return Err(Diagnostic::error(
                "BW0101",
                format!("`{name}` is a rounding mode, not a value: write `fp.add.{name}<E, S>(…)`"),
                sp,
            ));
        }
        if let Some(&i) = b.param_index.get(&name) {
            let w = b.params[i as usize].width.clone();
            let n = b.node(RNode::Param(i), sp)?;
            b.fix(n, SV::Bv(w), sp)?;
            return Ok(n);
        }
        if let Some(i) = b.width_vars.iter().position(|v| *v == name) {
            return lit(b, Literal::Width(WExpr::var(i as u8)));
        }
        // A `let` name, possibly defined later in the rule body.
        let n = b.node(RNode::Let(u16::MAX), sp)?;
        b.pending.push((n, name));
        Ok(n)
    }

    fn generics(&mut self, b: &RuleBuilder, count: usize) -> R<Vec<WExpr>> {
        self.expect(Tok::LAngle, "`<`")?;
        let mut out = Vec::new();
        for k in 0..count {
            if k > 0 {
                self.expect(Tok::Comma, "`,`")?;
            }
            out.push(self.wexpr(b)?);
        }
        self.expect(Tok::RAngle, "`>`")?;
        Ok(out)
    }

    fn args(&mut self, b: &mut RuleBuilder, depth: u32, count: usize) -> R<Vec<NodeId>> {
        self.expect(Tok::LParen, "`(`")?;
        let mut out = Vec::new();
        for k in 0..count {
            if k > 0 {
                self.expect(Tok::Comma, "`,`")?;
            }
            out.push(self.expr(b, depth + 1)?);
        }
        self.expect(Tok::RParen, "`)`")?;
        Ok(out)
    }

    fn call(
        &mut self,
        b: &mut RuleBuilder,
        depth: u32,
        name: &str,
        start: (usize, usize),
    ) -> R<NodeId> {
        let span = |p: &Self| (start.0, p.prev_end());
        let un = match name {
            "popcnt" => Some(UnOp::Popcnt),
            "clz" => Some(UnOp::Clz),
            "ctz" => Some(UnOp::Ctz),
            "bswap" => Some(UnOp::Bswap),
            "bitrev" => Some(UnOp::BitRev),
            _ => None,
        };
        if let Some(op) = un {
            let a = self.args(b, depth, 1)?[0];
            let sp = span(self);
            let n = b.node(RNode::Un(op, a), sp)?;
            b.unify(n, a, sp)?;
            return Ok(n);
        }
        let bin = match name {
            "udiv" => Some(BinOp::UDiv),
            "urem" => Some(BinOp::URem),
            "sdiv" => Some(BinOp::SDiv),
            "srem" => Some(BinOp::SRem),
            "rotl" => Some(BinOp::RotL),
            "rotr" => Some(BinOp::RotR),
            "umulhi" => Some(BinOp::UMulHi),
            "smulhi" => Some(BinOp::SMulHi),
            "pdep" => Some(BinOp::Pdep),
            "pext" => Some(BinOp::Pext),
            _ => None,
        };
        if let Some(op) = bin {
            let a = self.args(b, depth, 2)?;
            let sp = span(self);
            b.unify(a[0], a[1], sp)?;
            let n = b.node(RNode::Bin(op, a[0], a[1]), sp)?;
            b.unify(n, a[0], sp)?;
            return Ok(n);
        }
        match name {
            "zext" | "sext" | "trunc" => {
                let g = self.generics(b, 1)?;
                let a = self.args(b, depth, 1)?[0];
                let sp = span(self);
                let to = g[0].clone();
                let node = match name {
                    "zext" => RNode::Zext(a),
                    "sext" => RNode::Sext(a),
                    _ => RNode::Extract(WExpr::konst(0), a),
                };
                let n = b.node(node, sp)?;
                b.fix(n, SV::Bv(to), sp)?;
                Ok(n)
            }
            "extract" => {
                let g = self.generics(b, 2)?;
                let a = self.args(b, depth, 1)?[0];
                let sp = span(self);
                let n = b.node(RNode::Extract(g[0].clone(), a), sp)?;
                b.fix(n, SV::Bv(g[1].clone()), sp)?;
                Ok(n)
            }
            "concat" => {
                let a = self.args(b, depth, 2)?;
                let sp = span(self);
                b.node(RNode::Concat(a[0], a[1]), sp)
            }
            "select" => {
                let a = self.args(b, depth, 3)?;
                let sp = span(self);
                b.fix(a[0], SV::Bv(WExpr::konst(1)), sp)?;
                b.unify(a[1], a[2], sp)?;
                let n = b.node(RNode::Select(a[0], a[1], a[2]), sp)?;
                b.unify(n, a[1], sp)?;
                Ok(n)
            }
            "lowmask" | "bit" => {
                self.expect(Tok::LParen, "`(`")?;
                let k = self.wexpr(b)?;
                self.expect(Tok::RParen, "`)`")?;
                let sp = span(self);
                let l = if name == "lowmask" {
                    Literal::LowMask(k)
                } else {
                    Literal::Bit(k)
                };
                b.node(RNode::Lit(l), sp)
            }
            "umin" | "umax" | "smin" | "smax" => {
                let a = self.args(b, depth, 2)?;
                let sp = span(self);
                b.unify(a[0], a[1], sp)?;
                let op = if name.starts_with('u') {
                    CmpOpExt::Ult
                } else {
                    CmpOpExt::Slt
                };
                let c = b.node(RNode::Cmp(op, a[0], a[1]), sp)?;
                b.fix(c, SV::Bv(WExpr::konst(1)), sp)?;
                let (t, f) = if name.ends_with("min") {
                    (a[0], a[1])
                } else {
                    (a[1], a[0])
                };
                let n = b.node(RNode::Select(c, t, f), sp)?;
                b.unify(n, a[0], sp)?;
                Ok(n)
            }
            "disjoint" => {
                let a = self.args(b, depth, 2)?;
                let sp = span(self);
                b.unify(a[0], a[1], sp)?;
                let n = b.node(RNode::Fact(FactPred::Disjoint, a[0], Some(a[1])), sp)?;
                b.fix(n, SV::Bool, sp)?;
                Ok(n)
            }
            "zero_bits" | "one_bits" => {
                let a = self.args(b, depth, 2)?;
                let sp = span(self);
                b.unify(a[0], a[1], sp)?;
                let p = if name == "zero_bits" {
                    FactPred::ZeroBits
                } else {
                    FactPred::OneBits
                };
                let n = b.node(RNode::Fact(p, a[0], Some(a[1])), sp)?;
                b.fix(n, SV::Bool, sp)?;
                Ok(n)
            }
            "nonzero" => {
                let a = self.args(b, depth, 1)?[0];
                let sp = span(self);
                let n = b.node(RNode::Fact(FactPred::NonZero, a, None), sp)?;
                b.fix(n, SV::Bool, sp)?;
                Ok(n)
            }
            "proves" => {
                let a = self.args(b, depth, 1)?[0];
                let sp = span(self);
                if !matches!(b.nodes[a as usize], RNode::Cmp(..)) {
                    return Err(Diagnostic::error(
                        "BW0104",
                        "`proves` takes a comparison, e.g. `proves(b != c)`",
                        sp,
                    ));
                }
                let n = b.node(RNode::Fact(FactPred::Proves, a, None), sp)?;
                b.fix(n, SV::Bool, sp)?;
                Ok(n)
            }
            "is_pow2" | "is_lowmask" | "is_shifted_mask" => {
                let a = self.args(b, depth, 1)?[0];
                let sp = span(self);
                let p = match name {
                    "is_pow2" => ConstPred::IsPow2,
                    "is_lowmask" => ConstPred::IsLowMask,
                    _ => ConstPred::IsShiftedMask,
                };
                let n = b.node(RNode::ConstP(p, a), sp)?;
                b.fix(n, SV::Bool, sp)?;
                Ok(n)
            }
            _ => Err(Diagnostic::error(
                "BW0001",
                format!("unknown function `{name}`"),
                start,
            )),
        }
    }

    /// A floating-point call, `fp.<op>[.<mode>](.<format>… | <eb, sb, …>)(operands)`, or a
    /// floating-point constant, `fp.<name>(.<format> | <eb, sb>)`. The operations the
    /// builder makes from other operators (`neg`, `abs`, `copysign`, `sub`, `gt`, `ge`, the
    /// tests) are written out the same way here, so a pattern matches what the builder makes.
    fn fp_call(
        &mut self,
        b: &mut RuleBuilder,
        depth: u32,
        name: &str,
        start: (usize, usize),
    ) -> R<NodeId> {
        let span = |p: &Self| (start.0, p.prev_end());
        let bad = |m: String| Diagnostic::error("BW0001", m, start);
        let too_big = |sp| Diagnostic::error("BW0102", "width expression too large", sp);
        let konst = |v: u32| WExpr::konst(i64::from(v));
        let mut parts = name.split('.');
        parts.next();
        let op = parts.next().unwrap_or("");
        if let Some(value) = float_lit(op) {
            let rest: Vec<&str> = parts.collect();
            let (eb, sb) = match rest.as_slice() {
                [] => {
                    let g = self.generics(b, 2)?;
                    (g[0].clone(), g[1].clone())
                }
                [f] => {
                    let f = FpFormat::from_name(f).ok_or_else(|| {
                        bad(format!(
                            "`{f}` is not a format name (f16, bf16, f32, f64, f128, f256)"
                        ))
                    })?;
                    (konst(f.eb()), konst(f.sb()))
                }
                _ => return Err(bad(format!("`fp.{op}` takes one format"))),
            };
            let sp = span(self);
            let w = eb.add(&sb, 1).ok_or_else(|| too_big(sp))?;
            let n = b.node(RNode::Lit(Literal::Float { value, eb }), sp)?;
            b.fix(n, SV::Bv(w), sp)?;
            return Ok(n);
        }
        if let Some(pred) = match op {
            "not_nan" => Some(FactPred::FpNotNan),
            "finite" => Some(FactPred::FpFinite),
            "nonzero" => Some(FactPred::FpNonZero),
            _ => None,
        } {
            // A guard predicate on a float, true only when the facts prove it.
            let rest: Vec<&str> = parts.collect();
            let (eb, sb) = match rest.as_slice() {
                [] => {
                    let g = self.generics(b, 2)?;
                    (g[0].clone(), g[1].clone())
                }
                [f] => {
                    let f = FpFormat::from_name(f).ok_or_else(|| {
                        bad(format!(
                            "`{f}` is not a format name (f16, bf16, f32, f64, f128, f256)"
                        ))
                    })?;
                    (konst(f.eb()), konst(f.sb()))
                }
                _ => return Err(bad(format!("`fp.{op}` takes one format"))),
            };
            let x = self.args(b, depth, 1)?[0];
            let sp = span(self);
            let fw = eb.add(&sb, 1).ok_or_else(|| too_big(sp))?;
            b.fix(x, SV::Bv(fw.clone()), sp)?;
            let inf = b.node(
                RNode::Lit(Literal::Float {
                    value: FloatLit::Inf,
                    eb,
                }),
                sp,
            )?;
            b.fix(inf, SV::Bv(fw), sp)?;
            let n = b.node(RNode::Fact(pred, x, Some(inf)), sp)?;
            b.fix(n, SV::Bool, sp)?;
            return Ok(n);
        }
        let (base, rm_word, named) = crate::fp::syntax::split_name(name).map_err(bad)?;
        let rounding = match rm_word {
            None => None,
            Some(m) => Some(match RoundingMode::from_name(m) {
                Some(mode) => Rounding::Mode(mode),
                None => match b.modes.iter().position(|v| v == m) {
                    Some(i) => Rounding::Var(i as u8),
                    None => {
                        return Err(bad(format!(
                            "`{m}` is not a rounding mode (rne, rna, rtp, rtn, rtz) or a \
                             rounding-mode parameter (`{m}: rm`)"
                        )));
                    }
                },
            }),
        };
        if matches!(base, Base::X87Load | Base::X87Store) {
            return Err(bad("x87's load and store are not available in rules".into()));
        }
        let count = 2 * (base.formats() - named.len()) + usize::from(base.int_width());
        let g = if count > 0 {
            self.generics(b, count)?
        } else {
            Vec::new()
        };
        let mut g = g.into_iter();
        let mut formats: Vec<(WExpr, WExpr)> = named
            .iter()
            .map(|f| (konst(f.eb()), konst(f.sb())))
            .collect();
        while formats.len() < base.formats() {
            match (g.next(), g.next()) {
                (Some(e), Some(s)) => formats.push((e, s)),
                _ => return Err(bad("missing format".into())),
            }
        }
        let int_width = g.next();
        let args = self.args(b, depth, base.arity())?;
        let sp = span(self);
        let (eb, sb) = formats[0].clone();
        let fw = eb.add(&sb, 1).ok_or_else(|| too_big(sp))?;
        let fixed = |b: &mut RuleBuilder, n: RNode, w: &WExpr| -> R<NodeId> {
            let k = b.node(n, sp)?;
            b.fix(k, SV::Bv(w.clone()), sp)?;
            Ok(k)
        };
        let lit = |b: &mut RuleBuilder, l: Literal| fixed(b, RNode::Lit(l), &fw);
        let float = |b: &mut RuleBuilder, v: FloatLit| {
            fixed(
                b,
                RNode::Lit(Literal::Float {
                    value: v,
                    eb: eb.clone(),
                }),
                &fw,
            )
        };
        let bin = |b: &mut RuleBuilder, op: BinOp, x: NodeId, y: NodeId| {
            fixed(b, RNode::Bin(op, x, y), &fw)
        };
        let cmp = |b: &mut RuleBuilder, op: CmpOpExt, x: NodeId, y: NodeId| {
            fixed(b, RNode::Cmp(op, x, y), &WExpr::konst(1))
        };
        let node = |b: &mut RuleBuilder, kind: FpKind, args: Vec<NodeId>| -> R<NodeId> {
            let from_int = matches!(kind, FpKind::FromSInt | FpKind::FromUInt);
            if !from_int {
                for &a in &args {
                    b.fix(a, SV::Bv(fw.clone()), sp)?;
                }
            }
            let to = formats.get(1).cloned();
            let result = match kind {
                FpKind::Eq | FpKind::Lt | FpKind::Le => WExpr::konst(1),
                FpKind::Convert => {
                    let (e, s) = to.clone().ok_or_else(|| bad("missing format".into()))?;
                    e.add(&s, 1).ok_or_else(|| too_big(sp))?
                }
                FpKind::ToSInt | FpKind::ToUInt => int_width
                    .clone()
                    .ok_or_else(|| bad("missing integer width".into()))?,
                _ => fw.clone(),
            };
            let n = RNode::Fp(FpNode {
                kind,
                rounding,
                eb: eb.clone(),
                sb: sb.clone(),
                to,
                args,
            });
            fixed(b, n, &result)
        };
        for &a in &args {
            if !matches!(base, Base::Op(FpKind::FromSInt | FpKind::FromUInt)) {
                b.fix(a, SV::Bv(fw.clone()), sp)?;
            }
        }
        match base {
            Base::Op(kind) => node(b, kind, args),
            Base::Sub => {
                let s = lit(b, Literal::SMin)?;
                let nb = bin(b, BinOp::Xor, args[1], s)?;
                node(b, FpKind::Add, vec![args[0], nb])
            }
            Base::Neg => {
                let s = lit(b, Literal::SMin)?;
                bin(b, BinOp::Xor, args[0], s)
            }
            Base::Abs => {
                let s = lit(b, Literal::SMax)?;
                bin(b, BinOp::And, args[0], s)
            }
            Base::CopySign => {
                let m = lit(b, Literal::SMax)?;
                let mag = bin(b, BinOp::And, args[0], m)?;
                let s = lit(b, Literal::SMin)?;
                let sign = bin(b, BinOp::And, args[1], s)?;
                bin(b, BinOp::Or, mag, sign)
            }
            Base::Gt => node(b, FpKind::Lt, vec![args[1], args[0]]),
            Base::Ge => node(b, FpKind::Le, vec![args[1], args[0]]),
            Base::Test(t) => {
                let m = lit(b, Literal::SMax)?;
                let mut mag = || bin(b, BinOp::And, args[0], m);
                match t {
                    FpTest::Nan => {
                        let mag = mag()?;
                        let i = float(b, FloatLit::Inf)?;
                        cmp(b, CmpOpExt::Ult, i, mag)
                    }
                    FpTest::Infinite => {
                        let mag = mag()?;
                        let i = float(b, FloatLit::Inf)?;
                        cmp(b, CmpOpExt::Eq, mag, i)
                    }
                    FpTest::Zero => {
                        let mag = mag()?;
                        let z = lit(
                            b,
                            Literal::Int {
                                limbs: vec![0],
                                negative: false,
                            },
                        )?;
                        cmp(b, CmpOpExt::Eq, mag, z)
                    }
                    FpTest::Subnormal => {
                        // (|a| - 1) <u (min_normal - 1), as the builder writes it.
                        let mag = mag()?;
                        let ones = lit(b, Literal::Ones)?;
                        let shifted = bin(b, BinOp::Add, mag, ones)?;
                        let k = sb.add(&WExpr::konst(1), -1).ok_or_else(|| too_big(sp))?;
                        let bound = lit(b, Literal::LowMask(k))?;
                        cmp(b, CmpOpExt::Ult, shifted, bound)
                    }
                    FpTest::Normal => {
                        // (|a| - min_normal) <u (inf - min_normal).
                        let mag = mag()?;
                        let mn = float(b, FloatLit::MinNormal)?;
                        let neg = fixed(b, RNode::Un(UnOp::Neg, mn), &fw)?;
                        let shifted = bin(b, BinOp::Add, mag, neg)?;
                        let i = float(b, FloatLit::Inf)?;
                        let mn2 = float(b, FloatLit::MinNormal)?;
                        let bound = bin(b, BinOp::Sub, i, mn2)?;
                        cmp(b, CmpOpExt::Ult, shifted, bound)
                    }
                    FpTest::Negative => {
                        let s = lit(b, Literal::SMin)?;
                        let flipped = bin(b, BinOp::Xor, args[0], s)?;
                        let i = float(b, FloatLit::Inf)?;
                        cmp(b, CmpOpExt::Ule, flipped, i)
                    }
                    _ => {
                        let i = float(b, FloatLit::Inf)?;
                        cmp(b, CmpOpExt::Ule, args[0], i)
                    }
                }
            }
            Base::X87Load | Base::X87Store => unreachable!("refused above"),
        }
    }

    // ----- items ------------------------------------------------------------------------------

    fn attrs(&mut self) -> R<Attrs> {
        let (mut examples, mut allows, mut doc) = (Vec::new(), Vec::new(), String::new());
        loop {
            match self.peek().clone() {
                Tok::Doc(d) => {
                    self.bump();
                    if !doc.is_empty() {
                        doc.push('\n');
                    }
                    doc.push_str(&d);
                }
                Tok::AttrOpen => {
                    self.bump();
                    let (name, sp) = self.ident("an attribute name")?;
                    match name.as_str() {
                        "example" => {
                            self.expect(Tok::LParen, "`(`")?;
                            let a = self.string()?;
                            self.expect(Tok::FatArrow, "`=>`")?;
                            let c = self.string()?;
                            self.expect(Tok::RParen, "`)`")?;
                            examples.push((a, c));
                        }
                        "allow" => {
                            self.expect(Tok::LParen, "`(`")?;
                            loop {
                                let (code, span) = self.ident("a lint code")?;
                                // Errors (unsoundness, non-termination, ill-typing) are never
                                // suppressible; only these lints are.
                                if !ALLOWABLE.contains(&code.as_str()) {
                                    return Err(Diagnostic::error(
                                        "BW0002",
                                        format!(
                                            "`{code}` cannot be allowed; allowable lints: {}",
                                            ALLOWABLE.join(", ")
                                        ),
                                        span,
                                    ));
                                }
                                allows.push(code);
                                if *self.peek() != Tok::Comma {
                                    break;
                                }
                                self.bump();
                            }
                            self.expect(Tok::RParen, "`)`")?;
                        }
                        _ => {
                            return Err(Diagnostic::error(
                                "BW0002",
                                format!("unknown attribute `{name}`"),
                                sp,
                            ));
                        }
                    }
                    self.expect(Tok::RBracket, "`]`")?;
                }
                _ => return Ok((examples, allows, doc)),
            }
        }
    }

    fn string(&mut self) -> R<String> {
        let sp = self.span();
        match self.bump().tok {
            Tok::Str(s) => Ok(s),
            _ => Err(Diagnostic::error("BW0001", "expected a string", sp)),
        }
    }

    /// Parses and finishes one rule. The flag says whether the error happened after the
    /// rule's closing brace (so the caller must not skip ahead to recover).
    fn rule(
        &mut self,
        group: usize,
        group_name: &str,
    ) -> Result<(Rule, Vec<String>), (Diagnostic, bool)> {
        self.rule_inner(group, group_name)
    }

    fn rule_inner(
        &mut self,
        group: usize,
        group_name: &str,
    ) -> Result<(Rule, Vec<String>), (Diagnostic, bool)> {
        let parsed = self.rule_parse(group, group_name).map_err(|d| (d, false))?;
        let (b, fin, allows) = parsed;
        let rule = finish_rule(b, fin, &self.limits, &mut self.work).map_err(|d| (d, true))?;
        Ok((rule, allows))
    }

    fn rule_parse(
        &mut self,
        group: usize,
        group_name: &str,
    ) -> R<(RuleBuilder, FinishInput, Vec<String>)> {
        let (examples, allows, doc) = self.attrs()?;
        let start = self.span().0;
        let kind = match self.peek() {
            Tok::Ident(s) if s == "rule" => RuleKind::Rewrite,
            Tok::Ident(s) if s == "identity" => RuleKind::Identity,
            _ => return self.err("BW0001", "expected `rule` or `identity`"),
        };
        self.bump();
        let (short, name_span) = self.ident("a rule name")?;
        let mut b = RuleBuilder {
            width_vars: Vec::new(),
            modes: Vec::new(),
            params: Vec::new(),
            param_index: HashMap::new(),
            lets: Vec::new(),
            nodes: Vec::new(),
            spans: Vec::new(),
            vars: Vec::new(),
            sorts: Sorts {
                parent: Vec::new(),
                value: Vec::new(),
            },
            pending: Vec::new(),
        };
        if *self.peek() == Tok::LAngle {
            self.bump();
            loop {
                let (v, sp) = self.ident("a width variable")?;
                if !v.starts_with(|c: char| c.is_ascii_uppercase()) {
                    return Err(Diagnostic::error(
                        "BW0102",
                        "width variables start with an upper-case letter",
                        sp,
                    ));
                }
                if b.width_vars.contains(&v) || b.width_vars.len() >= 3 {
                    return Err(Diagnostic::error(
                        "BW0102",
                        "duplicate width variable, or more than 3",
                        sp,
                    ));
                }
                b.width_vars.push(v);
                if *self.peek() != Tok::Comma {
                    break;
                }
                self.bump();
            }
            self.expect(Tok::RAngle, "`>`")?;
        }
        self.expect(Tok::LParen, "`(`")?;
        while *self.peek() != Tok::RParen {
            let (pname, sp) = self.ident("a parameter name")?;
            if crate::text::is_reserved(&pname)
                || b.param_index.contains_key(&pname)
                || b.modes.contains(&pname)
                || RoundingMode::from_name(&pname).is_some()
            {
                return Err(Diagnostic::error(
                    "BW0103",
                    format!("parameter name `{pname}` is reserved or repeated"),
                    sp,
                ));
            }
            self.expect(Tok::Colon, "`:`")?;
            if self.is_ident("rm") {
                // A rounding-mode variable: every mode, bound by the pattern.
                self.bump();
                if b.modes.len() >= 2 {
                    return Err(Diagnostic::error(
                        "BW0103",
                        "at most 2 rounding-mode parameters",
                        sp,
                    ));
                }
                b.modes.push(pname);
                if *self.peek() == Tok::Comma {
                    self.bump();
                    continue;
                }
                break;
            }
            let pkind = match self.peek() {
                Tok::Ident(s) if s == "const" => ParamKind::Const,
                Tok::Ident(s) if s == "sym" => ParamKind::Sym,
                Tok::Ident(s) if s == "nonconst" => ParamKind::NonConst,
                _ => ParamKind::Any,
            };
            if pkind != ParamKind::Any {
                self.bump();
            }
            let w = self.wexpr(&b)?;
            b.param_index.insert(pname.clone(), b.params.len() as u16);
            b.params.push(Param {
                name: pname,
                kind: pkind,
                width: w,
            });
            if *self.peek() == Tok::Comma {
                self.bump();
            } else {
                break;
            }
        }
        self.expect(Tok::RParen, "`)`")?;
        let mut constraints = Vec::new();
        if self.is_ident("where") {
            self.bump();
            loop {
                constraints.push(self.wcons(&b)?);
                if *self.peek() != Tok::Comma {
                    break;
                }
                self.bump();
            }
        }
        self.expect(Tok::LBrace, "`{`")?;
        let lhs = self.expr(&mut b, 0)?;
        let arrow_span = self.span();
        match (kind, self.peek()) {
            (RuleKind::Rewrite, Tok::FatArrow) | (RuleKind::Identity, Tok::Iff) => {
                self.bump();
            }
            (RuleKind::Rewrite, _) => return self.err("BW0001", "expected `=>`"),
            (RuleKind::Identity, _) => {
                return self.err("BW0304", "an identity is written `lhs <=> rhs`");
            }
        }
        let rhs = self.expr(&mut b, 0)?;
        b.unify(lhs, rhs, (b.spans[lhs as usize].0, self.prev_end()))?;
        let mut guard: Option<NodeId> = None;
        loop {
            if self.is_ident("if") {
                let sp = self.span();
                if kind == RuleKind::Identity {
                    return Err(Diagnostic::error("BW0304", "an identity has no guard", sp));
                }
                self.bump();
                let g = self.expr(&mut b, 0)?;
                guard = Some(match guard {
                    None => g,
                    Some(prev) => {
                        let n = b.node(RNode::And(prev, g), sp)?;
                        b.fix(n, SV::Bool, sp)?;
                        n
                    }
                });
            } else if self.is_ident("let") {
                let sp = self.span();
                if kind == RuleKind::Identity {
                    return Err(Diagnostic::error("BW0304", "an identity has no `let`", sp));
                }
                self.bump();
                let (lname, lsp) = self.ident("a name")?;
                if crate::text::is_reserved(&lname)
                    || b.param_index.contains_key(&lname)
                    || b.lets.iter().any(|(n, ..)| *n == lname)
                {
                    return Err(Diagnostic::error(
                        "BW0103",
                        format!("`{lname}` is reserved or already bound"),
                        lsp,
                    ));
                }
                self.expect(Tok::Colon, "`:`")?;
                let w = self.wexpr(&b)?;
                self.expect(Tok::Assign, "`=`")?;
                let v = self.expr(&mut b, 0)?;
                b.fix(v, SV::Bv(w.clone()), lsp)?;
                b.lets.push((lname, Some(v), w, lsp));
            } else {
                break;
            }
        }
        self.expect(Tok::RBrace, "`}`")?;
        let end = self.prev_end();
        let _ = arrow_span;
        Ok((
            b,
            FinishInput {
                name: format!("{group_name}::{short}"),
                name_span,
                group,
                kind,
                constraints,
                lhs,
                rhs,
                guard,
                examples,
                doc,
                span: (start, end),
            },
            allows,
        ))
    }
}

struct FinishInput {
    name: String,
    name_span: (usize, usize),
    group: usize,
    kind: RuleKind,
    constraints: Vec<WCons>,
    lhs: NodeId,
    rhs: NodeId,
    guard: Option<NodeId>,
    examples: Vec<(String, String)>,
    doc: String,
    span: (usize, usize),
}

/// Resolves forward `let` references, finishes width inference, and runs the static checks.
fn finish_rule(
    mut b: RuleBuilder,
    f: FinishInput,
    limits: &CompileLimits,
    work: &mut u64,
) -> R<Rule> {
    if b.nodes.len() > limits.max_nodes {
        return Err(Diagnostic::error(
            "BW0100",
            "rule has too many nodes",
            f.span,
        ));
    }
    // Forward references to lets.
    for (n, name) in std::mem::take(&mut b.pending) {
        let sp = b.spans[n as usize];
        let Some(li) = b.lets.iter().position(|(ln, ..)| *ln == name) else {
            return Err(Diagnostic::error(
                "BW0103",
                format!("unknown name `{name}`"),
                sp,
            ));
        };
        b.nodes[n as usize] = RNode::Let(li as u16);
        let v = b.lets[li].1.unwrap_or(n);
        b.unify(n, v, sp)?;
    }
    // Concatenation widths.
    let too_big = |sp| Diagnostic::error("BW0102", "width expression too large", sp);
    loop {
        let mut changed = false;
        for i in 0..b.nodes.len() {
            if let RNode::Concat(h, l) = b.nodes[i] {
                let (vn, vh, vl) = (b.vars[i], b.vars[h as usize], b.vars[l as usize]);
                let (sn, sh, sl) = (b.sorts.get(vn), b.sorts.get(vh), b.sorts.get(vl));
                let sp = b.spans[i];
                match (sn, sh, sl) {
                    (None, Some(SV::Bv(x)), Some(SV::Bv(y))) => {
                        b.fix(
                            i as NodeId,
                            SV::Bv(x.add(&y, 1).ok_or_else(|| too_big(sp))?),
                            sp,
                        )?;
                        changed = true;
                    }
                    (Some(SV::Bv(t)), Some(SV::Bv(x)), None) => {
                        b.fix(l, SV::Bv(t.add(&x, -1).ok_or_else(|| too_big(sp))?), sp)?;
                        changed = true;
                    }
                    (Some(SV::Bv(t)), None, Some(SV::Bv(y))) => {
                        b.fix(h, SV::Bv(t.add(&y, -1).ok_or_else(|| too_big(sp))?), sp)?;
                        changed = true;
                    }
                    (Some(SV::Bv(t)), Some(SV::Bv(x)), Some(SV::Bv(y)))
                        if x.add(&y, 1).as_ref() != Some(&t) =>
                    {
                        return Err(Diagnostic::error(
                            "BW0101",
                            "concatenation widths do not add up",
                            sp,
                        ));
                    }
                    _ => {}
                }
            }
        }
        if !changed {
            break;
        }
    }
    let mut sorts = Vec::with_capacity(b.nodes.len());
    for i in 0..b.nodes.len() {
        match b.sorts.get(b.vars[i]) {
            Some(SV::Bv(w)) => sorts.push(Sort::Bv(w)),
            Some(SV::Bool) => sorts.push(Sort::Bool),
            None => {
                return Err(Diagnostic::error(
                    "BW0101",
                    "cannot infer this width; write `:W` (for example `1:W`)",
                    b.spans[i],
                ));
            }
        }
    }
    let lets: Vec<LetDef> = b
        .lets
        .iter()
        .map(|(name, v, _, _)| LetDef {
            name: name.clone(),
            value: v.unwrap_or(0),
        })
        .collect();
    let mut rule = Rule {
        name: f.name,
        group: f.group,
        kind: f.kind,
        id: RuleId([0, 0]),
        width_vars: b.width_vars,
        modes: b.modes,
        constraints: f.constraints,
        params: b.params,
        lets,
        nodes: b.nodes,
        sorts,
        lhs: f.lhs,
        rhs: f.rhs,
        guard: f.guard,
        decreasing: false,
        examples: f.examples,
        doc: f.doc,
        span: f.span,
        admitted_widths: None,
    };
    static_checks(&rule, &b.spans, f.name_span)?;
    let mut assignments = 0u64;
    for_each_assignment(&rule, |_| {
        assignments += 1;
        true
    });
    let cost = (rule.nodes.len() as u64).saturating_mul(assignments);
    *work = work.saturating_add(cost.saturating_mul(2));
    if *work > limits.max_work {
        return Err(Diagnostic::error(
            "BW0100",
            "the program is too costly to validate (width variables × rule size); \
             raise `CompileLimits::max_work`",
            f.span,
        ));
    }
    rule.admitted_widths = validate_widths(&rule, &b.spans)?;
    rule.decreasing = kbo_greater(&rule, rule.lhs, rule.rhs);
    rule.id = rule_id(&rule);
    Ok(rule)
}

fn walk(rule: &Rule, root: NodeId, mut f: impl FnMut(NodeId)) {
    let mut stack = vec![root];
    while let Some(n) = stack.pop() {
        f(n);
        push_children(&rule.nodes[n as usize], &mut stack);
    }
}

pub(crate) fn children(n: &RNode) -> Vec<NodeId> {
    let mut v = Vec::new();
    push_children(n, &mut v);
    v
}

/// Pushes the operands of `n` onto `out` (the walkers' stacks), in order.
pub(crate) fn push_children(n: &RNode, out: &mut Vec<NodeId>) {
    match *n {
        RNode::Param(_) | RNode::Let(_) | RNode::Lit(_) => {}
        RNode::Un(_, a)
        | RNode::Zext(a)
        | RNode::Sext(a)
        | RNode::Extract(_, a)
        | RNode::Not(a)
        | RNode::ConstP(_, a) => out.push(a),
        RNode::Bin(_, a, b)
        | RNode::Cmp(_, a, b)
        | RNode::Concat(a, b)
        | RNode::And(a, b)
        | RNode::Or(a, b) => out.extend([a, b]),
        RNode::Select(a, b, c) => out.extend([a, b, c]),
        RNode::Fact(_, a, m) => {
            out.push(a);
            out.extend(m);
        }
        RNode::Fp(ref f) => out.extend_from_slice(&f.args),
    }
}

fn is_guard_only(n: &RNode) -> bool {
    matches!(
        n,
        RNode::And(..) | RNode::Or(..) | RNode::Not(_) | RNode::Fact(..) | RNode::ConstP(..)
    )
}

/// Whether the value of `root` depends only on constant parameters, lets and literals.
fn is_pure(rule: &Rule, root: NodeId) -> bool {
    let mut pure = true;
    walk(rule, root, |n| {
        if let RNode::Param(i) = rule.nodes[n as usize]
            && rule.params[i as usize].kind != ParamKind::Const
        {
            pure = false;
        }
    });
    pure
}

/// The first width variable that matching cannot bind: widths are bound from the widths and
/// extract offsets of pattern nodes, one expression with a single unbound variable at a time
/// (the matcher does the same, in any order).
pub(crate) fn undetermined_width(rule: &Rule) -> Option<u8> {
    let mut exprs: Vec<&WExpr> = Vec::new();
    walk(rule, rule.lhs, |n| {
        if let Sort::Bv(w) = &rule.sorts[n as usize] {
            exprs.push(w);
        }
        match &rule.nodes[n as usize] {
            RNode::Extract(lo, _) => exprs.push(lo),
            RNode::Fp(f) => {
                exprs.push(&f.eb);
                exprs.extend(f.to.as_ref().map(|(e, _)| e));
            }
            _ => {}
        }
    });
    let mut bound = vec![false; rule.width_vars.len()];
    loop {
        let mut changed = false;
        for e in &exprs {
            let mut free = e.terms.iter().filter(|&&(v, _)| !bound[usize::from(v)]);
            if let (Some(&(v, _)), None) = (free.next(), free.next()) {
                bound[usize::from(v)] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    bound.iter().position(|b| !b).map(|v| v as u8)
}

fn static_checks(rule: &Rule, spans: &[(usize, usize)], name_span: (usize, usize)) -> R<()> {
    let sp = |n: NodeId| spans[n as usize];
    let err = |code, msg: &str, n: NodeId| Err(Diagnostic::error(code, msg, sp(n)));
    // Sorts of the top-level parts.
    let bv = |n: NodeId| matches!(rule.sorts[n as usize], Sort::Bv(_));
    if !bv(rule.lhs) {
        return err(
            "BW0101",
            "the pattern must be a bit-vector expression",
            rule.lhs,
        );
    }
    for part in [rule.lhs, rule.rhs] {
        let mut bad = None;
        walk(rule, part, |n| {
            if is_guard_only(&rule.nodes[n as usize]) {
                bad = Some(n);
            }
        });
        if let Some(n) = bad {
            return err("BW0104", "guard predicates belong after `if`", n);
        }
    }
    let mut let_in_lhs = None;
    walk(rule, rule.lhs, |n| {
        if matches!(rule.nodes[n as usize], RNode::Let(_)) {
            let_in_lhs = Some(n);
        }
    });
    if let Some(n) = let_in_lhs {
        return err("BW0103", "a `let` value cannot appear in the pattern", n);
    }
    // Every parameter occurs in the pattern (identities: on both sides).
    let occurs = |root: NodeId| {
        let mut seen = vec![false; rule.params.len()];
        walk(rule, root, |n| {
            if let RNode::Param(i) = rule.nodes[n as usize] {
                seen[i as usize] = true;
            }
        });
        seen
    };
    let in_lhs = occurs(rule.lhs);
    if let Some(i) = in_lhs.iter().position(|s| !s) {
        return Err(Diagnostic::error(
            "BW0103",
            format!(
                "parameter `{}` does not occur in the pattern",
                rule.params[i].name
            ),
            name_span,
        ));
    }
    if rule.kind == RuleKind::Identity {
        let in_rhs = occurs(rule.rhs);
        if let Some(i) = in_rhs.iter().position(|s| !s) {
            return Err(Diagnostic::error(
                "BW0304",
                format!(
                    "identity parameter `{}` must occur on both sides",
                    rule.params[i].name
                ),
                name_span,
            ));
        }
        if rule.params.iter().any(|p| p.kind != ParamKind::Any) {
            return Err(Diagnostic::error(
                "BW0304",
                "identity parameters take no capture kind (const, sym, nonconst)",
                name_span,
            ));
        }
    }
    // Conditions are not values: only `&&`, `||`, `!` and the guard itself take them.
    let mut misuse = None;
    for (i, node) in rule.nodes.iter().enumerate() {
        if matches!(node, RNode::And(..) | RNode::Or(..) | RNode::Not(_)) {
            continue;
        }
        for c in children(node) {
            if matches!(rule.sorts[c as usize], Sort::Bool)
                && !matches!(node, RNode::Fact(FactPred::Proves, ..))
            {
                misuse = Some(i as NodeId);
            }
        }
    }
    if let Some(n) = misuse {
        return err(
            "BW0101",
            "a condition cannot be used as a value; combine conditions with `&&`, `||` and `!`",
            n,
        );
    }
    // A `let` may use only earlier `let`s (so every `let` has a value).
    for (j, l) in rule.lets.iter().enumerate() {
        let mut bad = None;
        walk(rule, l.value, |n| {
            if let RNode::Let(i) = rule.nodes[n as usize]
                && usize::from(i) >= j
            {
                bad = Some(n);
            }
        });
        if let Some(n) = bad {
            return err("BW0105", "a `let` may only use earlier `let`s", n);
        }
    }
    // Every width variable is determined by the pattern, so a match binds it.
    if let Some(v) = undetermined_width(rule) {
        return Err(Diagnostic::error(
            "BW0102",
            format!(
                "width variable `{}` is not determined by the pattern",
                rule.width_vars[usize::from(v)]
            ),
            name_span,
        ));
    }
    // Every rounding-mode variable is bound by the pattern too.
    let mut bound_modes = vec![false; rule.modes.len()];
    walk(rule, rule.lhs, |n| {
        if let RNode::Fp(f) = &rule.nodes[n as usize]
            && let Some(super::ir::Rounding::Var(i)) = f.rounding
        {
            bound_modes[usize::from(i)] = true;
        }
    });
    if let Some(i) = bound_modes.iter().position(|b| !b) {
        return Err(Diagnostic::error(
            "BW0102",
            format!(
                "rounding-mode parameter `{}` does not occur in the pattern",
                rule.modes[i]
            ),
            name_span,
        ));
    }
    // Lets are constant computations.
    for l in &rule.lets {
        if !is_pure(rule, l.value) {
            return err(
                "BW0105",
                "a `let` may only use constant parameters and literals",
                l.value,
            );
        }
    }
    // Guards: monotone in facts; every non-fact part is a constant computation.
    if let Some(g) = rule.guard {
        check_guard(rule, g, false, &sp)?;
    }
    Ok(())
}

fn check_guard(
    rule: &Rule,
    n: NodeId,
    negated: bool,
    sp: &dyn Fn(NodeId) -> (usize, usize),
) -> R<()> {
    let e = |code, msg: &str| Err(Diagnostic::error(code, msg, sp(n)));
    match rule.nodes[n as usize] {
        RNode::And(a, b) | RNode::Or(a, b) => {
            check_guard(rule, a, negated, sp)?;
            check_guard(rule, b, negated, sp)
        }
        RNode::Not(a) => check_guard(rule, a, !negated, sp),
        RNode::Fact(p, x, m) => {
            if negated {
                return e(
                    "BW0106",
                    "a fact predicate cannot be negated: facts only prove, they never refute",
                );
            }
            if p == FactPred::Proves {
                let RNode::Cmp(_, a, b) = rule.nodes[x as usize] else {
                    return e("BW0104", "`proves` takes a comparison");
                };
                for o in [a, b] {
                    if !matches!(
                        rule.nodes[o as usize],
                        RNode::Param(_) | RNode::Let(_) | RNode::Lit(_)
                    ) {
                        return Err(Diagnostic::error(
                            "BW0104",
                            "`proves` compares parameters, lets and literals only",
                            sp(o),
                        ));
                    }
                }
                return Ok(());
            }
            if !matches!(rule.nodes[x as usize], RNode::Param(_)) {
                return Err(Diagnostic::error(
                    "BW0104",
                    "a fact predicate's first argument must be a parameter",
                    sp(x),
                ));
            }
            if p == FactPred::Disjoint {
                if let Some(y) = m
                    && !matches!(rule.nodes[y as usize], RNode::Param(_))
                {
                    return Err(Diagnostic::error(
                        "BW0104",
                        "`disjoint` takes two parameters",
                        sp(y),
                    ));
                }
                return Ok(());
            }
            if let Some(m) = m
                && !is_pure(rule, m)
            {
                return Err(Diagnostic::error(
                    "BW0105",
                    "the mask must be a constant computation",
                    sp(m),
                ));
            }
            Ok(())
        }
        RNode::ConstP(_, a) => {
            if is_pure(rule, a) {
                Ok(())
            } else {
                e(
                    "BW0105",
                    "this predicate needs a constant; use a fact predicate for other values",
                )
            }
        }
        _ => {
            let is_bit = matches!(&rule.sorts[n as usize], Sort::Bv(w) if w.as_konst() == Some(1));
            if !is_bit {
                return e("BW0101", "a guard must be a condition or a 1-bit value");
            }
            if is_pure(rule, n) {
                Ok(())
            } else {
                e(
                    "BW0105",
                    "this condition depends on a non-constant parameter; state it with `proves(...)`",
                )
            }
        }
    }
}

/// The content hash: kind, constraints, parameter kinds and widths, and the node structure,
/// with parameters renumbered by first occurrence in the pattern (names never matter).
fn rule_id(rule: &Rule) -> RuleId {
    let mut order: Vec<u16> = Vec::new();
    walk(rule, rule.lhs, |n| {
        if let RNode::Param(i) = rule.nodes[n as usize]
            && !order.contains(&i)
        {
            order.push(i);
        }
    });
    let renum = |i: u16| order.iter().position(|&x| x == i).unwrap_or(usize::MAX) as u64;
    let mut hs = [0x6269_7477_7269_6768u64, 0x0072_756c_6573_0001u64];
    let mut feed = |v: u64| {
        hs[0] = combine(hs[0], v);
        hs[1] = combine(hs[1] ^ 0x5555_5555_5555_5555, v.rotate_left(17));
    };
    let wexpr = |feed: &mut dyn FnMut(u64), w: &WExpr| {
        feed(w.konst as u64);
        for &(v, c) in &w.terms {
            feed(u64::from(v));
            feed(c as u64);
        }
    };
    feed(rule.kind as u64);
    feed(rule.width_vars.len() as u64);
    if !rule.modes.is_empty() {
        feed(0x6d6f_6465 + rule.modes.len() as u64);
    }
    for c in &rule.constraints {
        match c {
            WCons::Cmp(a, op, b) => {
                feed(1);
                wexpr(&mut feed, a);
                feed(*op as u64);
                wexpr(&mut feed, b);
            }
            WCons::Mod(a, m, r) => {
                feed(2);
                wexpr(&mut feed, a);
                feed(u64::from(*m));
                feed(u64::from(*r));
            }
        }
    }
    for &i in &order {
        let p = &rule.params[i as usize];
        feed(p.kind as u64);
        wexpr(&mut feed, &p.width);
    }
    // Every node's sort is part of its meaning (a literal's width decides its value).
    let sort = |feed: &mut dyn FnMut(u64), n: NodeId| match &rule.sorts[n as usize] {
        Sort::Bv(w) => {
            feed(0xb5);
            wexpr(feed, w);
        }
        Sort::Bool => feed(0xb0),
    };
    // Structure of every part, in a fixed traversal.
    let mut roots = vec![rule.lhs, rule.rhs];
    roots.extend(rule.guard);
    roots.extend(rule.lets.iter().map(|l| l.value));
    for r in roots {
        feed(0xfeed);
        let mut stack = vec![r];
        while let Some(n) = stack.pop() {
            let node = &rule.nodes[n as usize];
            match node {
                RNode::Param(i) => {
                    feed(1);
                    feed(renum(*i));
                    sort(&mut feed, n);
                }
                RNode::Let(i) => {
                    feed(2);
                    feed(u64::from(*i));
                    sort(&mut feed, n);
                }
                RNode::Lit(l) => {
                    feed(3);
                    feed(crate::hash::bytes(0, format!("{l:?}").as_bytes()));
                    sort(&mut feed, n);
                }
                other => {
                    feed(crate::hash::bytes(
                        4,
                        format!("{:?}", std::mem::discriminant(other)).as_bytes(),
                    ));
                    feed(crate::hash::bytes(
                        5,
                        format!("{other:?}")
                            .split('(')
                            .next()
                            .unwrap_or("")
                            .as_bytes(),
                    ));
                    match other {
                        RNode::Un(op, _) => feed(*op as u64),
                        RNode::Bin(op, ..) => feed(*op as u64),
                        RNode::Cmp(op, ..) => feed(*op as u64),
                        RNode::Extract(lo, _) => wexpr(&mut feed, lo),
                        RNode::Fact(p, ..) => feed(*p as u64),
                        RNode::ConstP(p, _) => feed(*p as u64),
                        RNode::Fp(f) => {
                            feed(crate::hash::bytes(
                                6,
                                format!("{:?} {:?}", f.kind, f.rounding).as_bytes(),
                            ));
                            wexpr(&mut feed, &f.eb);
                            wexpr(&mut feed, &f.sb);
                            if let Some((e, s)) = &f.to {
                                wexpr(&mut feed, e);
                                wexpr(&mut feed, s);
                            }
                        }
                        _ => {}
                    }
                    sort(&mut feed, n);
                }
            }
            push_children(node, &mut stack);
        }
    }
    RuleId(hs)
}

/// The floating-point constant `fp.<name>` names.
fn float_lit(name: &str) -> Option<FloatLit> {
    Some(match name {
        "zero" => FloatLit::Zero,
        "nzero" => FloatLit::NegZero,
        "inf" => FloatLit::Inf,
        "ninf" => FloatLit::NegInf,
        "nan" => FloatLit::Nan,
        "one" => FloatLit::One,
        "none" => FloatLit::NegOne,
        "two" => FloatLit::Two,
        "half" => FloatLit::Half,
        "min_normal" => FloatLit::MinNormal,
        "min_subnormal" => FloatLit::MinSubnormal,
        "max" => FloatLit::MaxFinite,
        _ => return None,
    })
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

/// Compiles a rule program. Returns the rules and groups, plus warnings and notes.
pub(crate) fn compile(src: &str, limits: &CompileLimits) -> Result<Compiled, CompileError> {
    let fail = |d: Diagnostic| CompileError {
        diagnostics: vec![d],
    };
    if src.len() > limits.max_source {
        return Err(fail(Diagnostic::error(
            "BW0100",
            "source too large",
            (0, 0),
        )));
    }
    let toks = lex_mode(src, true)
        .map_err(|e| fail(Diagnostic::error("BW0001", e.message, (e.start, e.end))))?;
    let mut p = Parser {
        src,
        toks,
        pos: 0,
        diags: Vec::new(),
        limits: limits.clone(),
        wdepth: 0,
        work: 0,
    };
    // Header: `bitwright 1;`
    let header_ok = p.is_ident("bitwright") && matches!(p.peek2(), Tok::Int(d, 10) if d == "1");
    if !header_ok {
        return Err(fail(Diagnostic::error(
            "BW0003",
            "a rule file starts with `bitwright 1;`",
            p.span(),
        )));
    }
    p.bump();
    p.bump();
    p.expect(Tok::Semi, "`;`").map_err(fail)?;
    let mut groups: Vec<Group> = Vec::new();
    let mut rules: Vec<Rule> = Vec::new();
    let mut names: HashMap<String, (usize, usize)> = HashMap::new();
    while *p.peek() != Tok::Eof {
        if p.diags.len() >= limits.max_diagnostics {
            p.diags.push(Diagnostic::error(
                "BW0100",
                "too many errors; stopping",
                p.span(),
            ));
            break;
        }
        if matches!(p.peek(), Tok::AttrOpen | Tok::Doc(_)) {
            let sp = p.span();
            if let Err(d) = p.attrs() {
                p.diags.push(d);
            }
            if !matches!(p.peek(), Tok::Eof) && !p.is_ident("group") {
                continue;
            }
            p.diags.push(Diagnostic::error(
                "BW0002",
                "attributes and doc comments belong on rules, not groups",
                sp,
            ));
            continue;
        }
        if !p.is_ident("group") {
            let d = Diagnostic::error("BW0001", "expected `group`", p.span());
            p.diags.push(d);
            // Skip to the next `group`, so junk yields one diagnostic, not one per token.
            p.bump();
            while *p.peek() != Tok::Eof && !p.is_ident("group") {
                p.bump();
            }
            continue;
        }
        p.bump();
        let (gname, gsp) = match p.ident("a group name") {
            Ok(x) => x,
            Err(d) => {
                p.diags.push(d);
                continue;
            }
        };
        if groups.iter().any(|g| g.name == gname) {
            p.diags.push(Diagnostic::error(
                "BW0004",
                format!("group `{gname}` is defined twice"),
                gsp,
            ));
        }
        if let Err(d) = p.expect(Tok::LBrace, "`{`") {
            p.diags.push(d);
            continue;
        }
        let gi = groups.len();
        groups.push(Group {
            name: gname.clone(),
            rules: Vec::new(),
        });
        while *p.peek() != Tok::RBrace && *p.peek() != Tok::Eof {
            if p.diags.len() >= limits.max_diagnostics {
                break;
            }
            if rules.len() >= limits.max_rules {
                p.diags
                    .push(Diagnostic::error("BW0100", "too many rules", p.span()));
                break;
            }
            match p.rule(gi, &gname) {
                Ok((rule, allows)) => {
                    if let Some(prev) = names.insert(rule.name.clone(), rule.span) {
                        let _ = prev;
                        p.diags.push(Diagnostic::error(
                            "BW0004",
                            format!("rule `{}` is defined twice", rule.name),
                            rule.span,
                        ));
                    }
                    if rule.kind == RuleKind::Rewrite && !rule.decreasing {
                        p.diags.push(Diagnostic::error(
                            "BW0302",
                            "this rule does not decrease the termination order (it could loop); \
                             make the result smaller or declare an `identity`",
                            rule.span,
                        ));
                    }
                    if rule.kind == RuleKind::Identity && !rule.decreasing {
                        p.diags.push(Diagnostic::note_level(
                            "BW0409",
                            "this identity does not decrease the termination order: search only",
                            rule.span,
                        ));
                    }
                    if !allows.iter().any(|a| a == "BW0402")
                        && !super::matcher::pattern_reachable(&rule)
                    {
                        p.diags.push(Diagnostic::warning(
                            "BW0402",
                            "this pattern never matches: the builder always rewrites it first \
                             (constants go on the right, `x - c` becomes `x + -c`, …)",
                            rule.span,
                        ));
                    }
                    if rule.examples.is_empty() && !allows.iter().any(|a| a == "BW0407") {
                        p.diags
                            .push(Diagnostic::note_level("BW0407", "no #[example]", rule.span));
                    }
                    groups[gi].rules.push(rules.len());
                    rules.push(rule);
                }
                Err((d, finished)) => {
                    p.diags.push(d);
                    if !finished {
                        p.recover();
                    }
                }
            }
        }
        if let Err(d) = p.expect(Tok::RBrace, "`}`") {
            p.diags.push(d);
        }
    }
    let _ = p.src;
    if p.diags.iter().any(|d| d.level == Level::Error) {
        return Err(CompileError {
            diagnostics: p.diags,
        });
    }
    Ok((groups, rules, p.diags))
}

/// The widths each width variable ranges over in compile-time validation and the checker:
/// every width for one variable; for two, every width to 64 plus boundary widths above; for
/// three, every width to 16 plus boundary widths. Validation is a diagnostic aid: the matcher
/// independently refuses any assignment at which the rule is not well formed.
fn width_domain(vars: usize) -> Vec<u16> {
    const WIDE: &[u16] = &[
        24, 31, 32, 33, 48, 63, 64, 65, 96, 127, 128, 129, 192, 255, 256, 257, 384, 511, 512,
    ];
    let dense: u16 = match vars {
        0 | 1 => 512,
        2 => 64,
        _ => 16,
    };
    let mut d: Vec<u16> = (1..=dense).collect();
    d.extend(WIDE.iter().copied().filter(|&w| w > dense));
    d
}

/// The width assignments of the rule's variables over [`width_domain`] that satisfy the
/// constraints, each with every assignment of its rounding-mode variables after the widths.
#[cfg_attr(not(feature = "check"), allow(dead_code))] // the checker's
pub(crate) fn width_assignments(rule: &Rule) -> Vec<Vec<u16>> {
    let mut out = Vec::new();
    for_each_assignment(rule, |ws| {
        out.push(ws.to_vec());
        true
    });
    out
}

/// Calls `f` on each of [`width_assignments`] in turn, without collecting them, until it
/// returns `false`.
pub(crate) fn for_each_assignment(rule: &Rule, mut f: impl FnMut(&[u16]) -> bool) {
    let n = rule.width_vars.len();
    let m = rule.modes.len();
    let domain = width_domain(n);
    let mut idx = vec![0usize; n];
    let mut cur: Vec<u16> = vec![0; n + m];
    loop {
        for (c, &i) in cur.iter_mut().zip(&idx) {
            *c = domain[i];
        }
        if rule.constraints.iter().all(|c| c.holds(&cur)) {
            // Every mode assignment, as a number in base 5.
            let modes = (RoundingMode::ALL.len() as u32).pow(m as u32);
            for k in 0..modes {
                let mut k = k;
                for slot in &mut cur[n..] {
                    *slot = (k % RoundingMode::ALL.len() as u32) as u16;
                    k /= RoundingMode::ALL.len() as u32;
                }
                if !f(&cur) {
                    return;
                }
            }
        }
        let mut k = 0;
        loop {
            if k == n {
                return;
            }
            if idx[k] + 1 < domain.len() {
                idx[k] += 1;
                break;
            }
            idx[k] = 0;
            k += 1;
        }
    }
}

/// `widths` followed by each assignment of the rule's rounding-mode variables.
#[cfg_attr(not(feature = "check"), allow(dead_code))] // the checker's
pub(crate) fn with_modes(rule: &Rule, widths: Vec<u16>) -> Vec<Vec<u16>> {
    let mut out = vec![widths];
    for _ in &rule.modes {
        out = out
            .into_iter()
            .flat_map(|ws| {
                (0..RoundingMode::ALL.len() as u16).map(move |m| {
                    let mut v = ws.clone();
                    v.push(m);
                    v
                })
            })
            .collect();
    }
    out
}

/// Checks that wherever the pattern can match, the template, guard and lets are well typed
/// (every width in range, extensions widen, extracts fit, literals are representable).
///
/// For a rule with at most one width variable and no rounding-mode variable, also the
/// assignments at which it applies (see `Rule::admitted_widths`): the domain is every width.
fn validate_widths(rule: &Rule, spans: &[(usize, usize)]) -> R<Option<Box<[u64; 9]>>> {
    use super::eval::well_formed_with;
    let mut stack = Vec::new();
    let mut well_formed =
        |root, ws: &[u16], strict| well_formed_with(rule, root, ws, strict, &mut stack);
    let mut matchable = 0usize;
    let mut admitted =
        (rule.width_vars.len() <= 1 && rule.modes.is_empty()).then(|| Box::new([0u64; 9]));
    let mut parts = vec![rule.rhs];
    parts.extend(rule.guard);
    parts.extend(rule.lets.iter().map(|l| l.value));
    let mut failure = None;
    for_each_assignment(rule, |ws| {
        if well_formed(rule.lhs, ws, true).is_err() {
            return true;
        }
        matchable += 1;
        if let Some(bits) = admitted.as_mut() {
            let i = usize::from(ws.first().copied().unwrap_or(0));
            bits[i / 64] |= 1 << (i % 64);
        }
        for &p in &parts {
            if let Err(bad) = well_formed(p, ws, false) {
                let inst: Vec<String> = rule
                    .width_vars
                    .iter()
                    .zip(ws)
                    .map(|(n, w)| format!("{n} = {w}"))
                    .collect();
                failure = Some(Diagnostic::error(
                    "BW0107",
                    format!(
                        "ill-typed where the pattern matches ({}); add a `where` constraint",
                        inst.join(", ")
                    ),
                    spans[bad as usize],
                ));
                return false;
            }
        }
        true
    });
    if let Some(d) = failure {
        return Err(d);
    }
    if matchable == 0 {
        return Err(Diagnostic::error(
            "BW0107",
            "the pattern can never match at any width",
            spans[rule.lhs as usize],
        ));
    }
    Ok(admitted)
}

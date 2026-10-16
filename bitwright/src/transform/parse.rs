//! What both syntaxes share: types, operands, instructions, and (in the transformation syntax)
//! constant expressions and preconditions.

use std::collections::HashMap;

use super::ir::{
    CFun, FPred, IPred, Inst, InstAttrs, Intrinsic, Lit, Node, NodeId, Op, PFun, ParamAttrs,
    Transform, Ty, flags, float_type,
};
use super::lex::{Cursor, SyntaxError, Tok};
use super::llvm::fpclass;

/// What an attribute word means for an integer or floating-point value.
#[derive(Copy, Clone, PartialEq, Eq)]
enum Attr {
    /// `noundef`, `range`, `nofpclass`, `returned`: read and modeled.
    Modeled,
    /// No effect on what the value may be: ABI details (`zeroext`, `signext`, `noext`,
    /// `inreg`) and `immarg`.
    Neutral,
    /// A known attribute that may matter (on pointers, mostly) and that bitwright does not
    /// model.
    Other,
}

fn attr_kind(w: &str) -> Option<Attr> {
    Some(match w {
        "noundef" | "range" | "nofpclass" | "returned" => Attr::Modeled,
        "zeroext" | "signext" | "noext" | "inreg" | "immarg" => Attr::Neutral,
        "noalias"
        | "nonnull"
        | "nocapture"
        | "captures"
        | "nofree"
        | "nest"
        | "readnone"
        | "readonly"
        | "writeonly"
        | "writable"
        | "dereferenceable"
        | "dereferenceable_or_null"
        | "align"
        | "alignstack"
        | "allocalign"
        | "allocptr"
        | "byval"
        | "byref"
        | "preallocated"
        | "inalloca"
        | "sret"
        | "elementtype"
        | "swiftself"
        | "swiftasync"
        | "swifterror"
        | "initializes"
        | "dead_on_unwind"
        | "dead_on_return" => Attr::Other,
        _ => return None,
    })
}

/// The attributes at the cursor (of a parameter, a return value, a call's result or one of
/// its arguments): what they declare, and the names of those that may matter but that
/// bitwright does not model. With `known_only` (a value follows: a call's argument), only
/// attribute words are read; otherwise every word up to a type is, unknown ones as attributes
/// that may matter.
pub(crate) fn attributes(
    c: &mut Cursor<'_>,
    known_only: bool,
) -> Result<(ParamAttrs, Vec<String>), SyntaxError> {
    let mut a = ParamAttrs::default();
    let mut other = Vec::new();
    loop {
        match c.peek() {
            Some(Tok::Ident(w)) => {
                let w = w.clone();
                // A type ends the attributes of a return value.
                if type_name(&w).is_some() || w == "void" {
                    break;
                }
                let kind = attr_kind(&w);
                if kind.is_none() && known_only {
                    break;
                }
                c.pos += 1;
                match w.as_str() {
                    "noundef" => a.noundef = true,
                    "returned" => a.returned = true,
                    "range" => {
                        c.expect("(")?;
                        c.word();
                        let lo = signed_num(c)?;
                        c.expect(",")?;
                        let hi = signed_num(c)?;
                        c.expect(")")?;
                        a.range = Some((lo, hi));
                    }
                    "nofpclass" => {
                        c.expect("(")?;
                        while let Some(w) = c.word() {
                            match fpclass::parse(w) {
                                Some(b) => a.nofpclass |= b,
                                None => return c.err(format!("unknown class `{w}` in nofpclass")),
                            }
                        }
                        c.expect(")")?;
                    }
                    _ => {
                        // `align 4`, `dereferenceable(8)`, `byval(i32)`, "": skip arguments.
                        if c.eat("(") {
                            let mut depth = 1;
                            while depth > 0 {
                                match c.next() {
                                    Some(Tok::P("(")) => depth += 1,
                                    Some(Tok::P(")")) => depth -= 1,
                                    None => return c.err("unbalanced parentheses"),
                                    _ => {}
                                }
                            }
                        } else if matches!(c.peek(), Some(Tok::Num(_))) {
                            c.pos += 1;
                        }
                        if kind != Some(Attr::Neutral) {
                            other.push(w);
                        }
                    }
                }
            }
            // String attributes (`"key"="value"`) may matter too.
            Some(Tok::Str(s)) if !known_only => {
                let s = s.clone();
                c.pos += 1;
                if c.eat("=") {
                    c.next();
                }
                other.push(format!("\"{s}\""));
            }
            Some(Tok::P("#")) if !known_only => {
                c.pos += 1;
                c.next();
            }
            _ => break,
        }
    }
    Ok((a, other))
}

pub(crate) fn signed_num(c: &mut Cursor<'_>) -> Result<String, SyntaxError> {
    let neg = c.eat("-");
    match c.next() {
        Some(Tok::Num(s)) => Ok(if neg { format!("-{s}") } else { s.clone() }),
        Some(Tok::Ident(w)) if w == "true" => Ok("1".into()),
        Some(Tok::Ident(w)) if w == "false" => Ok("0".into()),
        _ => c.err("expected a number"),
    }
}

/// Metadata that says nothing about the values an instruction computes (debug information,
/// profiles, aliasing of memory, which the verifier refuses anyway).
fn harmless_metadata(kind: &str) -> bool {
    matches!(
        kind,
        "dbg"
            | "prof"
            | "annotation"
            | "unpredictable"
            | "llvm.loop"
            | "nosanitize"
            | "tbaa"
            | "tbaa.struct"
            | "alias.scope"
            | "noalias"
            | "DIAssignID"
            | "heapallocsite"
            | "pcsections"
            | "srcloc"
    )
}

/// A type name (`i8`, `float`, …).
pub(crate) fn type_name(w: &str) -> Option<Ty> {
    // Pointers are 64-bit addresses (lifting reads memory as one flat array of bytes).
    if w == "ptr" {
        return Some(Ty::Int(64));
    }
    if let Some(n) = w.strip_prefix('i')
        && !n.is_empty()
        && n.bytes().all(|b| b.is_ascii_digit())
    {
        let bits: u32 = n.parse().ok()?;
        return (1..=crate::Width::MAX_BITS as u32)
            .contains(&bits)
            .then_some(Ty::Int(bits as u16));
    }
    float_type(w).map(Ty::Float)
}

/// `, align N` after a memory instruction.
fn skip_align(c: &mut Cursor<'_>) {
    if matches!(c.peek(), Some(Tok::P(",")))
        && matches!(c.peek_at(1), Some(Tok::Ident(w)) if w == "align")
    {
        c.pos += 3;
    }
}

/// The words that are not symbolic constants in an operand.
const KEYWORDS: &[&str] = &[
    "true",
    "false",
    "poison",
    "undef",
    "inf",
    "nan",
    "zeroinitializer",
    "to",
    "label",
    "void",
];

/// The parser state of one transformation or function pair.
pub(crate) struct Ctx<'a> {
    pub(crate) t: &'a mut Transform,
    /// Registers in scope.
    pub(crate) names: HashMap<String, NodeId>,
    /// Symbolic constants.
    pub(crate) syms: HashMap<String, NodeId>,
    /// The transformation syntax: undefined registers are inputs, operands may be constant
    /// expressions, words are symbolic constants.
    pub(crate) alive: bool,
    /// Block labels (the function syntax).
    pub(crate) blocks: HashMap<String, usize>,
    pub(crate) expression_depth: usize,
}

impl Ctx<'_> {
    /// Annotates node `n` with type `ty`.
    pub(crate) fn annotate(
        &mut self,
        c: &Cursor<'_>,
        n: NodeId,
        ty: Ty,
    ) -> Result<(), SyntaxError> {
        match self.t.types[n as usize] {
            Some(old) if old != ty => c.err(format!(
                "{} is {old} here and {ty} elsewhere",
                self.t.label(n)
            )),
            _ => {
                self.t.types[n as usize] = Some(ty);
                Ok(())
            }
        }
    }

    /// An optional type.
    pub(crate) fn opt_type(&mut self, c: &mut Cursor<'_>) -> Option<Ty> {
        let w = c.peek_word()?;
        let ty = type_name(w)?;
        if w == "ptr" {
            self.t.pointers = true;
        }
        c.pos += 1;
        Some(ty)
    }

    /// A type, after `to`.
    fn type_after_to(&mut self, c: &mut Cursor<'_>) -> Result<Ty, SyntaxError> {
        match self.opt_type(c) {
            Some(ty) => Ok(ty),
            None => c.err("expected a type after `to`"),
        }
    }

    fn lit(&mut self, l: Lit) -> NodeId {
        self.t.push(Node::Lit(l), None)
    }

    /// A register by name: in scope, or (transformations) a new input.
    pub(crate) fn register(&mut self, c: &Cursor<'_>, name: &str) -> Result<NodeId, SyntaxError> {
        if let Some(&n) = self.names.get(name) {
            return Ok(n);
        }
        if !self.alive {
            return c.err(format!("%{name} is not defined"));
        }
        let n = self.t.push(
            Node::Input {
                name: name.to_string(),
                noundef: false,
                range: None,
            },
            None,
        );
        self.t.inputs.push(n);
        self.names.insert(name.to_string(), n);
        Ok(n)
    }

    /// An operand: an optional type, then a value (in the transformation syntax, a constant
    /// expression).
    pub(crate) fn operand(&mut self, c: &mut Cursor<'_>) -> Result<NodeId, SyntaxError> {
        let ty = self.opt_type(c);
        let n = if self.alive {
            self.cexpr(c, 0)?
        } else {
            self.simple(c)?
        };
        if let Some(ty) = ty {
            self.annotate(c, n, ty)?;
        }
        Ok(n)
    }

    /// A register or a literal.
    fn simple(&mut self, c: &mut Cursor<'_>) -> Result<NodeId, SyntaxError> {
        let t = c.next().cloned();
        Ok(match t {
            Some(Tok::Local(name)) => self.register(c, &name)?,
            Some(Tok::Num(s)) => self.lit(Lit::Num(s)),
            Some(Tok::P("-")) => match c.next() {
                Some(Tok::Num(s)) => self.lit(Lit::Num(format!("-{s}"))),
                Some(Tok::Ident(w)) if w == "inf" => self.lit(Lit::Inf(true)),
                _ => return c.err("expected a number after `-`"),
            },
            Some(Tok::Ident(w)) => match w.as_str() {
                "true" => self.lit(Lit::Bool(true)),
                "false" => self.lit(Lit::Bool(false)),
                "poison" => self.lit(Lit::Poison),
                "undef" => self.lit(Lit::Undef),
                "inf" => self.lit(Lit::Inf(false)),
                "nan" => self.lit(Lit::Nan),
                "zeroinitializer" | "null" => self.lit(Lit::Num("0".into())),
                _ if self.alive && !KEYWORDS.contains(&w.as_str()) => self.sym(&w),
                _ => return c.err(format!("unexpected `{w}`")),
            },
            Some(t) => return c.err(format!("unexpected `{t}`")),
            None => return c.err("expected an operand"),
        })
    }

    /// The symbolic constant named `w`.
    pub(crate) fn sym(&mut self, w: &str) -> NodeId {
        if let Some(&n) = self.syms.get(w) {
            return n;
        }
        let n = self.t.push(Node::Sym(w.to_string()), None);
        self.t.consts.push(n);
        self.syms.insert(w.to_string(), n);
        n
    }

    /// A constant expression or precondition, by precedence climbing (`min` is the lowest
    /// level allowed: 0 for anything).
    pub(crate) fn cexpr(&mut self, c: &mut Cursor<'_>, min: u8) -> Result<NodeId, SyntaxError> {
        self.nested(c, |cx, c| cx.cexpr_inner(c, min))
    }

    fn nested(
        &mut self,
        c: &mut Cursor<'_>,
        f: impl FnOnce(&mut Self, &mut Cursor<'_>) -> Result<NodeId, SyntaxError>,
    ) -> Result<NodeId, SyntaxError> {
        if self.expression_depth >= 128 {
            return c.err("constant expression nested too deeply");
        }
        self.expression_depth += 1;
        let result = f(self, c);
        self.expression_depth -= 1;
        result
    }

    fn cexpr_inner(&mut self, c: &mut Cursor<'_>, min: u8) -> Result<NodeId, SyntaxError> {
        let mut lhs = self.unary(c)?;
        loop {
            let Some(Tok::P(p)) = c.peek() else {
                // `%u` in operator position is unsigned remainder.
                if let Some(Tok::Local(u)) = c.peek()
                    && u == "u"
                    && min <= 9
                {
                    c.pos += 1;
                    let rhs = self.cexpr(c, 10)?;
                    lhs = self.t.push(Node::CExpr(CFun::URem, vec![lhs, rhs]), None);
                    continue;
                }
                break;
            };
            let (level, kind): (u8, Bin) = match *p {
                "||" => (1, Bin::P(PFun::Or)),
                "&&" => (2, Bin::P(PFun::And)),
                "==" => (3, Bin::P(PFun::Cmp(IPred::Eq))),
                "!=" => (3, Bin::P(PFun::Cmp(IPred::Ne))),
                "<" => (3, Bin::P(PFun::Cmp(IPred::Slt))),
                "<=" => (3, Bin::P(PFun::Cmp(IPred::Sle))),
                ">" => (3, Bin::P(PFun::Cmp(IPred::Sgt))),
                ">=" => (3, Bin::P(PFun::Cmp(IPred::Sge))),
                "u<" => (3, Bin::P(PFun::Cmp(IPred::Ult))),
                "u<=" => (3, Bin::P(PFun::Cmp(IPred::Ule))),
                "u>" => (3, Bin::P(PFun::Cmp(IPred::Ugt))),
                "u>=" => (3, Bin::P(PFun::Cmp(IPred::Uge))),
                "|" => (4, Bin::C(CFun::Or)),
                "^" => (5, Bin::C(CFun::Xor)),
                "&" => (6, Bin::C(CFun::And)),
                "<<" => (7, Bin::C(CFun::Shl)),
                ">>" => (7, Bin::C(CFun::AShr)),
                "u>>" => (7, Bin::C(CFun::LShr)),
                "+" => (8, Bin::C(CFun::Add)),
                "-" => (8, Bin::C(CFun::Sub)),
                "*" => (9, Bin::C(CFun::Mul)),
                "/" => (9, Bin::C(CFun::SDiv)),
                "/u" => (9, Bin::C(CFun::UDiv)),
                "%" => (9, Bin::C(CFun::SRem)),
                _ => break,
            };
            if level < min {
                break;
            }
            c.pos += 1;
            let rhs = self.cexpr(c, level + 1)?;
            lhs = match kind {
                Bin::C(f) => self.t.push(Node::CExpr(f, vec![lhs, rhs]), None),
                Bin::P(f) => self.t.push(Node::Pred(f, vec![lhs, rhs]), None),
            };
        }
        Ok(lhs)
    }

    fn unary(&mut self, c: &mut Cursor<'_>) -> Result<NodeId, SyntaxError> {
        self.nested(c, |cx, c| cx.unary_inner(c))
    }

    fn unary_inner(&mut self, c: &mut Cursor<'_>) -> Result<NodeId, SyntaxError> {
        match c.peek() {
            Some(Tok::P("-")) => {
                // A negative number is a literal.
                if let Some(Tok::Num(s)) = c.peek_at(1) {
                    let s = s.clone();
                    c.pos += 2;
                    return Ok(self.lit(Lit::Num(format!("-{s}"))));
                }
                c.pos += 1;
                let a = self.unary(c)?;
                Ok(self.t.push(Node::CExpr(CFun::Neg, vec![a]), None))
            }
            Some(Tok::P("~")) => {
                c.pos += 1;
                let a = self.unary(c)?;
                Ok(self.t.push(Node::CExpr(CFun::Not, vec![a]), None))
            }
            Some(Tok::P("!")) => {
                c.pos += 1;
                let a = self.unary(c)?;
                Ok(self.t.push(Node::Pred(PFun::Not, vec![a]), None))
            }
            Some(Tok::P("(")) => {
                c.pos += 1;
                let e = self.cexpr(c, 0)?;
                c.expect(")")?;
                Ok(e)
            }
            Some(Tok::Ident(w)) if matches!(c.peek_at(1), Some(Tok::P("("))) => {
                let w = w.clone();
                c.pos += 2;
                let mut args = Vec::new();
                if !c.eat(")") {
                    loop {
                        args.push(self.cexpr(c, 0)?);
                        if c.eat(")") {
                            break;
                        }
                        c.expect(",")?;
                    }
                }
                if let Some((p, arity)) = PFun::function(&w) {
                    if args.len() != arity {
                        return c.err(format!("{w} takes {arity} arguments"));
                    }
                    return Ok(self.t.push(Node::Pred(p, args), None));
                }
                let (f, arity) = match w.as_str() {
                    "abs" => (CFun::Abs, 1),
                    "log2" => (CFun::Log2, 1),
                    "width" => (CFun::Width, 1),
                    "trunc" => (CFun::Trunc, 1),
                    "zext" => (CFun::ZExt, 1),
                    "sext" => (CFun::SExt, 1),
                    "umax" => (CFun::UMax, 2),
                    "umin" => (CFun::UMin, 2),
                    "smax" => (CFun::SMax, 2),
                    "smin" => (CFun::SMin, 2),
                    "countLeadingZeros" | "ctlz" => (CFun::Clz, 1),
                    "countTrailingZeros" | "cttz" => (CFun::Ctz, 1),
                    "popcount" | "ctpop" => (CFun::Popcount, 1),
                    "udiv" => (CFun::UDiv, 2),
                    "urem" => (CFun::URem, 2),
                    "sdiv" => (CFun::SDiv, 2),
                    "srem" => (CFun::SRem, 2),
                    _ => return c.err(format!("unknown function `{w}`")),
                };
                if args.len() != arity {
                    return c.err(format!("{w} takes {arity} arguments"));
                }
                Ok(self.t.push(Node::CExpr(f, args), None))
            }
            _ => self.simple(c),
        }
    }

    /// The flags at the cursor.
    pub(crate) fn flags(&self, c: &mut Cursor<'_>) -> u16 {
        let mut f = 0;
        while let Some(w) = c.peek_word() {
            match flags::parse(w) {
                Some(b) => {
                    f |= b;
                    c.pos += 1;
                }
                None => break,
            }
        }
        f
    }

    /// An instruction after `%name =` (or a void call): the operation and its operands, with
    /// the type annotations the syntax gives. Returns the instruction and its result type
    /// annotation.
    pub(crate) fn inst(
        &mut self,
        c: &mut Cursor<'_>,
        name: &str,
    ) -> Result<(Inst, Option<Ty>), SyntaxError> {
        let is_op = c.peek_word().is_some_and(|w| {
            Op::binary(w).is_some()
                || Op::cast(w).is_some()
                || matches!(
                    w,
                    "icmp"
                        | "fcmp"
                        | "select"
                        | "freeze"
                        | "fneg"
                        | "phi"
                        | "call"
                        | "tail"
                        | "musttail"
                        | "notail"
                        | "load"
                        | "store"
                        | "getelementptr"
                        | "alloca"
                        | "ptrtoint"
                        | "inttoptr"
                )
        });
        if !is_op {
            // `%r = <operand>`: a copy (the transformation syntax).
            if !self.alive {
                return match c.peek_word() {
                    Some(w) => c.err(format!("unknown instruction `{w}`")),
                    None => c.err("expected an instruction"),
                };
            }
            let a = self.operand(c)?;
            let mut inst = Inst::new(name, Op::Copy);
            inst.args = vec![a];
            return Ok((inst, None));
        }
        let opname = c.word().expect("checked");
        let mut result_ty = None;
        let mut inst = Inst::new(name, Op::Freeze);
        let mut attrs = InstAttrs::default();
        if let Some(op) = Op::binary(opname) {
            inst.op = op;
            inst.flags = self.flags(c);
            let a = self.operand(c)?;
            c.expect(",")?;
            let b = self.operand(c)?;
            inst.args = vec![a, b];
        } else if let Some(op) = Op::cast(opname) {
            inst.op = op;
            inst.flags = self.flags(c);
            let a = self.operand(c)?;
            if c.eat_word("to") {
                result_ty = Some(self.type_after_to(c)?);
            }
            inst.args = vec![a];
        } else {
            match opname {
                "icmp" => {
                    inst.flags = self.flags(c);
                    let Some(p) = c.word().and_then(IPred::parse) else {
                        return c.err("expected an integer comparison (eq, ult, …)");
                    };
                    inst.op = Op::ICmp(p);
                    let a = self.operand(c)?;
                    c.expect(",")?;
                    let b = self.operand(c)?;
                    inst.args = vec![a, b];
                    result_ty = Some(Ty::Int(1));
                }
                "fcmp" => {
                    inst.flags = self.flags(c);
                    let Some(p) = c.word().and_then(FPred::parse) else {
                        return c.err("expected a floating-point comparison (oeq, ult, …)");
                    };
                    inst.op = Op::FCmp(p);
                    let a = self.operand(c)?;
                    c.expect(",")?;
                    let b = self.operand(c)?;
                    inst.args = vec![a, b];
                    result_ty = Some(Ty::Int(1));
                }
                "select" => {
                    inst.op = Op::Select;
                    inst.flags = self.flags(c);
                    let cnd = self.operand(c)?;
                    c.expect(",")?;
                    let a = self.operand(c)?;
                    c.expect(",")?;
                    let b = self.operand(c)?;
                    inst.args = vec![cnd, a, b];
                    self.annotate(c, cnd, Ty::Int(1))?;
                }
                "load" => {
                    // load [volatile] <ty>, ptr %p [, align N]
                    self.t.pointers = true;
                    c.eat_word("volatile");
                    inst.op = Op::Load;
                    let Some(ty) = self.opt_type(c) else {
                        return c.err("expected the loaded type");
                    };
                    result_ty = Some(ty);
                    c.expect(",")?;
                    let p = self.operand(c)?;
                    inst.args = vec![p];
                    skip_align(c);
                }
                "store" => {
                    // store [volatile] <ty> %v, ptr %p [, align N]
                    self.t.pointers = true;
                    c.eat_word("volatile");
                    inst.op = Op::Store;
                    let v = self.operand(c)?;
                    c.expect(",")?;
                    let p = self.operand(c)?;
                    inst.args = vec![v, p];
                    result_ty = Some(Ty::Int(1));
                    skip_align(c);
                }
                "alloca" => {
                    self.t.pointers = true;
                    inst.op = Op::Alloca;
                    if self.opt_type(c).is_none() {
                        return c.err("expected the allocated type");
                    }
                    result_ty = Some(Ty::Int(64));
                    skip_align(c);
                }
                "getelementptr" => {
                    // getelementptr [inbounds|nuw|nusw]* <elem>, ptr %p, <ty> %i (their
                    // poison is not modeled: only lifting reads memory)
                    self.t.pointers = true;
                    while matches!(c.peek_word(), Some("inbounds" | "nuw" | "nusw")) {
                        c.pos += 1;
                    }
                    let Some(elem) = self.opt_type(c) else {
                        return c.err("getelementptr over a scalar type (i8, i32, …)");
                    };
                    c.expect(",")?;
                    let p = self.operand(c)?;
                    c.expect(",")?;
                    let i = self.operand(c)?;
                    inst.op = Op::Gep(elem.bits().div_ceil(8));
                    inst.args = vec![p, i];
                    result_ty = Some(Ty::Int(64));
                }
                "ptrtoint" | "inttoptr" => {
                    // A resize of the address: zero extension or truncation.
                    self.t.pointers = true;
                    let a = self.operand(c)?;
                    if !c.eat_word("to") {
                        return c.err("expected `to`");
                    }
                    let ty = self.type_after_to(c)?;
                    inst.op = Op::Resize;
                    inst.args = vec![a];
                    result_ty = Some(ty);
                }
                "freeze" | "fneg" => {
                    inst.op = if opname == "freeze" {
                        Op::Freeze
                    } else {
                        Op::FNeg
                    };
                    inst.flags = self.flags(c);
                    let a = self.operand(c)?;
                    inst.args = vec![a];
                    if inst.op == Op::FNeg {}
                }
                "phi" => {
                    inst.op = Op::Phi;
                    inst.flags = self.flags(c);
                    result_ty = self.opt_type(c);
                    loop {
                        c.expect("[")?;
                        let v = self.operand(c)?;
                        c.expect(",")?;
                        let Some(Tok::Local(b)) = c.next() else {
                            return c.err("expected a block label in a phi");
                        };
                        let Some(&bi) = self.blocks.get(b.as_str()) else {
                            return c.err(format!("unknown block %{b}"));
                        };
                        c.expect("]")?;
                        inst.args.push(v);
                        inst.incoming.push(bi);
                        if !c.eat(",") {
                            break;
                        }
                    }
                }
                "call" | "tail" | "musttail" | "notail" => {
                    if opname != "call" && !c.eat_word("call") {
                        return c.err("expected `call`");
                    }
                    inst.flags = self.flags(c);
                    // Return attributes and the return type.
                    let (result, other) = attributes(c, false)?;
                    attrs.result = result;
                    attrs.unmodeled.extend(other);
                    let ret = if c.eat_word("void") {
                        None
                    } else {
                        self.opt_type(c)
                    };
                    let Some(Tok::Global(f)) = c.next() else {
                        return c.err("expected a function name after `call`");
                    };
                    let Some(i) = Intrinsic::parse(f) else {
                        return c.err(format!("@{f} is not an intrinsic bitwright knows"));
                    };
                    inst.op = Op::Call(i);
                    c.expect("(")?;
                    if !c.eat(")") {
                        loop {
                            // `ty attrs value`: a type, attributes, then the value (some write
                            // the attributes first).
                            let (mut arg, other) = attributes(c, true)?;
                            attrs.unmodeled.extend(other);
                            let ty = self.opt_type(c);
                            let (after, other) = attributes(c, true)?;
                            attrs.unmodeled.extend(other);
                            arg.noundef |= after.noundef;
                            arg.range = arg.range.or(after.range);
                            arg.nofpclass |= after.nofpclass;
                            if arg.returned || after.returned {
                                attrs.unmodeled.push("`returned` on an argument".into());
                            }
                            let a = if self.alive {
                                self.cexpr(c, 0)?
                            } else {
                                self.simple(c)?
                            };
                            if let Some(ty) = ty {
                                self.annotate(c, a, ty)?;
                            }
                            inst.args.push(a);
                            attrs.args.push(arg);
                            if c.eat(")") {
                                break;
                            }
                            c.expect(",")?;
                        }
                    }
                    if attrs.args.iter().all(ParamAttrs::is_empty) {
                        attrs.args.clear();
                    }
                    if inst.args.len() != i.arity() {
                        return c.err(format!(
                            "@{f} takes {} operands, not {}",
                            i.arity(),
                            inst.args.len()
                        ));
                    }
                    result_ty = ret;
                    match i {
                        Intrinsic::Assume => self.annotate(c, inst.args[0], Ty::Int(1))?,
                        Intrinsic::Abs | Intrinsic::Ctlz | Intrinsic::Cttz => {
                            self.annotate(c, inst.args[1], Ty::Int(1))?;
                        }
                        _ => {}
                    }
                }
                _ => return c.err(format!("unknown instruction `{opname}`")),
            }
        }
        // Metadata and call-site attribute groups: any that may change the result is not
        // modeled (`!fpmath` allows an error, `!range` makes poison, a group may hold
        // `strictfp`).
        for kind in c.trailer()? {
            if !harmless_metadata(&kind) {
                attrs.unmodeled.push(if kind.starts_with('#') {
                    format!("the attribute group {kind}")
                } else {
                    format!("!{kind}")
                });
            }
        }
        if attrs != InstAttrs::default() {
            inst.attrs = Some(Box::new(attrs));
        }
        Ok((inst, result_ty))
    }
}

enum Bin {
    C(CFun),
    P(PFun),
}

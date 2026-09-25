//! What both syntaxes share: types, operands, instructions, and (in the transformation syntax)
//! constant expressions and preconditions.

use std::collections::HashMap;

use super::ir::{
    CFun, FPred, IPred, Inst, Intrinsic, Lit, Node, NodeId, Op, PFun, Transform, Ty, flags,
    float_type,
};
use super::lex::{Cursor, SyntaxError, Tok};

/// A type name (`i8`, `float`, …).
pub(crate) fn type_name(w: &str) -> Option<Ty> {
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
    pub(crate) fn opt_type(&self, c: &mut Cursor<'_>) -> Option<Ty> {
        let ty = c.peek_word().and_then(type_name)?;
        c.pos += 1;
        Some(ty)
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
            let inst = Inst {
                name: name.to_string(),
                op: Op::Copy,
                flags: 0,
                args: vec![a],
                incoming: Vec::new(),
            };
            return Ok((inst, None));
        }
        let opname = c.word().expect("checked");
        let mut result_ty = None;
        let mut inst = Inst {
            name: name.to_string(),
            op: Op::Freeze,
            flags: 0,
            args: Vec::new(),
            incoming: Vec::new(),
        };
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
                match c.word().and_then(type_name) {
                    Some(ty) => result_ty = Some(ty),
                    None => return c.err("expected a type after `to`"),
                }
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
                    while matches!(c.peek_word(), Some("noundef" | "zeroext" | "signext")) {
                        c.pos += 1;
                    }
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
                            while matches!(
                                c.peek_word(),
                                Some("noundef" | "zeroext" | "signext" | "immarg")
                            ) && !matches!(c.peek_at(1), Some(Tok::P(",") | Tok::P(")")))
                            {
                                c.pos += 1;
                            }
                            // `ty attrs value`: a type, attributes, then the value.
                            let ty = self.opt_type(c);
                            while matches!(
                                c.peek_word(),
                                Some("noundef" | "immarg" | "zeroext" | "signext")
                            ) {
                                c.pos += 1;
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
                            if c.eat(")") {
                                break;
                            }
                            c.expect(",")?;
                        }
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
        c.end()?;
        Ok((inst, result_ty))
    }
}

enum Bin {
    C(CFun),
    P(PFun),
}

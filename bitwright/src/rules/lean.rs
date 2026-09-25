//! Rules as Lean 4 theorems over `BitVec`. [`lean`] states each rule for every width:
//!
//! ```text
//! theorem rule_name (W : Nat) (hW : 0 < W) (x y : BitVec (W)) (hg : …) :
//!     lhs = rhs := by
//!   sorry
//! ```
//!
//! with its width variables universally quantified, its `where` constraints and its guard as
//! hypotheses (fact predicates read as what they state about values, as the SMT obligations
//! read them) and its `let`s written out. The checker establishes a rule at the widths it
//! enumerates and samples, and the native prover at the ones it is asked about; a proof of the
//! Lean statement covers every width at once. [`lean`] with `at` states each rule at fixed
//! widths instead, proved by `bv_decide`, whose certificates Lean's kernel checks: an oracle
//! that shares nothing with bitwright.
//!
//! Division follows SMT-LIB (`x / 0` is all ones: `BitVec.smtUDiv`, `BitVec.smtSDiv`), as
//! bitwright's operators do. Operators Lean's core `BitVec` does not have (bit counts, byte
//! swaps, bit reversal, `pdep`, `pext`, floating point) leave the rule out, with a comment
//! saying so.

use core::fmt::Write as _;

use super::RuleProgram;
use super::ir::{
    ConstPred, FactPred, Literal, NodeId, RNode, Rule, RuleKind, Sort, WCmp, WCons, WExpr,
};
use crate::ops::{BinOp, CmpOpExt, UnOp};

/// Words Lean reserves, which an identifier must quote as `«…»`.
const KEYWORDS: &[&str] = &[
    "at",
    "by",
    "do",
    "else",
    "end",
    "fun",
    "from",
    "have",
    "if",
    "in",
    "let",
    "match",
    "mut",
    "open",
    "return",
    "show",
    "then",
    "where",
    "with",
    "theorem",
    "def",
    "namespace",
    "section",
    "variable",
    "universe",
    "import",
    "instance",
    "class",
    "structure",
    "inductive",
    "deriving",
    "private",
    "protected",
    "noncomputable",
    "partial",
    "unsafe",
    "macro",
    "syntax",
    "notation",
    "infix",
    "prefix",
    "postfix",
    "calc",
    "suffices",
    "obtain",
    "for",
    "unless",
    "try",
    "catch",
    "finally",
    "break",
    "continue",
    "Type",
    "Prop",
    "Sort",
    "nomatch",
    "nofun",
    "local",
    "scoped",
    "attribute",
    "example",
    "abbrev",
    "opaque",
    "axiom",
    "mutual",
    "set_option",
    "omit",
    "include",
];

/// A Lean identifier for a name (one component).
fn ident(name: &str) -> String {
    let plain = name
        .chars()
        .next()
        .is_some_and(|c| c.is_alphabetic() || c == '_')
        && name
            .chars()
            .all(|c| c.is_alphanumeric() || c == '_' || c == '\'');
    if plain && !KEYWORDS.contains(&name) {
        name.to_string()
    } else {
        format!("«{}»", name.replace(['«', '»'], "_"))
    }
}

/// A dotted name (a group) as a Lean namespace.
fn namespace(name: &str) -> String {
    name.split('.').map(ident).collect::<Vec<_>>().join(".")
}

/// The short name of a rule (after its group).
fn short_name(rule: &Rule) -> String {
    ident(rule.name.rsplit("::").next().unwrap_or(&rule.name))
}

struct Out<'r> {
    rule: &'r Rule,
    /// Fixed widths, for an instance; `None` states the rule for every width.
    vals: Option<&'r [u16]>,
    unsupported: Option<String>,
}

impl Out<'_> {
    fn no(&mut self, what: &str) -> String {
        if self.unsupported.is_none() {
            self.unsupported = Some(what.to_string());
        }
        "sorry".into()
    }

    /// A width expression: a natural number (`b - c` truncates in Lean, and every width a rule
    /// admits is positive, so each one written here means what the rule means).
    fn wexpr(&self, w: &WExpr) -> String {
        if let Some(vals) = self.vals {
            return w.eval(vals).to_string();
        }
        let (mut pos, mut neg) = (Vec::new(), Vec::new());
        for &(v, c) in &w.terms {
            let name = self
                .rule
                .width_vars
                .get(v as usize)
                .map_or_else(|| format!("V{v}"), |s| ident(s));
            let t = match c.unsigned_abs() {
                1 => name,
                a => format!("{a} * {name}"),
            };
            if c > 0 { pos.push(t) } else { neg.push(t) }
        }
        match w.konst {
            k if k > 0 => pos.push(k.to_string()),
            k if k < 0 => neg.push(k.unsigned_abs().to_string()),
            _ => {}
        }
        let p = if pos.is_empty() {
            "0".to_string()
        } else {
            pos.join(" + ")
        };
        match neg.len() {
            0 => p,
            1 => format!("{p} - {}", neg[0]),
            _ => format!("{p} - ({})", neg.join(" + ")),
        }
    }

    /// The width of a node.
    fn width(&self, n: NodeId) -> String {
        match &self.rule.sorts[n as usize] {
            Sort::Bv(w) => self.wexpr(w),
            Sort::Bool => "1".into(),
        }
    }

    /// A bit-vector term (parenthesized unless it is a name).
    fn term(&mut self, n: NodeId) -> String {
        let rule = self.rule;
        let w = self.width(n);
        match &rule.nodes[n as usize] {
            RNode::Param(i) => ident(&rule.params[*i as usize].name),
            RNode::Let(i) => match rule.lets.get(*i as usize) {
                Some(l) => self.term(l.value),
                None => self.no("a let"),
            },
            RNode::Lit(l) => match l {
                Literal::Int { limbs, negative } => {
                    if limbs.iter().skip(2).any(|&x| x != 0) {
                        return self.no("a literal over 128 bits");
                    }
                    let v = limbs
                        .iter()
                        .take(2)
                        .enumerate()
                        .fold(0u128, |v, (k, &x)| v | (u128::from(x) << (64 * k)));
                    if *negative {
                        format!("(-({v}#({w})))")
                    } else {
                        format!("({v}#({w}))")
                    }
                }
                Literal::Ones => format!("(BitVec.allOnes ({w}))"),
                Literal::SMin => format!("(BitVec.intMin ({w}))"),
                Literal::SMax => format!("(BitVec.intMax ({w}))"),
                Literal::Width(e) => format!("(BitVec.ofNat ({w}) ({}))", self.wexpr(e)),
                Literal::LowMask(e) => {
                    format!("(BitVec.ofNat ({w}) (2 ^ ({}) - 1))", self.wexpr(e))
                }
                Literal::Bit(e) => format!("(BitVec.twoPow ({w}) ({}))", self.wexpr(e)),
                _ => self.no("a floating-point literal"),
            },
            RNode::Un(op, a) => {
                let a = self.term(*a);
                match op {
                    UnOp::Not => format!("(~~~{a})"),
                    UnOp::Neg => format!("(-{a})"),
                    _ => self.no("a bit count, byte swap or bit reversal"),
                }
            }
            RNode::Bin(op, a, b) => {
                let (a, b) = (self.term(*a), self.term(*b));
                match op {
                    BinOp::Add => format!("({a} + {b})"),
                    BinOp::Sub => format!("({a} - {b})"),
                    BinOp::Mul => format!("({a} * {b})"),
                    BinOp::UMulHi => format!(
                        "((({a}.zeroExtend (2 * ({w}))) * ({b}.zeroExtend (2 * ({w})))).extractLsb' ({w}) ({w}))"
                    ),
                    BinOp::SMulHi => format!(
                        "((({a}.signExtend (2 * ({w}))) * ({b}.signExtend (2 * ({w})))).extractLsb' ({w}) ({w}))"
                    ),
                    BinOp::UDiv => format!("({a}.smtUDiv {b})"),
                    BinOp::URem => format!("({a} % {b})"),
                    BinOp::SDiv => format!("({a}.smtSDiv {b})"),
                    BinOp::SRem => format!("({a}.srem {b})"),
                    BinOp::And => format!("({a} &&& {b})"),
                    BinOp::Or => format!("({a} ||| {b})"),
                    BinOp::Xor => format!("({a} ^^^ {b})"),
                    BinOp::Shl => format!("({a} <<< {b})"),
                    BinOp::LShr => format!("({a} >>> {b})"),
                    BinOp::AShr => format!("({a}.sshiftRight' {b})"),
                    BinOp::RotL | BinOp::RotR => self.rotate(*op == BinOp::RotL, &a, &b, &w),
                    _ => self.no("pdep or pext"),
                }
            }
            RNode::Cmp(op, a, b) => {
                let (a, b) = (self.term(*a), self.term(*b));
                let c = match op {
                    CmpOpExt::Eq => format!("({a} == {b})"),
                    CmpOpExt::Ne => format!("({a} != {b})"),
                    CmpOpExt::Ult => format!("({a}.ult {b})"),
                    CmpOpExt::Ule => format!("({a}.ule {b})"),
                    CmpOpExt::Ugt => format!("({b}.ult {a})"),
                    CmpOpExt::Uge => format!("({b}.ule {a})"),
                    CmpOpExt::Slt => format!("({a}.slt {b})"),
                    CmpOpExt::Sle => format!("({a}.sle {b})"),
                    CmpOpExt::Sgt => format!("({b}.slt {a})"),
                    CmpOpExt::Sge => format!("({b}.sle {a})"),
                };
                format!("(BitVec.ofBool {c})")
            }
            RNode::Zext(a) => format!("({}.zeroExtend ({w}))", self.term(*a)),
            RNode::Sext(a) => format!("({}.signExtend ({w}))", self.term(*a)),
            RNode::Extract(lo, a) => {
                let lo = self.wexpr(lo);
                format!("({}.extractLsb' ({lo}) ({w}))", self.term(*a))
            }
            RNode::Concat(h, l) => {
                // `++` has the type `BitVec (a + b)`; the cast states it as the node's width.
                let (h, l) = (self.term(*h), self.term(*l));
                format!("(BitVec.cast (m := {w}) (by omega) ({h} ++ {l}))")
            }
            RNode::Select(c, t, e) => {
                let c = self.cond(*c);
                let (t, e) = (self.term(*t), self.term(*e));
                format!("(if {c} then {t} else {e})")
            }
            RNode::Fp(_) => self.no("floating point"),
            _ => self.no("a condition where a value belongs"),
        }
    }

    /// A rotation of `a` by `b` (left when `left`). At fixed widths it is written with shifts,
    /// which `bv_decide` understands, unlike a rotation by a variable amount:
    /// `rotl(a, b) = a << (b % w) | a >> ((w - b % w) % w)`.
    fn rotate(&self, left: bool, a: &str, b: &str, w: &str) -> String {
        let (l, r) = if left {
            ("rotateLeft", ("<<<", ">>>"))
        } else {
            ("rotateRight", (">>>", "<<<"))
        };
        if self.vals.is_none() {
            return format!("({a}.{l} {b}.toNat)");
        }
        let n = format!("{w}#({w})");
        format!(
            "(({a} {} ({b} % {n})) ||| ({a} {} (({n} - {b} % {n}) % {n})))",
            r.0, r.1
        )
    }

    /// A comparison as a proposition.
    fn cmp(&mut self, op: CmpOpExt, a: NodeId, b: NodeId) -> String {
        let (a, b) = (self.term(a), self.term(b));
        match op {
            CmpOpExt::Eq => format!("{a} = {b}"),
            CmpOpExt::Ne => format!("{a} ≠ {b}"),
            CmpOpExt::Ult => format!("{a} < {b}"),
            CmpOpExt::Ule => format!("{a} ≤ {b}"),
            CmpOpExt::Ugt => format!("{b} < {a}"),
            CmpOpExt::Uge => format!("{b} ≤ {a}"),
            CmpOpExt::Slt => format!("{a}.slt {b} = true"),
            CmpOpExt::Sle => format!("{a}.sle {b} = true"),
            CmpOpExt::Sgt => format!("{b}.slt {a} = true"),
            CmpOpExt::Sge => format!("{b}.sle {a} = true"),
        }
    }

    /// A 1-bit value as a condition.
    fn cond(&mut self, n: NodeId) -> String {
        match self.rule.nodes[n as usize] {
            RNode::Cmp(op, a, b) => format!("({})", self.cmp(op, a, b)),
            _ => format!("({} = 1#1)", self.term(n)),
        }
    }

    /// A guard.
    fn prop(&mut self, n: NodeId) -> String {
        let rule = self.rule;
        match &rule.nodes[n as usize] {
            RNode::And(a, b) => format!("({} ∧ {})", self.prop(*a), self.prop(*b)),
            RNode::Or(a, b) => format!("({} ∨ {})", self.prop(*a), self.prop(*b)),
            RNode::Not(a) => format!("¬{}", self.prop(*a)),
            RNode::Fact(p, x, m) => {
                let w = self.width(*x);
                match (p, m) {
                    (FactPred::Proves, _) => self.cond(*x),
                    (FactPred::NonZero, _) => format!("({} ≠ 0#({w}))", self.term(*x)),
                    (FactPred::ZeroBits | FactPred::Disjoint, Some(m)) => {
                        let (x, m) = (self.term(*x), self.term(*m));
                        format!("({x} &&& {m} = 0#({w}))")
                    }
                    (FactPred::OneBits, Some(m)) => {
                        let (x, m) = (self.term(*x), self.term(*m));
                        format!("({x} &&& {m} = {m})")
                    }
                    _ => self.no("a floating-point guard"),
                }
            }
            RNode::ConstP(p, a) => {
                let c = self.term(*a);
                let w = self.width(*a);
                let z = format!("0#({w})");
                match p {
                    ConstPred::IsPow2 => format!("({c} ≠ {z} ∧ {c} &&& ({c} - 1) = {z})"),
                    ConstPred::IsLowMask => format!("({c} ≠ {z} ∧ {c} &&& ({c} + 1) = {z})"),
                    ConstPred::IsShiftedMask => {
                        let f = format!("({c} ||| ({c} - 1))");
                        format!("({c} ≠ {z} ∧ {f} &&& ({f} + 1) = {z})")
                    }
                }
            }
            _ => self.cond(n),
        }
    }
}

/// The statement of a rule, or why Lean's core `BitVec` cannot state it.
fn statement(rule: &Rule, vals: Option<&[u16]>, proof: &str) -> Result<String, String> {
    let mut o = Out {
        rule,
        vals,
        unsupported: None,
    };
    let lhs = o.term(rule.lhs);
    let rhs = o.term(rule.rhs);
    let guard = rule.guard.map(|g| o.prop(g));
    if let Some(why) = o.unsupported.take() {
        return Err(why);
    }
    if !rule.modes.is_empty() {
        return Err("a rounding mode".into());
    }
    let mut s = String::new();
    if !rule.doc.is_empty() {
        let _ = writeln!(s, "/-- {} -/", rule.doc.trim().replace("-/", "- /"));
    }
    let _ = write!(s, "theorem {}", short_name(rule));
    if vals.is_none() {
        let vars: Vec<String> = rule.width_vars.iter().map(|v| ident(v)).collect();
        if !vars.is_empty() {
            let _ = write!(s, " ({} : Nat)", vars.join(" "));
        }
        // Every width is positive (a bit-vector has at least one bit).
        for v in &vars {
            let _ = write!(s, " (h{} : 0 < {v})", v.trim_matches(['«', '»']));
        }
        for (k, c) in rule.constraints.iter().enumerate() {
            let text = match c {
                WCons::Cmp(a, op, b) => {
                    let (a, b) = (o.wexpr(a), o.wexpr(b));
                    let op = match op {
                        WCmp::Eq => "=",
                        WCmp::Ne => "≠",
                        WCmp::Lt => "<",
                        WCmp::Le => "≤",
                        WCmp::Gt => ">",
                        WCmp::Ge => "≥",
                    };
                    format!("{a} {op} {b}")
                }
                WCons::Mod(a, m, r) => format!("({}) % {m} = {r}", o.wexpr(a)),
            };
            let _ = write!(s, " (hw{k} : {text})");
        }
    }
    // Parameters of one width share a binder.
    let mut k = 0;
    while k < rule.params.len() {
        let w = o.wexpr(&rule.params[k].width);
        let mut names = vec![ident(&rule.params[k].name)];
        while k + names.len() < rule.params.len()
            && o.wexpr(&rule.params[k + names.len()].width) == w
        {
            names.push(ident(&rule.params[k + names.len()].name));
        }
        k += names.len();
        let _ = write!(s, " ({} : BitVec ({w}))", names.join(" "));
    }
    if let Some(g) = guard {
        let _ = write!(s, " (hg : {g})");
    }
    let kind = match rule.kind {
        RuleKind::Identity => " -- an identity",
        _ => "",
    };
    let _ = writeln!(s, " :\n    {lhs} = {rhs} := by{kind}\n  {proof}");
    Ok(s)
}

/// The theorem of one rule for every width, its proof left as `sorry`; or a comment when it
/// uses what Lean's core `BitVec` lacks.
pub fn rule_theorem(rule: &Rule) -> String {
    statement(rule, None, "sorry").unwrap_or_else(|why| {
        format!(
            "-- {}: not stated ({why} has no counterpart in Lean's BitVec)\n",
            rule.name
        )
    })
}

/// The theorem of one rule at fixed widths (`widths` lists a value for each width variable),
/// proved by `bv_decide`; `None` when Lean's core `BitVec` cannot state it.
pub fn rule_instance(rule: &Rule, widths: &[u16]) -> Option<String> {
    if widths.len() != rule.width_vars.len() || !rule.admits(widths) {
        return None;
    }
    statement(rule, Some(widths), "bv_decide").ok()
}

/// The rules of `programs` as one Lean 4 file, a namespace per group. Without `at`, each
/// rule is a theorem for every width whose proof is left to write (`sorry`). With `at`, each
/// rule is a theorem at fixed widths that `bv_decide` proves: the widest assignment the rule
/// admits with every width variable at most `at` (the largest total). Rules Lean's core
/// `BitVec` cannot state, or that admit no such assignment, are left out with a comment.
pub fn lean(programs: &[&RuleProgram], at: Option<u16>) -> String {
    let mut s = match at {
        None => String::from(
            "-- bitwright rules as Lean 4 theorems over BitVec, for every width.\n\
             -- Each proof is `sorry` until written.\n",
        ),
        Some(w) => format!(
            "-- bitwright rules as Lean 4 theorems over BitVec at widths up to {w}, proved by\n\
             -- bv_decide.\n\nimport Std.Tactic.BVDecide\n"
        ),
    };
    for program in programs {
        for g in program.groups() {
            let ns = namespace(&g.name);
            let _ = writeln!(s, "\nnamespace {ns}\n");
            for &i in &g.rules {
                let rule = &program.rules()[i];
                match at {
                    None => s.push_str(&rule_theorem(rule)),
                    Some(width) => s.push_str(&instance_at(rule, width)),
                }
                s.push('\n');
            }
            let _ = writeln!(s, "end {ns}");
        }
    }
    s
}

/// A rule at the widest assignment it admits with every width at most `width`.
fn instance_at(rule: &Rule, width: u16) -> String {
    let best = super::compile::width_assignments(rule)
        .into_iter()
        .filter(|ws| {
            ws.len() == rule.width_vars.len() && ws.iter().all(|&w| w <= width) && rule.admits(ws)
        })
        .max_by_key(|ws| ws.iter().map(|&w| u32::from(w)).sum::<u32>());
    let Some((ws, t)) = best.and_then(|ws| rule_instance(rule, &ws).map(|t| (ws, t))) else {
        return format!("-- {}: not stated\n", rule.name);
    };
    if ws.is_empty() {
        return t;
    }
    let at: Vec<String> = rule
        .width_vars
        .iter()
        .zip(&ws)
        .map(|(v, w)| format!("{v} = {w}"))
        .collect();
    format!("-- at {}\n{t}", at.join(", "))
}

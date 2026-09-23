//! egg (the e-graph library) as a baseline. A dataset's expression is parsed straight into an
//! egg term, saturated with a rule set under egg's default limits, and the smallest term by
//! AST size is extracted.
//!
//! Two rule sets: `bw` is bitwright's own equality-saturation equations (`eqsat.bwr`: every
//! group, identities both ways, cancellations one way) plus commutativity, which bitwright's
//! e-graph gets from sorting operands and egg needs as rules; `mba` adds the usual MBA
//! identities and constant folding, as an egg-based MBA simplifier would. Values are 64-bit, as
//! in every dataset.

use egg::{
    Analysis, AstSize, DidMerge, EGraph, Extractor, Id, Language, RecExpr, Rewrite, Runner, Symbol,
    define_language, rewrite as rw,
};

define_language! {
    /// Bit-vector terms of one width (64).
    pub enum Bv {
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "&" = And([Id; 2]),
        "|" = Or([Id; 2]),
        "^" = Xor([Id; 2]),
        "<<" = Shl([Id; 2]),
        ">>" = Shr([Id; 2]),
        "neg" = Neg(Id),
        "~" = Not(Id),
        Num(u64),
        Var(Symbol),
    }
}

/// Constant folding at 64 bits (the `mba` rule set).
#[derive(Debug, Default)]
pub struct Fold;

fn fold(n: &Bv, c: impl Fn(Id) -> Option<u64>) -> Option<u64> {
    Some(match *n {
        Bv::Num(v) => v,
        Bv::Var(_) => return None,
        Bv::Add([a, b]) => c(a)?.wrapping_add(c(b)?),
        Bv::Sub([a, b]) => c(a)?.wrapping_sub(c(b)?),
        Bv::Mul([a, b]) => c(a)?.wrapping_mul(c(b)?),
        Bv::And([a, b]) => c(a)? & c(b)?,
        Bv::Or([a, b]) => c(a)? | c(b)?,
        Bv::Xor([a, b]) => c(a)? ^ c(b)?,
        Bv::Shl([a, b]) => c(a)?.checked_shl(u32::try_from(c(b)?).ok()?).unwrap_or(0),
        Bv::Shr([a, b]) => c(a)?.checked_shr(u32::try_from(c(b)?).ok()?).unwrap_or(0),
        Bv::Neg(a) => c(a)?.wrapping_neg(),
        Bv::Not(a) => !c(a)?,
    })
}

impl Analysis<Bv> for Fold {
    type Data = Option<u64>;

    fn make(egraph: &mut EGraph<Bv, Self>, enode: &Bv, _id: Id) -> Option<u64> {
        fold(enode, |i| egraph[i].data)
    }

    fn merge(&mut self, to: &mut Option<u64>, from: Option<u64>) -> DidMerge {
        egg::merge_option(to, from, |_, _| DidMerge(false, false))
    }

    fn modify(egraph: &mut EGraph<Bv, Self>, id: Id) {
        if let Some(v) = egraph[id].data {
            let k = egraph.add(Bv::Num(v));
            egraph.union(id, k);
        }
    }
}

/// bitwright's `eqsat.bwr`, every group, plus commutativity.
fn bw_rules<N: Analysis<Bv>>() -> Vec<Rewrite<Bv, N>> {
    let mut v: Vec<Rewrite<Bv, N>> = vec![
        rw!("add-comm"; "(+ ?x ?y)" => "(+ ?y ?x)"),
        rw!("mul-comm"; "(* ?x ?y)" => "(* ?y ?x)"),
        rw!("and-comm"; "(& ?x ?y)" => "(& ?y ?x)"),
        rw!("or-comm"; "(| ?x ?y)" => "(| ?y ?x)"),
        rw!("xor-comm"; "(^ ?x ?y)" => "(^ ?y ?x)"),
        // eqsat.cancel, in the authored direction.
        rw!("add-sub"; "(- (+ ?x ?y) ?y)" => "?x"),
        rw!("sub-add"; "(+ (- ?x ?y) ?y)" => "?x"),
        rw!("xor-xor"; "(^ (^ ?x ?y) ?y)" => "?x"),
        rw!("neg-neg"; "(neg (neg ?x))" => "?x"),
        rw!("not-not"; "(~ (~ ?x))" => "?x"),
        rw!("add-neg"; "(+ ?x (neg ?x))" => "0"),
        rw!("mul-one"; "(* ?x 1)" => "?x"),
        rw!("mul-zero"; "(* ?x 0)" => "0"),
        rw!("add-zero"; "(+ ?x 0)" => "?x"),
    ];
    // eqsat.assoc, distrib, distrib_and, distrib_or, negation: both ways.
    v.extend(rw!("add-assoc"; "(+ (+ ?x ?y) ?z)" <=> "(+ ?x (+ ?y ?z))"));
    v.extend(rw!("mul-assoc"; "(* (* ?x ?y) ?z)" <=> "(* ?x (* ?y ?z))"));
    v.extend(rw!("and-assoc"; "(& (& ?x ?y) ?z)" <=> "(& ?x (& ?y ?z))"));
    v.extend(rw!("or-assoc"; "(| (| ?x ?y) ?z)" <=> "(| ?x (| ?y ?z))"));
    v.extend(rw!("xor-assoc"; "(^ (^ ?x ?y) ?z)" <=> "(^ ?x (^ ?y ?z))"));
    v.extend(rw!("mul-add"; "(* ?x (+ ?y ?z))" <=> "(+ (* ?x ?y) (* ?x ?z))"));
    v.extend(rw!("and-or"; "(& ?x (| ?y ?z))" <=> "(| (& ?x ?y) (& ?x ?z))"));
    v.extend(rw!("and-xor"; "(& ?x (^ ?y ?z))" <=> "(^ (& ?x ?y) (& ?x ?z))"));
    v.extend(rw!("or-and"; "(| ?x (& ?y ?z))" <=> "(& (| ?x ?y) (| ?x ?z))"));
    v.extend(rw!("de-morgan-and"; "(~ (& ?x ?y))" <=> "(| (~ ?x) (~ ?y))"));
    v.extend(rw!("de-morgan-or"; "(~ (| ?x ?y))" <=> "(& (~ ?x) (~ ?y))"));
    v.extend(rw!("neg-add"; "(neg (+ ?x ?y))" <=> "(+ (neg ?x) (neg ?y))"));
    v.extend(rw!("neg-mul"; "(neg (* ?x ?y))" <=> "(* (neg ?x) ?y)"));
    v.extend(rw!("not-xor"; "(~ (^ ?x ?y))" <=> "(^ (~ ?x) ?y)"));
    v
}

/// The `bw` rules plus MBA identities and the usual Boolean facts.
fn mba_rules() -> Vec<Rewrite<Bv, Fold>> {
    let mut v = bw_rules::<Fold>();
    v.extend(rw!("mba-add-xor"; "(+ ?x ?y)" <=> "(+ (^ ?x ?y) (* 2 (& ?x ?y)))"));
    v.extend(rw!("mba-add-or"; "(+ ?x ?y)" <=> "(+ (| ?x ?y) (& ?x ?y))"));
    v.extend(rw!("mba-xor"; "(^ ?x ?y)" <=> "(- (| ?x ?y) (& ?x ?y))"));
    v.extend(rw!("mba-or"; "(| ?x ?y)" <=> "(+ (^ ?x ?y) (& ?x ?y))"));
    v.extend(rw!("mba-or-and"; "(| ?x ?y)" <=> "(+ (& ?x (~ ?y)) ?y)"));
    v.extend(rw!("mba-sub"; "(- ?x ?y)" <=> "(+ ?x (neg ?y))"));
    v.extend(rw!("mba-not"; "(~ ?x)" <=> "(- (neg ?x) 1)"));
    v.extend(rw!("mba-neg"; "(neg ?x)" <=> "(+ (~ ?x) 1)"));
    v.extend([
        rw!("and-self"; "(& ?x ?x)" => "?x"),
        rw!("or-self"; "(| ?x ?x)" => "?x"),
        rw!("xor-self"; "(^ ?x ?x)" => "0"),
        rw!("sub-self"; "(- ?x ?x)" => "0"),
        rw!("and-zero"; "(& ?x 0)" => "0"),
        rw!("and-ones"; "(& ?x 18446744073709551615)" => "?x"),
        rw!("or-zero"; "(| ?x 0)" => "?x"),
        rw!("or-ones"; "(| ?x 18446744073709551615)" => "18446744073709551615"),
        rw!("xor-zero"; "(^ ?x 0)" => "?x"),
        rw!("and-not"; "(& ?x (~ ?x))" => "0"),
        rw!("or-not"; "(| ?x (~ ?x))" => "18446744073709551615"),
        rw!("xor-not"; "(^ ?x (~ ?x))" => "18446744073709551615"),
        rw!("sub-zero"; "(- ?x 0)" => "?x"),
    ]);
    v
}

/// The rule sets, built once.
#[derive(Debug)]
pub struct Rules {
    bw: Vec<Rewrite<Bv, ()>>,
    mba: Vec<Rewrite<Bv, Fold>>,
}

impl Rules {
    pub fn new() -> Rules {
        Rules {
            bw: bw_rules(),
            mba: mba_rules(),
        }
    }
}

/// What a run produced: the extracted term in bitwright's syntax, and whether the e-graph
/// saturated.
#[derive(Debug)]
pub struct Answer {
    pub text: String,
    pub saturated: bool,
}

/// Simplifies `input` (the dataset's syntax) with the `bw` or the `mba` rules.
pub fn simplify(rules: &Rules, input: &str, mba: bool) -> Result<Answer, String> {
    let expr = parse(input)?;
    if mba {
        run(&expr, &rules.mba, Fold)
    } else {
        run(&expr, &rules.bw, ())
    }
}

fn run<N: Analysis<Bv> + Default>(
    expr: &RecExpr<Bv>,
    rules: &[Rewrite<Bv, N>],
    analysis: N,
) -> Result<Answer, String> {
    let runner: Runner<Bv, N, ()> = Runner::new(analysis).with_expr(expr).run(rules);
    let saturated = matches!(runner.stop_reason, Some(egg::StopReason::Saturated));
    let best = Extractor::new(&runner.egraph, AstSize)
        .find_best(runner.roots[0])
        .1;
    Ok(Answer {
        text: print(&best),
        saturated,
    })
}

// ----- the dataset syntax ------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Num(u64),
    Name(String),
    Op(&'static str),
    Open,
    Close,
}

fn lex(s: &str) -> Result<Vec<Tok>, String> {
    let b = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        if c.is_ascii_whitespace() {
            i += 1;
        } else if c.is_ascii_digit() {
            let start = i;
            while i < b.len() && b[i].is_ascii_alphanumeric() {
                i += 1;
            }
            let t = &s[start..i];
            let v = match t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
                Some(h) => u64::from_str_radix(h, 16),
                None => t.parse::<u64>(),
            };
            out.push(Tok::Num(v.map_err(|e| format!("{t}: {e}"))?));
        } else if c.is_ascii_alphabetic() || c == b'_' {
            let start = i;
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                i += 1;
            }
            out.push(Tok::Name(s[start..i].to_string()));
        } else {
            let two = s.get(i..i + 2);
            let (t, n) = match (c, two) {
                (_, Some("<<")) => (Tok::Op("<<"), 2),
                (_, Some(">>")) => (Tok::Op(">>"), 2),
                (b'(', _) => (Tok::Open, 1),
                (b')', _) => (Tok::Close, 1),
                (b'+', _) => (Tok::Op("+"), 1),
                (b'-', _) => (Tok::Op("-"), 1),
                (b'*', _) => (Tok::Op("*"), 1),
                (b'&', _) => (Tok::Op("&"), 1),
                (b'|', _) => (Tok::Op("|"), 1),
                (b'^', _) => (Tok::Op("^"), 1),
                (b'~', _) => (Tok::Op("~"), 1),
                _ => return Err(format!("unexpected {:?}", c as char)),
            };
            out.push(t);
            i += n;
        }
    }
    Ok(out)
}

/// C's binary precedence (higher binds tighter).
fn prec(op: &str) -> Option<u8> {
    Some(match op {
        "|" => 1,
        "^" => 2,
        "&" => 3,
        "<<" | ">>" => 4,
        "+" | "-" => 5,
        "*" => 6,
        _ => return None,
    })
}

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
    out: RecExpr<Bv>,
}

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }

    fn unary(&mut self) -> Result<Id, String> {
        let t = self.peek().cloned().ok_or("unexpected end")?;
        self.pos += 1;
        Ok(match t {
            Tok::Num(v) => self.out.add(Bv::Num(v)),
            Tok::Name(n) => self.out.add(Bv::Var(Symbol::from(n))),
            Tok::Op("-") => {
                let a = self.unary()?;
                self.out.add(Bv::Neg(a))
            }
            Tok::Op("~") => {
                let a = self.unary()?;
                self.out.add(Bv::Not(a))
            }
            Tok::Open => {
                let e = self.binary(0)?;
                if self.peek() != Some(&Tok::Close) {
                    return Err("expected ')'".into());
                }
                self.pos += 1;
                e
            }
            t => return Err(format!("unexpected {t:?}")),
        })
    }

    fn binary(&mut self, min: u8) -> Result<Id, String> {
        let mut lhs = self.unary()?;
        while let Some(Tok::Op(op)) = self.peek().cloned() {
            let Some(p) = prec(op) else { break };
            if p < min {
                break;
            }
            self.pos += 1;
            let rhs = self.binary(p + 1)?;
            let ab = [lhs, rhs];
            lhs = self.out.add(match op {
                "|" => Bv::Or(ab),
                "^" => Bv::Xor(ab),
                "&" => Bv::And(ab),
                "<<" => Bv::Shl(ab),
                ">>" => Bv::Shr(ab),
                "+" => Bv::Add(ab),
                "-" => Bv::Sub(ab),
                _ => Bv::Mul(ab),
            });
        }
        Ok(lhs)
    }
}

/// The dataset's C-like infix as an egg term.
pub fn parse(s: &str) -> Result<RecExpr<Bv>, String> {
    let mut p = Parser {
        toks: lex(s)?,
        pos: 0,
        out: RecExpr::default(),
    };
    p.binary(0)?;
    if p.pos != p.toks.len() {
        return Err(format!("trailing input at token {}", p.pos));
    }
    Ok(p.out)
}

/// A term in bitwright's syntax, one `let` per operator node so sharing survives.
fn print(e: &RecExpr<Bv>) -> String {
    let name = |i: Id| -> String {
        match &e[i] {
            Bv::Num(v) => v.to_string(),
            Bv::Var(s) => s.to_string(),
            _ => format!("t_{}", usize::from(i)),
        }
    };
    let mut out = String::new();
    for (i, n) in e.as_ref().iter().enumerate() {
        let c = n.children();
        let body = match n {
            Bv::Num(_) | Bv::Var(_) => continue,
            Bv::Neg(a) => format!("-{}", name(*a)),
            Bv::Not(a) => format!("~{}", name(*a)),
            _ => {
                let op = match n {
                    Bv::Add(_) => "+",
                    Bv::Sub(_) => "-",
                    Bv::Mul(_) => "*",
                    Bv::And(_) => "&",
                    Bv::Or(_) => "|",
                    Bv::Xor(_) => "^",
                    Bv::Shl(_) => "<<",
                    _ => ">>",
                };
                format!("({} {op} {})", name(c[0]), name(c[1]))
            }
        };
        out.push_str(&format!("let t_{i} = {body}; "));
    }
    out.push_str(&name(Id::from(e.as_ref().len() - 1)));
    out
}

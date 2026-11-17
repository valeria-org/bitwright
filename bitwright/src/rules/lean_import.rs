//! Lean 4 theorems about `BitVec` as `.bwr` rules: `theorem t (x y : BitVec w) (h : x.ult y) :
//! lhs = rhs` becomes `rule t<W>(x: W, y: W) { lhs => rhs if proves(x <u y) }`. A statement
//! Lean proved is an equation that holds, so the rule is sound; the engine still checks what it
//! can (the caller decides whether to run the checker or link the rules trusted).
//!
//! The subset read: `theorem`, `lemma` and `example` declarations (the proof after `:=` is
//! skipped), binders `{w : Nat}`, `(x y : BitVec w)`, `(x : BitVec 32)` and hypotheses
//! `(h : p)`; terms over `+ - * / % &&& ||| ^^^ ~~~ <<< >>> ++`, the `BitVec` methods
//! `zeroExtend` (`setWidth`), `signExtend`, `extractLsb'`, `extractLsb`, `rotateLeft`,
//! `rotateRight`, `sshiftRight'`, `smtUDiv`, `smtSDiv`, `srem`, `ult ule slt sle`, `==`,
//! `!=`, `BitVec.ofBool`, `BitVec.ofNat`, `BitVec.allOnes`, `intMin`, `intMax`,
//! `if … then … else`, `bif`, `decide`, literals `5#w`, `0x1f#32`, `(5 : BitVec w)`. A
//! statement is an equation of bit-vector terms, or a comparison stated `= true` or `= false`.
//! Anything else makes that theorem a comment saying what was not understood; so does a proof
//! that is, or contains, `sorry`: such a statement is a claim, not a theorem.
//!
//! This reads source text, not Lean's checked environment: what it calls proved is what the
//! file says is. A caller that needs more runs Lean on the file first (`bitwright lean-rules
//! --verify` does), and bitwright's own rule checker on the result, which tests every rule
//! exhaustively at small widths whatever its origin.

use std::fmt::Write as _;

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Ident(String),
    Num(String),
    Sym(String),
}

fn lex(src: &str) -> Vec<Tok> {
    let mut out = Vec::new();
    let cs: Vec<char> = src.chars().collect();
    let mut i = 0;
    while i < cs.len() {
        let c = cs[i];
        if c.is_whitespace() {
            i += 1;
        } else if c == '-' && cs.get(i + 1) == Some(&'-') {
            while i < cs.len() && cs[i] != '\n' {
                i += 1;
            }
        } else if c == '/' && cs.get(i + 1) == Some(&'-') {
            let mut depth = 0;
            while i < cs.len() {
                if cs[i] == '/' && cs.get(i + 1) == Some(&'-') {
                    depth += 1;
                    i += 2;
                } else if cs[i] == '-' && cs.get(i + 1) == Some(&'/') {
                    depth -= 1;
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    i += 1;
                }
            }
        } else if c.is_ascii_digit() {
            let s = i;
            if c == '0' && matches!(cs.get(i + 1), Some('x' | 'X')) {
                i += 2;
                while i < cs.len() && cs[i].is_ascii_hexdigit() {
                    i += 1;
                }
            } else {
                while i < cs.len() && cs[i].is_ascii_digit() {
                    i += 1;
                }
            }
            out.push(Tok::Num(cs[s..i].iter().collect()));
        } else if c.is_alphabetic() || c == '_' || c == '«' {
            let s = i;
            if c == '«' {
                while i < cs.len() && cs[i] != '»' {
                    i += 1;
                }
                i += 1;
            } else {
                while i < cs.len()
                    && (cs[i].is_alphanumeric() || matches!(cs[i], '_' | '\'' | '!' | '?' | '.'))
                {
                    // A dot joins a namespace (`BitVec.ofNat`); a dot before a method on a
                    // closing parenthesis is lexed by the parser from the symbol.
                    i += 1;
                }
            }
            let mut word: String = cs[s..i].iter().collect();
            word = word.trim_matches(|c| c == '«' || c == '»').to_string();
            // `x.ult` lexes as one word; split into the name and its methods.
            let mut parts = word.split('.').peekable();
            let first = parts.next().unwrap_or("").to_string();
            if first.chars().next().is_some_and(|c| c.is_uppercase()) && parts.peek().is_some() {
                // A namespace path (`BitVec.ofBool`): keep it whole.
                out.push(Tok::Ident(word.clone()));
            } else {
                out.push(Tok::Ident(first));
                for p in parts {
                    out.push(Tok::Sym(".".into()));
                    out.push(Tok::Ident(p.to_string()));
                }
            }
        } else {
            let three: String = cs[i..(i + 3).min(cs.len())].iter().collect();
            let two: String = cs[i..(i + 2).min(cs.len())].iter().collect();
            let sym = if ["&&&", "|||", "^^^", "~~~", "<<<", ">>>"].contains(&three.as_str()) {
                three
            } else if ["++", "==", "!=", ":=", "<=", ">=", "=>", "→", "∧"].contains(&two.as_str())
            {
                two
            } else {
                c.to_string()
            };
            i += sym.chars().count();
            out.push(Tok::Sym(sym));
        }
    }
    out
}

/// A translated term: its `.bwr` text, whether it is a Boolean (1-bit) value, its known width
/// text when obvious, its raw numeric value while untyped (before `#w` is attached), and
/// whether it is a `Nat` read off a vector (`x.toNat`, written as the vector itself).
#[derive(Clone, Debug)]
struct T {
    text: String,
    boolean: bool,
    width: Option<String>,
    raw_num: Option<u128>,
    nat: bool,
}

impl T {
    fn bool_val(text: String) -> Self {
        T {
            text,
            boolean: true,
            width: None,
            raw_num: None,
            nat: false,
        }
    }
}

struct Parser<'a> {
    toks: &'a [Tok],
    at: usize,
    /// Width variables, Lean name to `.bwr` name.
    widths: Vec<(String, String)>,
    /// Parameters, with their width text (`W` or `32`).
    params: Vec<(String, String)>,
    /// Minimum bitwidth required for each `.bwr` width variable by typed literals (`5#w`).
    width_bounds: Vec<(String, u32)>,
    /// Minimum bitwidth required by untyped literals (`x + 5`).
    untyped_literal_bits: u32,
}

type R<T> = Result<T, String>;

impl Parser<'_> {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.at)
    }
    fn peek_sym(&self, s: &str) -> bool {
        matches!(self.peek(), Some(Tok::Sym(x)) if x == s)
    }
    fn peek_ident(&self, s: &str) -> bool {
        matches!(self.peek(), Some(Tok::Ident(x)) if x == s)
    }
    fn eat_sym(&mut self, s: &str) -> bool {
        if self.peek_sym(s) {
            self.at += 1;
            true
        } else {
            false
        }
    }
    fn expect_sym(&mut self, s: &str) -> R<()> {
        if self.eat_sym(s) {
            Ok(())
        } else {
            Err(format!("expected `{s}`, found {}", self.describe()))
        }
    }
    fn describe(&self) -> String {
        match self.peek() {
            Some(Tok::Ident(s)) | Some(Tok::Num(s)) | Some(Tok::Sym(s)) => format!("`{s}`"),
            None => "the end".to_string(),
        }
    }
    fn ident(&mut self) -> R<String> {
        match self.peek().cloned() {
            Some(Tok::Ident(s)) => {
                self.at += 1;
                Ok(s)
            }
            _ => Err(format!("expected a name, found {}", self.describe())),
        }
    }

    /// A width in a type or a method argument: a width variable or a number.
    fn width(&mut self) -> R<String> {
        let paren = self.eat_sym("(");
        let w = match self.peek().cloned() {
            Some(Tok::Num(n)) => {
                self.at += 1;
                n
            }
            Some(Tok::Ident(v)) => {
                self.at += 1;
                self.widths
                    .iter()
                    .find(|(l, _)| *l == v)
                    .map(|(_, b)| b.clone())
                    .ok_or_else(|| format!("`{v}` is not a width variable"))?
            }
            _ => return Err(format!("expected a width, found {}", self.describe())),
        };
        if paren {
            self.expect_sym(")")?;
        }
        Ok(w)
    }

    /// The width of a parameter by name, for literals typed by their context.
    fn param_width(&self, name: &str) -> Option<&str> {
        self.params
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, w)| w.as_str())
    }

    /// A literal's value; an error past 128 bits (its value modulo `2^w` would be lost).
    fn parse_num(s: &str) -> R<u128> {
        let v = match s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
            Some(h) => u128::from_str_radix(h, 16),
            None => s.parse::<u128>(),
        };
        v.map_err(|_| format!("the literal `{s}` (more than 128 bits)"))
    }

    /// The literal `v` at the fixed width `wb`, where it does not fit: modulo `2^wb`, as Lean
    /// reads it (`300#8` is 44).
    fn wrapped(v: u128, wb: u32) -> Option<u128> {
        if !(1..=128).contains(&wb) {
            return None;
        }
        let mask = u128::MAX >> (128 - wb);
        (v > mask).then_some(v & mask)
    }

    fn note_width_bits(&mut self, bwr_width: &str, bits: u32) {
        if bits <= 1 || !self.widths.iter().any(|(_, b)| b == bwr_width) {
            return;
        }
        if let Some(slot) = self.width_bounds.iter_mut().find(|(b, _)| b == bwr_width) {
            slot.1 = slot.1.max(bits);
        } else {
            self.width_bounds.push((bwr_width.to_string(), bits));
        }
    }

    fn resize_cast(kind: &str, a: T, w: String) -> T {
        if a.width.as_deref() == Some(w.as_str()) {
            return T {
                width: Some(w),
                ..a
            };
        }
        if let (Some(Ok(aw)), Ok(tw)) =
            (a.width.as_deref().map(str::parse::<u32>), w.parse::<u32>())
        {
            let text = if tw < aw {
                format!("trunc<{w}>({})", a.text)
            } else if tw > aw {
                format!("zext<{w}>({})", a.text)
            } else {
                a.text
            };
            return T {
                text,
                boolean: false,
                width: Some(w),
                raw_num: None,
                nat: false,
            };
        }
        let op = if kind == "truncate" { "trunc" } else { "zext" };
        T {
            text: format!("{op}<{w}>({})", a.text),
            boolean: false,
            width: Some(w),
            raw_num: None,
            nat: false,
        }
    }

    // Lean's precedences, lowest first: ∧ (35), = ≠ == != < ≤ > ≥ (50), ||| (55), ^^^ (58),
    // &&& (60), + - ++ (65), * / % (70), <<< >>> (75). All associate to the left but `∧`
    // (`infixr:35`): `a ++ b + c` is `(a ++ b) + c`.
    fn term(&mut self) -> R<T> {
        self.binary(0)
    }

    fn binary(&mut self, min: u8) -> R<T> {
        let mut lhs = self.unary()?;
        while let Some(Tok::Sym(op)) = self.peek().cloned() {
            if op == "/" && 8 >= min {
                return Err(
                    "`/` defines division by zero as 0 in Lean (use `BitVec.smtUDiv`)".into(),
                );
            }
            let (prec, bwr, boolean) = match op.as_str() {
                // The 1-bit `&`, not the guard's `&&`: a conjunction can be a value (an `if`
                // condition, `BitVec.ofBool`). Hypotheses are split at it (`split_conjuncts`).
                "∧" => (1, "&", true),
                "=" | "==" => (2, "==", true),
                "≠" | "!=" => (2, "!=", true),
                "<" => (2, "<u", true),
                "≤" | "<=" => (2, "<=u", true),
                ">" => (2, ">u", true),
                "≥" | ">=" => (2, ">=u", true),
                "|||" => (3, "|", false),
                "^^^" => (4, "^", false),
                "&&&" => (5, "&", false),
                "++" => (7, "concat", false),
                "+" => (7, "+", false),
                "-" => (7, "-", false),
                "*" => (8, "*", false),
                "%" => (8, "urem", false),
                "<<<" => (9, "<<", false),
                ">>>" => (9, ">>u", false),
                _ => break,
            };
            if prec < min {
                break;
            }
            self.at += 1;
            let next_min = if op == "∧" { prec } else { prec + 1 };
            let rhs = self.binary(next_min)?;
            // A `toNat` is written as its vector: comparisons read the same (unsigned, below
            // `2^w`), arithmetic does not (`Nat` neither wraps nor truncates the same way).
            if (lhs.nat || rhs.nat) && !boolean {
                return Err(format!(
                    "`{op}` on a `toNat` (Nat arithmetic does not wrap)"
                ));
            }
            // A `toNat` against a `Nat` literal: the literal is written at the vector's width,
            // where it wraps; so it must be below `2^w` (a width variable is bounded to that).
            if boolean && op != "∧" && lhs.nat != rhs.nat {
                let (v, k) = if lhs.nat { (&lhs, &rhs) } else { (&rhs, &lhs) };
                if k.width.is_none() && k.text.starts_with(|c: char| c.is_ascii_digit()) {
                    let bits = 128 - Self::parse_num(&k.text)?.leading_zeros();
                    match v.width.clone() {
                        Some(w) => match w.parse::<u32>() {
                            Ok(wb) if bits > wb => {
                                return Err(format!(
                                    "`{}` compared with a `toNat` of {wb} bits",
                                    k.text
                                ));
                            }
                            Ok(_) => {}
                            Err(_) => self.note_width_bits(&w, bits),
                        },
                        None => {
                            return Err("a `toNat` of unknown width against a literal".into());
                        }
                    }
                }
            }
            // `t = true` and `t == true` are the Boolean `t` itself.
            if boolean && op != "∧" && (rhs.text == "true" || lhs.text == "true") {
                lhs = if rhs.text == "true" { lhs } else { rhs };
                lhs.boolean = true;
                continue;
            }
            let out_width = if boolean || bwr == "concat" {
                None
            } else {
                lhs.width.clone().or_else(|| rhs.width.clone())
            };
            lhs = T {
                text: match bwr {
                    "concat" | "udiv" | "urem" => format!("{bwr}({}, {})", lhs.text, rhs.text),
                    _ => format!("({} {bwr} {})", lhs.text, rhs.text),
                },
                boolean,
                width: out_width,
                raw_num: None,
                nat: false,
            };
        }
        Ok(lhs)
    }

    fn unary(&mut self) -> R<T> {
        if self.eat_sym("~~~") {
            let a = self.unary()?;
            return Ok(T {
                text: format!("~{}", a.text),
                boolean: false,
                width: a.width,
                raw_num: None,
                nat: false,
            });
        }
        if self.eat_sym("-") {
            let a = self.unary()?;
            return Ok(T {
                text: format!("-{}", a.text),
                boolean: false,
                width: a.width,
                raw_num: None,
                nat: false,
            });
        }
        if self.eat_sym("¬") {
            return Err("negation (the facts can prove, never refute)".into());
        }
        self.postfix()
    }

    fn postfix(&mut self) -> R<T> {
        let mut t = self.atom()?;
        loop {
            if self.peek_sym(".") {
                let save = self.at;
                self.at += 1;
                let Ok(m) = self.ident() else {
                    self.at = save;
                    break;
                };
                if let Some(v) = t.raw_num.take() {
                    self.untyped_literal_bits =
                        self.untyped_literal_bits.max(128 - v.leading_zeros());
                }
                t = self.method(t, &m)?;
            } else if self.peek_sym("#") {
                // `5#w`: a literal with its width (wrapped modulo `2^w` at fixed widths).
                self.at += 1;
                let w = self.width()?;
                if let Some(v) = t.raw_num.take() {
                    match w.parse::<u32>() {
                        Ok(wb) => {
                            if let Some(k) = Self::wrapped(v, wb) {
                                t.text = k.to_string();
                            }
                        }
                        Err(_) => self.note_width_bits(&w, 128 - v.leading_zeros()),
                    }
                }
                t.width = Some(w);
            } else {
                break;
            }
        }
        if let Some(v) = t.raw_num.take() {
            self.untyped_literal_bits = self.untyped_literal_bits.max(128 - v.leading_zeros());
        }
        Ok(t)
    }

    fn method(&mut self, t: T, m: &str) -> R<T> {
        let a = t.text.clone();
        let aw = t.width.clone();
        let arg = |p: &mut Self| p.arg();
        Ok(match m {
            "zeroExtend" | "setWidth" | "truncate" => {
                let w = self.width()?;
                Self::resize_cast(m, t, w)
            }
            "signExtend" => {
                let w = self.width()?;
                T {
                    text: format!("sext<{w}>({a})"),
                    boolean: false,
                    width: Some(w),
                    raw_num: None,
                    nat: false,
                }
            }
            "extractLsb'" => {
                let lo = self.nat()?;
                let len = self.nat()?;
                T {
                    text: if lo == 0 {
                        format!("trunc<{len}>({a})")
                    } else {
                        format!("extract<{lo}, {len}>({a})")
                    },
                    boolean: false,
                    width: Some(len.to_string()),
                    raw_num: None,
                    nat: false,
                }
            }
            "extractLsb" => {
                let hi = self.nat()?;
                let lo = self.nat()?;
                let len = hi + 1 - lo;
                T {
                    text: if lo == 0 {
                        format!("trunc<{len}>({a})")
                    } else {
                        format!("extract<{lo}, {len}>({a})")
                    },
                    boolean: false,
                    width: Some(len.to_string()),
                    raw_num: None,
                    nat: false,
                }
            }
            "rotateLeft" | "rotateRight" => {
                let n = arg(self)?;
                T {
                    text: format!(
                        "{}({a}, {})",
                        if m == "rotateLeft" { "rotl" } else { "rotr" },
                        n.text
                    ),
                    boolean: false,
                    width: aw,
                    raw_num: None,
                    nat: false,
                }
            }
            "sshiftRight'" | "sshiftRight" => {
                let n = arg(self)?;
                T {
                    text: format!("({a} >>s {})", n.text),
                    boolean: false,
                    width: aw,
                    raw_num: None,
                    nat: false,
                }
            }
            "smtUDiv" => T {
                text: format!("udiv({a}, {})", arg(self)?.text),
                boolean: false,
                width: aw,
                raw_num: None,
                nat: false,
            },
            "smtSDiv" => T {
                text: format!("sdiv({a}, {})", arg(self)?.text),
                boolean: false,
                width: aw,
                raw_num: None,
                nat: false,
            },
            "udiv" | "sdiv" => {
                return Err(format!(
                    "`{m}` defines division by zero as 0 in Lean (use `smtUDiv` or `smtSDiv`)"
                ));
            }
            "umod" | "urem" => T {
                text: format!("urem({a}, {})", arg(self)?.text),
                boolean: false,
                width: aw,
                raw_num: None,
                nat: false,
            },
            "srem" => T {
                text: format!("srem({a}, {})", arg(self)?.text),
                boolean: false,
                width: aw,
                raw_num: None,
                nat: false,
            },
            "ult" | "ule" | "slt" | "sle" => {
                let op = match m {
                    "ult" => "<u",
                    "ule" => "<=u",
                    "slt" => "<s",
                    _ => "<=s",
                };
                T::bool_val(format!("({a} {op} {})", arg(self)?.text))
            }
            "toNat" => T {
                text: a,
                boolean: false,
                width: aw,
                raw_num: None,
                nat: true,
            },
            other => return Err(format!("the method `{other}`")),
        })
    }

    /// An argument of a method or a function: an atom (with its own postfix methods).
    fn arg(&mut self) -> R<T> {
        if self.eat_sym("(") {
            let t = self.term()?;
            self.expect_sym(")")?;
            return Ok(t);
        }
        self.postfix()
    }

    fn nat(&mut self) -> R<u32> {
        let paren = self.eat_sym("(");
        let v = match self.peek().cloned() {
            Some(Tok::Num(n)) => {
                self.at += 1;
                n.parse::<u32>()
                    .map_err(|_| format!("`{n}` is not a small number"))?
            }
            _ => return Err(format!("expected a number, found {}", self.describe())),
        };
        if paren {
            self.expect_sym(")")?;
        }
        Ok(v)
    }

    fn atom(&mut self) -> R<T> {
        match self.peek().cloned() {
            Some(Tok::Sym(s)) if s == "(" => {
                self.at += 1;
                let t = self.term()?;
                // `(5 : BitVec w)`: a typed literal.
                if self.eat_sym(":") {
                    self.skip_type()?;
                }
                self.expect_sym(")")?;
                Ok(t)
            }
            Some(Tok::Num(n)) => {
                self.at += 1;
                let v = Self::parse_num(&n)?;
                Ok(T {
                    text: n,
                    boolean: false,
                    width: None,
                    raw_num: Some(v),
                    nat: false,
                })
            }
            Some(Tok::Ident(name)) => {
                self.at += 1;
                match name.as_str() {
                    "true" | "false" => Ok(T::bool_val(name)),
                    "if" | "bif" => {
                        let c = self.term()?;
                        if !self.peek_ident("then") {
                            return Err(format!("expected `then`, found {}", self.describe()));
                        }
                        self.at += 1;
                        let t = self.term()?;
                        if !self.peek_ident("else") {
                            return Err(format!("expected `else`, found {}", self.describe()));
                        }
                        self.at += 1;
                        let e = self.term()?;
                        Ok(T {
                            text: format!("select({}, {}, {})", c.text, t.text, e.text),
                            boolean: false,
                            width: t.width.or(e.width),
                            raw_num: None,
                            nat: t.nat || e.nat,
                        })
                    }
                    "decide" => {
                        let c = self.arg()?;
                        Ok(T { boolean: true, ..c })
                    }
                    "BitVec.ofBool" => {
                        let c = self.arg()?;
                        Ok(T::bool_val(c.text))
                    }
                    "BitVec.ofNat" => {
                        let w = self.width()?;
                        if let Some(Tok::Num(ns)) = self.peek().cloned() {
                            self.at += 1;
                            let v = Self::parse_num(&ns)?;
                            let text = match w.parse::<u32>() {
                                Ok(wb) => Self::wrapped(v, wb).map_or(ns, |k| k.to_string()),
                                Err(_) => {
                                    self.note_width_bits(&w, 128 - v.leading_zeros());
                                    ns
                                }
                            };
                            Ok(T {
                                text,
                                boolean: false,
                                width: Some(w),
                                raw_num: None,
                                nat: false,
                            })
                        } else {
                            let n = self.arg()?;
                            Ok(T {
                                text: n.text,
                                boolean: false,
                                width: Some(w),
                                raw_num: None,
                                nat: false,
                            })
                        }
                    }
                    "BitVec.allOnes" => {
                        let w = self.width()?;
                        Ok(T {
                            text: "ones".into(),
                            boolean: false,
                            width: Some(w),
                            raw_num: None,
                            nat: false,
                        })
                    }
                    "BitVec.intMin" => {
                        let w = self.width()?;
                        Ok(T {
                            text: "smin_lit".into(),
                            boolean: false,
                            width: Some(w),
                            raw_num: None,
                            nat: false,
                        })
                    }
                    "BitVec.intMax" => {
                        let w = self.width()?;
                        Ok(T {
                            text: "smax_lit".into(),
                            boolean: false,
                            width: Some(w),
                            raw_num: None,
                            nat: false,
                        })
                    }
                    "BitVec.zeroExtend" | "BitVec.setWidth" | "BitVec.truncate"
                    | "BitVec.signExtend" => {
                        let w = self.width()?;
                        let a = self.arg()?;
                        if name.ends_with("signExtend") {
                            Ok(T {
                                text: format!("sext<{w}>({})", a.text),
                                boolean: false,
                                width: Some(w),
                                raw_num: None,
                                nat: false,
                            })
                        } else {
                            let kind = name.rsplit('.').next().unwrap_or("zext");
                            Ok(Self::resize_cast(kind, a, w))
                        }
                    }
                    "BitVec.smtUDiv" | "BitVec.smtSDiv" | "BitVec.srem" => {
                        let a = self.arg()?;
                        let b = self.arg()?;
                        let f = match name.as_str() {
                            "BitVec.smtUDiv" => "udiv",
                            "BitVec.smtSDiv" => "sdiv",
                            _ => "srem",
                        };
                        Ok(T {
                            text: format!("{f}({}, {})", a.text, b.text),
                            boolean: false,
                            width: a.width.or(b.width),
                            raw_num: None,
                            nat: false,
                        })
                    }
                    "BitVec.udiv" | "BitVec.sdiv" => Err(format!(
                        "`{name}` defines division by zero as 0 in Lean (use `BitVec.smtUDiv` or `BitVec.smtSDiv`)"
                    )),
                    "BitVec.rotateLeft" | "BitVec.rotateRight" => {
                        let a = self.arg()?;
                        let n = self.arg()?;
                        let f = if name.ends_with("Left") {
                            "rotl"
                        } else {
                            "rotr"
                        };
                        Ok(T {
                            text: format!("{f}({}, {})", a.text, n.text),
                            boolean: false,
                            width: a.width,
                            raw_num: None,
                            nat: false,
                        })
                    }
                    _ if self.param_width(&name).is_some() => {
                        let w = self.param_width(&name).map(str::to_string);
                        Ok(T {
                            text: name,
                            boolean: false,
                            width: w,
                            raw_num: None,
                            nat: false,
                        })
                    }
                    _ => Err(format!("`{name}`")),
                }
            }
            _ => Err(format!("expected a term, found {}", self.describe())),
        }
    }

    /// Skips a type after `:` inside parentheses.
    fn skip_type(&mut self) -> R<()> {
        let mut depth = 0;
        while let Some(t) = self.peek() {
            match t {
                Tok::Sym(s) if s == "(" => depth += 1,
                Tok::Sym(s) if s == ")" => {
                    if depth == 0 {
                        return Ok(());
                    }
                    depth -= 1;
                }
                _ => {}
            }
            self.at += 1;
        }
        Err("an unclosed type".into())
    }
}

/// One declaration, translated or not.
struct Decl {
    name: String,
    text: Result<String, String>,
}

/// The conjuncts of a Boolean hypothesis's text, each its own `proves(...)`. Every binary
/// operation is written parenthesized, so the only `&` outside parentheses is the root's: of
/// two 1-bit values (the hypothesis is Boolean), true exactly when both are.
fn split_conjuncts(s: &str, out: &mut Vec<String>) {
    let s = strip_outer(s.trim());
    let mut depth = 0usize;
    let bytes = s.as_bytes();
    for i in 0..bytes.len() {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => depth = depth.saturating_sub(1),
            b' ' if depth == 0 && s[i..].starts_with(" & ") => {
                split_conjuncts(&s[..i], out);
                split_conjuncts(&s[i + 3..], out);
                return;
            }
            _ => {}
        }
    }
    out.push(s);
}

fn declaration(toks: &[Tok], at: &mut usize, n: usize) -> Decl {
    let mut p = Parser {
        toks,
        at: *at,
        widths: Vec::new(),
        params: Vec::new(),
        width_bounds: Vec::new(),
        untyped_literal_bits: 0,
    };
    // The keyword and the name first, so a failure can be reported by name.
    let kw = p.ident().unwrap_or_default();
    let decl_name = if kw == "example" {
        format!("lean_example_{n}")
    } else {
        p.ident().unwrap_or_else(|_| format!("declaration {n}"))
    };
    let r = (|| -> R<String> {
        let name = decl_name.clone();
        let mut hyps: Vec<String> = Vec::new();
        // Binders.
        loop {
            if p.eat_sym("{") {
                let mut names = Vec::new();
                while let Some(Tok::Ident(_)) = p.peek() {
                    names.push(p.ident()?);
                }
                p.expect_sym(":")?;
                let ty = p.ident()?;
                if ty != "Nat" && ty != "ℕ" {
                    return Err(format!("an implicit of type `{ty}`"));
                }
                for v in names {
                    let bwr = ["W", "U", "V", "X"]
                        .get(p.widths.len())
                        .ok_or("more than four width variables")?
                        .to_string();
                    p.widths.push((v, bwr));
                }
                p.expect_sym("}")?;
            } else if p.eat_sym("[") {
                p.skip_type()?;
                // `]` is skipped as the type's closer.
                while !p.eat_sym("]") {
                    if p.peek().is_none() {
                        return Err("an unclosed instance binder".into());
                    }
                    p.at += 1;
                }
            } else if p.eat_sym("(") {
                let mut names = Vec::new();
                while let Some(Tok::Ident(_)) = p.peek() {
                    names.push(p.ident()?);
                }
                p.expect_sym(":")?;
                if p.peek_ident("BitVec") {
                    p.at += 1;
                    let w = p.width()?;
                    for v in names {
                        p.params.push((v, w.clone()));
                    }
                } else if p.peek_ident("Nat") || p.peek_ident("ℕ") {
                    p.at += 1;
                    for v in names {
                        let bwr = ["W", "U", "V", "X"]
                            .get(p.widths.len())
                            .ok_or("more than four width variables")?
                            .to_string();
                        p.widths.push((v, bwr));
                    }
                } else {
                    // A hypothesis: a proposition about the parameters.
                    let prop = p.term().map_err(|e| format!("in a hypothesis: {e}"))?;
                    if !prop.boolean {
                        return Err("a hypothesis that is not a comparison".into());
                    }
                    let mut parts = Vec::new();
                    split_conjuncts(&prop.text, &mut parts);
                    for part in parts {
                        hyps.push(format!("proves({part})"));
                    }
                }
                p.expect_sym(")")?;
            } else {
                break;
            }
        }
        p.expect_sym(":")?;
        // The statement: `lhs = rhs` over bit-vectors.
        let lhs = p.binary(3)?;
        if !p.eat_sym("=") {
            return Err(format!(
                "a statement that is not an equation (found {})",
                p.describe()
            ));
        }
        // A comparison stated true or false is a rule too: `p = true` is `p => true`.
        let truth = match p.peek() {
            Some(Tok::Ident(t)) if lhs.boolean && (t == "true" || t == "false") => {
                let t = t.clone();
                p.at += 1;
                Some(t)
            }
            _ => None,
        };
        let rhs = match &truth {
            Some(t) => T::bool_val(t.clone()),
            None => p.binary(3)?,
        };
        if truth.is_none() && (lhs.boolean || rhs.boolean) {
            return Err("an equation of Booleans (write it over `BitVec.ofBool` values)".into());
        }
        if !p.eat_sym(":=") && p.peek().is_some() {
            return Err(format!(
                "expected `:=` after the statement, found {}",
                p.describe()
            ));
        }
        // Untyped literals bound the statement's width variable (or the first width variable).
        if p.untyped_literal_bits > 1 {
            let target = lhs
                .width
                .clone()
                .or_else(|| rhs.width.clone())
                .or_else(|| p.widths.first().map(|(_, b)| b.clone()));
            if let Some(w) = target {
                p.note_width_bits(&w, p.untyped_literal_bits);
            }
        }
        let params: Vec<String> = p.params.iter().map(|(n, w)| format!("{n}: {w}")).collect();
        let generics = if p.widths.is_empty() {
            String::new()
        } else {
            format!(
                "<{}>",
                p.widths
                    .iter()
                    .map(|(_, b)| b.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        let mut wher = String::new();
        if !p.width_bounds.is_empty() {
            let clauses: Vec<String> = p
                .width_bounds
                .iter()
                .map(|(w, b)| format!("{w} >= {b}"))
                .collect();
            let _ = write!(wher, " where {}", clauses.join(", "));
        }
        let guard = if hyps.is_empty() {
            String::new()
        } else {
            format!("\n        if {}", hyps.join(" && "))
        };
        let mut s = format!(
            "    /// From Lean: `{kw} {name}`.\n    rule {name}{generics}({}){wher} {{\n        {} => {}{guard}\n    }}\n",
            params.join(", "),
            strip_outer(&lhs.text),
            strip_outer(&rhs.text)
        );
        // A comparison stated true or false says as much of its negation, which is the
        // form the other way round and is not rewritten to it: a rule for that one too.
        if let Some(t) = &truth
            && let Some(negation) = negated(&strip_outer(&lhs.text))
        {
            let opposite = if t == "true" { "false" } else { "true" };
            let _ = write!(
                s,
                "    /// From Lean: `{kw} {name}`, of the negation.\n    rule {name}_negated{generics}({}){wher} {{\n        {negation} => {opposite}{guard}\n    }}\n",
                params.join(", "),
            );
        }
        Ok(s)
    })();
    // Skip to the next declaration: the proof, which must not give up.
    let mut i = p.at.max(*at + 1);
    let mut admitted = false;
    while i < toks.len() {
        if let Tok::Ident(k) = &toks[i] {
            if matches!(k.as_str(), "theorem" | "lemma" | "example") {
                break;
            }
            admitted |= matches!(k.as_str(), "sorry" | "admit" | "sorryAx");
        }
        i += 1;
    }
    *at = i;
    Decl {
        name: decl_name,
        text: match r {
            Ok(_) if admitted => Err("its proof is `sorry`: nothing was proved".into()),
            r => r,
        },
    }
}

/// The negation of a comparison `a op b` (its operator outside any parentheses), as the
/// comparison it is: `a <u b` is not `b <=u a`, `a == b` is not `a != b`.
fn negated(cmp: &str) -> Option<String> {
    let mut depth = 0usize;
    let bytes = cmp.as_bytes();
    for (i, &c) in bytes.iter().enumerate() {
        match c {
            b'(' => depth += 1,
            b')' => depth = depth.saturating_sub(1),
            b' ' if depth == 0 => {
                for (op, other, swap) in [
                    (" <=u ", "<u", true),
                    (" <u ", "<=u", true),
                    (" <=s ", "<s", true),
                    (" <s ", "<=s", true),
                    (" == ", "!=", false),
                    (" != ", "==", false),
                ] {
                    if cmp[i..].starts_with(op) {
                        let (a, b) = (&cmp[..i], &cmp[i + op.len()..]);
                        return Some(if swap {
                            format!("{b} {other} {a}")
                        } else {
                            format!("{a} {other} {b}")
                        });
                    }
                }
            }
            _ => {}
        }
    }
    None
}

/// `(x)` as `x`.
fn strip_outer(s: &str) -> String {
    if s.starts_with('(') && s.ends_with(')') {
        let mut depth = 0;
        for (i, c) in s.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 && i != s.len() - 1 {
                        return s.to_string();
                    }
                }
                _ => {}
            }
        }
        return s[1..s.len() - 1].to_string();
    }
    s.to_string()
}

/// Lean source as a `.bwr` program (group `lean`), with a comment for each theorem not read:
/// see the [module](self) for what is read and what the result may be trusted for.
///
/// ```
/// let lean = "
///     theorem add_sub_cancel {w : Nat} (x y : BitVec w) : x + y - y = x := by bv_omega
///     theorem and_or_absorb (x y : BitVec 32) : x &&& (x ||| y) = x := by bv_decide
///     theorem wishful {w : Nat} (x : BitVec w) : x * 3 = x := by sorry";
/// let rules = bitwright::rules::lean_import::to_bwr(lean);
/// assert!(rules.contains("rule add_sub_cancel<W>(x: W, y: W)"));
/// assert!(rules.contains("// wishful: not translated: its proof is `sorry`"));
/// let program = bitwright::rules::RuleProgram::compile(&rules).unwrap();
/// assert_eq!(program.rules().len(), 2);
///
/// // A comparison stated true gives a rule for it and one for its negation.
/// let lean = "theorem umod_ult {w : Nat} (x y : BitVec w) (h : y != 0#w) :
///     (x % y).ult y = true := by sorry_free_proof";
/// let rules = bitwright::rules::lean_import::to_bwr(lean);
/// assert!(rules.contains("urem(x, y) <u y => true"));
/// assert!(rules.contains("y <=u urem(x, y) => false"));
/// ```
pub fn to_bwr(src: &str) -> String {
    let toks = lex(src);
    let mut at = 0;
    // To the first declaration.
    while at < toks.len()
        && !matches!(&toks[at], Tok::Ident(k) if matches!(k.as_str(), "theorem" | "lemma" | "example"))
    {
        at += 1;
    }
    let mut rules = String::new();
    let mut notes = String::new();
    let mut n = 0;
    while at < toks.len() {
        n += 1;
        let d = declaration(&toks, &mut at, n);
        match d.text {
            Ok(t) => rules.push_str(&t),
            Err(why) => {
                let _ = writeln!(notes, "// {}: not translated: {why}.", d.name);
            }
        }
    }
    if n == 0 {
        notes.push_str("// No `theorem`, `lemma` or `example` found.\n");
    }
    format!("bitwright 1;\n\n{notes}group lean {{\n{rules}}}\n")
}

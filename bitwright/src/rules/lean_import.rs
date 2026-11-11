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

/// A translated term: its `.bwr` text, and whether it is a Boolean (1-bit) value.
#[derive(Clone, Debug)]
struct T {
    text: String,
    boolean: bool,
}

struct Parser<'a> {
    toks: &'a [Tok],
    at: usize,
    /// Width variables, Lean name to `.bwr` name.
    widths: Vec<(String, String)>,
    /// Parameters, with their width text (`W` or `32`).
    params: Vec<(String, String)>,
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

    // Lean's precedences, lowest first: ∧ (35), = ≠ == != < ≤ (50), ||| (65), ^^^ (58? in
    // Lean `^^^` is 58, `&&&` 60, `|||` 55), <<< >>> (75), + - (65), * / % (70), ++ (65).
    fn term(&mut self) -> R<T> {
        self.binary(0)
    }

    fn binary(&mut self, min: u8) -> R<T> {
        let mut lhs = self.unary()?;
        while let Some(Tok::Sym(op)) = self.peek().cloned() {
            let (prec, bwr, boolean) = match op.as_str() {
                "∧" => (1, "&", true),
                "=" | "==" => (2, "==", true),
                "≠" | "!=" => (2, "!=", true),
                "|||" => (3, "|", false),
                "^^^" => (4, "^", false),
                "&&&" => (5, "&", false),
                "++" => (6, "concat", false),
                "+" => (7, "+", false),
                "-" => (7, "-", false),
                "*" => (8, "*", false),
                "/" => (8, "udiv", false),
                "%" => (8, "urem", false),
                "<<<" => (9, "<<", false),
                ">>>" => (9, ">>u", false),
                _ => break,
            };
            if prec < min {
                break;
            }
            self.at += 1;
            let rhs = self.binary(prec + 1)?;
            // `t = true` and `t == true` are the Boolean `t` itself.
            if boolean && op != "∧" && (rhs.text == "true" || lhs.text == "true") {
                lhs = if rhs.text == "true" { lhs } else { rhs };
                lhs.boolean = true;
                continue;
            }
            lhs = T {
                text: match bwr {
                    "concat" | "udiv" | "urem" => format!("{bwr}({}, {})", lhs.text, rhs.text),
                    _ => format!("({} {bwr} {})", lhs.text, rhs.text),
                },
                boolean,
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
            });
        }
        if self.eat_sym("-") {
            let a = self.unary()?;
            return Ok(T {
                text: format!("-{}", a.text),
                boolean: false,
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
                t = self.method(t, &m)?;
            } else if self.peek_sym("#") {
                // `5#w`: a literal with its width.
                self.at += 1;
                let _w = self.width()?;
            } else {
                break;
            }
        }
        Ok(t)
    }

    fn method(&mut self, t: T, m: &str) -> R<T> {
        let a = t.text;
        let arg = |p: &mut Self| p.arg();
        Ok(match m {
            "zeroExtend" | "setWidth" | "truncate" => {
                let w = self.width()?;
                T {
                    text: format!("zext<{w}>({a})"),
                    boolean: false,
                }
            }
            "signExtend" => {
                let w = self.width()?;
                T {
                    text: format!("sext<{w}>({a})"),
                    boolean: false,
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
                }
            }
            "sshiftRight'" | "sshiftRight" => {
                let n = arg(self)?;
                T {
                    text: format!("({a} >>s {})", n.text),
                    boolean: false,
                }
            }
            "smtUDiv" | "udiv" => T {
                text: format!("udiv({a}, {})", arg(self)?.text),
                boolean: false,
            },
            "smtSDiv" | "sdiv" => T {
                text: format!("sdiv({a}, {})", arg(self)?.text),
                boolean: false,
            },
            "umod" | "urem" => T {
                text: format!("urem({a}, {})", arg(self)?.text),
                boolean: false,
            },
            "srem" => T {
                text: format!("srem({a}, {})", arg(self)?.text),
                boolean: false,
            },
            "ult" | "ule" | "slt" | "sle" => {
                let op = match m {
                    "ult" => "<u",
                    "ule" => "<=u",
                    "slt" => "<s",
                    _ => "<=s",
                };
                T {
                    text: format!("({a} {op} {})", arg(self)?.text),
                    boolean: true,
                }
            }
            "toNat" => T {
                text: a,
                boolean: false,
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
                Ok(T {
                    text: n,
                    boolean: false,
                })
            }
            Some(Tok::Ident(name)) => {
                self.at += 1;
                match name.as_str() {
                    "true" | "false" => Ok(T {
                        text: name,
                        boolean: true,
                    }),
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
                        })
                    }
                    "decide" => {
                        let c = self.arg()?;
                        Ok(T { boolean: true, ..c })
                    }
                    "BitVec.ofBool" => {
                        let c = self.arg()?;
                        Ok(T {
                            text: c.text,
                            boolean: true,
                        })
                    }
                    "BitVec.ofNat" => {
                        let _w = self.width()?;
                        let n = self.arg()?;
                        Ok(T {
                            text: n.text,
                            boolean: false,
                        })
                    }
                    "BitVec.allOnes" => {
                        let _w = self.width()?;
                        Ok(T {
                            text: "ones".into(),
                            boolean: false,
                        })
                    }
                    "BitVec.intMin" => {
                        let _w = self.width()?;
                        Ok(T {
                            text: "smin_lit".into(),
                            boolean: false,
                        })
                    }
                    "BitVec.intMax" => {
                        let _w = self.width()?;
                        Ok(T {
                            text: "smax_lit".into(),
                            boolean: false,
                        })
                    }
                    "BitVec.zeroExtend" | "BitVec.setWidth" | "BitVec.signExtend" => {
                        let w = self.width()?;
                        let a = self.arg()?;
                        let f = if name.ends_with("signExtend") {
                            "sext"
                        } else {
                            "zext"
                        };
                        Ok(T {
                            text: format!("{f}<{w}>({})", a.text),
                            boolean: false,
                        })
                    }
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
                        })
                    }
                    _ if self.param_width(&name).is_some() => Ok(T {
                        text: name,
                        boolean: false,
                    }),
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

fn declaration(toks: &[Tok], at: &mut usize, n: usize) -> Decl {
    let mut p = Parser {
        toks,
        at: *at,
        widths: Vec::new(),
        params: Vec::new(),
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
        let mut literal_bits = 0u32;
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
                    hyps.push(format!("proves({})", strip_outer(&prop.text)));
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
            Some(t) => T {
                text: t.clone(),
                boolean: true,
            },
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
        // Literals need enough width: the widest literal in the text bounds the width variable.
        for tok in &toks[*at..p.at] {
            if let Tok::Num(s) = tok {
                let v = if let Some(h) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
                    u128::from_str_radix(h, 16).unwrap_or(u128::MAX)
                } else {
                    s.parse::<u128>().unwrap_or(u128::MAX)
                };
                literal_bits = literal_bits.max(128 - v.leading_zeros());
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
        if let Some((_, w)) = p.widths.first()
            && literal_bits > 1
        {
            let _ = write!(wher, " where {w} >= {literal_bits}");
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

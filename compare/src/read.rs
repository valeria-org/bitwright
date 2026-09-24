//! A reader for the datasets' own syntax where bitwright's parser declines a line: Python's
//! operators and precedence (`**` with a constant exponent, unary `+`), literals of any size
//! modulo 2^64 (so `-18446744073709551615` is 1), array-style names (`X[0]`), nesting deeper
//! than the parser takes, a trailing note in words (`(needs Z3)`, `(with resets = 10)`), a
//! leading label (`original = …`), and a ground truth written `(constant 123)`. It builds
//! through the context's constructors, so a line both readers take is the same node either way.

use bitwright::{BinOp, BitVec, Context, Expr, UnOp, Width};

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Num(u64),
    Name(String),
    Op(&'static str),
}

fn tokens(s: &str) -> Result<Vec<Tok>, String> {
    let b = s.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        if c.is_ascii_whitespace() {
            i += 1;
        } else if c.is_ascii_digit() {
            // Wrapping arithmetic reads a literal of any size modulo 2^64.
            let (radix, start) = if c == b'0' && matches!(b.get(i + 1), Some(b'x' | b'X')) {
                (16u64, i + 2)
            } else {
                (10, i)
            };
            let mut j = start;
            let mut v = 0u64;
            while let Some(d) = b.get(j).and_then(|&d| char::from(d).to_digit(radix as u32)) {
                v = v.wrapping_mul(radix).wrapping_add(u64::from(d));
                j += 1;
            }
            if j == start {
                return Err(format!("bad literal at byte {i}"));
            }
            out.push(Tok::Num(v));
            i = j;
        } else if c.is_ascii_alphabetic() || c == b'_' {
            let mut j = i;
            while j < b.len() && (b[j].is_ascii_alphanumeric() || b[j] == b'_') {
                j += 1;
            }
            // `X[0]`: an array element is a name of its own.
            if b.get(j) == Some(&b'[') {
                let close = s[j..].find(']').ok_or("unclosed `[`")? + j;
                j = close + 1;
            }
            out.push(Tok::Name(s[i..j].to_string()));
            i = j;
        } else {
            let two = s.get(i..i + 2).unwrap_or("");
            let op: &'static str = match two {
                "**" => "**",
                "<<" => "<<",
                ">>" => ">>",
                _ => match c {
                    b'+' => "+",
                    b'-' => "-",
                    b'*' => "*",
                    b'&' => "&",
                    b'|' => "|",
                    b'^' => "^",
                    b'~' => "~",
                    b'(' => "(",
                    b')' => ")",
                    _ => return Err(format!("unexpected `{}` at byte {i}", char::from(c))),
                },
            };
            out.push(Tok::Op(op));
            i += op.len();
        }
    }
    Ok(out)
}

/// The expression in `s`: a trailing note in words (` (needs Z3)`: a word of letters, a space,
/// and no operator), a leading label (`original = `) and a `(constant …)` wrapper removed.
fn strip_notes(s: &str) -> &str {
    let mut t = s.trim();
    if let Some(inner) = t
        .strip_prefix("(constant ")
        .and_then(|r| r.strip_suffix(')'))
    {
        return inner.trim();
    }
    if let Some(body) = t.strip_suffix(')')
        && let Some(open) = body.rfind('(')
    {
        let inner = &body[open + 1..];
        let word = inner.split_whitespace().next().unwrap_or("");
        if word.len() >= 2
            && word.chars().all(|c| c.is_ascii_alphabetic())
            && inner.contains(' ')
            && !inner.chars().any(|c| "&|^~*+-<>".contains(c))
        {
            t = t[..open].trim_end();
        }
    }
    if let Some(eq) = t.find('=') {
        let label = t[..eq].trim();
        if !label.is_empty()
            && label.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
            && !t[eq + 1..].starts_with('=')
        {
            t = t[eq + 1..].trim_start();
        }
    }
    t
}

struct Reader<'a> {
    cx: &'a mut Context,
    toks: Vec<Tok>,
    at: usize,
    w: Width,
}

impl Reader<'_> {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.at)
    }

    fn next(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.at).cloned();
        self.at += 1;
        t
    }

    fn expect(&mut self, op: &str) -> Result<(), String> {
        match self.next() {
            Some(Tok::Op(o)) if o == op => Ok(()),
            other => Err(format!("expected `{op}`, found {other:?}")),
        }
    }

    fn err<T>(&self, e: bitwright::Error) -> Result<T, String> {
        Err(e.to_string())
    }

    /// Python's binding powers: `|` < `^` < `&` < shifts < `+ -` < `*` < unary < `**`.
    fn infix(op: &str) -> Option<(u8, u8)> {
        Some(match op {
            "|" => (1, 2),
            "^" => (3, 4),
            "&" => (5, 6),
            "<<" | ">>" => (7, 8),
            "+" | "-" => (9, 10),
            "*" => (11, 12),
            // Right-associative, and tighter than a unary operator on its left.
            "**" => (16, 15),
            _ => return None,
        })
    }

    const UNARY: u8 = 13;

    fn expr(&mut self, min: u8) -> Result<Expr, String> {
        let mut lhs = match self.next() {
            Some(Tok::Num(v)) => match self.cx.constant(&BitVec::wrapping_from_u64(self.w, v)) {
                Ok(e) => e,
                Err(e) => return self.err(e),
            },
            Some(Tok::Name(n)) => match self.cx.symbol(n.as_str(), self.w) {
                Ok(e) => e,
                Err(e) => return self.err(e),
            },
            Some(Tok::Op("(")) => {
                let e = self.expr(0)?;
                self.expect(")")?;
                e
            }
            Some(Tok::Op("+")) => self.expr(Self::UNARY)?,
            Some(Tok::Op(op @ ("-" | "~"))) => {
                let a = self.expr(Self::UNARY)?;
                let u = if op == "-" { UnOp::Neg } else { UnOp::Not };
                match self.cx.un(u, a) {
                    Ok(e) => e,
                    Err(e) => return self.err(e),
                }
            }
            other => return Err(format!("expected an expression, found {other:?}")),
        };
        loop {
            let op = match self.peek() {
                Some(Tok::Op(o)) if *o != "(" && *o != ")" && *o != "~" => *o,
                _ => break,
            };
            let Some((l, r)) = Self::infix(op) else {
                break;
            };
            if l < min {
                break;
            }
            self.at += 1;
            if op == "**" {
                // A constant exponent: repeated multiplication.
                let k = match self.next() {
                    Some(Tok::Num(k)) => k,
                    Some(Tok::Op("(")) => match (self.next(), self.next()) {
                        (Some(Tok::Num(k)), Some(Tok::Op(")"))) => k,
                        _ => return Err("`**` needs a constant exponent".into()),
                    },
                    _ => return Err("`**` needs a constant exponent".into()),
                };
                lhs = self.power(lhs, k)?;
                continue;
            }
            let rhs = self.expr(r)?;
            let b = match op {
                "|" => BinOp::Or,
                "^" => BinOp::Xor,
                "&" => BinOp::And,
                "<<" => BinOp::Shl,
                // The datasets' values are unsigned: `>>` is logical.
                ">>" => BinOp::LShr,
                "+" => BinOp::Add,
                "-" => BinOp::Sub,
                _ => BinOp::Mul,
            };
            lhs = match self.cx.bin(b, lhs, rhs) {
                Ok(e) => e,
                Err(e) => return self.err(e),
            };
        }
        Ok(lhs)
    }

    fn power(&mut self, x: Expr, k: u64) -> Result<Expr, String> {
        if k > 64 {
            return Err(format!("exponent {k} too large"));
        }
        let mut acc = match self.cx.constant(&BitVec::one(self.w)) {
            Ok(e) => e,
            Err(e) => return self.err(e),
        };
        for _ in 0..k {
            acc = match self.cx.bin(BinOp::Mul, acc, x) {
                Ok(e) => e,
                Err(e) => return self.err(e),
            };
        }
        Ok(acc)
    }
}

/// Reads `s` as the datasets write it, at width `w`.
pub fn read(cx: &mut Context, s: &str, w: Width) -> Result<Expr, String> {
    let toks = tokens(strip_notes(s))?;
    let mut r = Reader { cx, toks, at: 0, w };
    let e = r.expr(0)?;
    if r.at != r.toks.len() {
        return Err(format!("unexpected {:?} after the expression", r.peek()));
    }
    Ok(e)
}

#[cfg(test)]
mod tests {
    use super::read;
    use bitwright::{Context, Expr, ParseOptions, Width};

    /// `a` read by the fallback reader and `b` by bitwright's parser: the same node.
    fn same(a: &str, b: &str) {
        let mut cx = Context::new();
        let x: Expr = read(&mut cx, a, Width::W64).unwrap();
        let y = cx.parse(b, &ParseOptions::width(Width::W64)).unwrap();
        assert_eq!(x, y, "{a} read as {}", cx.display(x));
    }

    #[test]
    fn python_precedence() {
        // Shifts bind looser than `+`, `&` tighter than `^` and `|`, `**` tighter than unary.
        same("a + b << 1", "(a + b) << 1");
        same("a | b ^ c & d", "a | (b ^ (c & d))");
        same("-x**2", "-(x * x)");
        same("x ** 3 * y", "x * x * x * y");
        same("+x - ~y", "x - ~y");
        same("x >> 2", "x >>u 2");
    }

    #[test]
    fn literals_names_and_notes() {
        // Literals wrap modulo 2^64.
        same("-18446744073709551615 * x", "1 * x");
        same("0x10000000000000001 + x", "1 + x");
        same("x + y (needs Z3)", "x + y");
        same("original = x & y", "x & y");
        same("(constant 123)", "123");
    }

    #[test]
    fn array_elements_are_names() {
        let mut cx = Context::new();
        let a = read(&mut cx, "X[0] + X[1]", Width::W64).unwrap();
        let b = read(&mut cx, "X[1] + X[0]", Width::W64).unwrap();
        let c = read(&mut cx, "X[0] + X[0]", Width::W64).unwrap();
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(cx.symbols_in(&[a]).unwrap().len(), 2);
    }

    #[test]
    fn declines_what_it_cannot_read() {
        let mut cx = Context::new();
        assert!(read(&mut cx, "x ** y", Width::W64).is_err());
        assert!(read(&mut cx, "x + ", Width::W64).is_err());
        assert!(read(&mut cx, "(x + y", Width::W64).is_err());
        assert!(read(&mut cx, "x $ y", Width::W64).is_err());
    }
}

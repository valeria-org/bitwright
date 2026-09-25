//! Tokens of a line of either syntax (both put one statement on a line).

/// A token.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Tok {
    /// A word: a keyword, a type, an opcode, a constant's or a function's name.
    Ident(String),
    /// `%name` (the name).
    Local(String),
    /// `@name` (the name).
    Global(String),
    /// A number as written (no sign).
    Num(String),
    /// A quoted string.
    Str(String),
    /// Punctuation or an operator.
    P(&'static str),
}

impl core::fmt::Display for Tok {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Tok::Ident(s) | Tok::Num(s) => f.write_str(s),
            Tok::Local(s) => write!(f, "%{s}"),
            Tok::Global(s) => write!(f, "@{s}"),
            Tok::Str(s) => write!(f, "\"{s}\""),
            Tok::P(p) => f.write_str(p),
        }
    }
}

/// An error at a line (1-based).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SyntaxError {
    /// The line.
    pub line: usize,
    /// What is wrong.
    pub message: String,
}

impl core::fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "line {}: {}", self.line, self.message)
    }
}

impl std::error::Error for SyntaxError {}

const PUNCT: &[&str] = &[
    "=>", "&&", "||", "==", "!=", "<=", ">=", "<<", ">>", "...", "=", ",", "(", ")", "[", "]", "{",
    "}", "<", ">", ":", "*", "+", "-", "&", "|", "^", "~", "!", "/", "%", "#",
];

fn name_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '$')
}

/// The text of a line without its comment (`;` to the end, outside quotes).
pub(crate) fn strip_comment(line: &str) -> &str {
    let mut quoted = false;
    for (i, c) in line.char_indices() {
        match c {
            '"' => quoted = !quoted,
            ';' if !quoted => return &line[..i],
            _ => {}
        }
    }
    line
}

/// The tokens of a line (its comment already removed).
pub(crate) fn lex(line: &str, n: usize) -> Result<Vec<Tok>, SyntaxError> {
    let err = |m: String| SyntaxError {
        line: n,
        message: m,
    };
    let chars: Vec<char> = line.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    let word = |i: &mut usize| {
        let s = *i;
        while *i < chars.len() && name_char(chars[*i]) {
            *i += 1;
        }
        chars[s..*i].iter().collect::<String>()
    };
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c == '%' || c == '@' {
            let sigil = c;
            i += 1;
            let name = if i < chars.len() && chars[i] == '"' {
                i += 1;
                let s = i;
                while i < chars.len() && chars[i] != '"' {
                    i += 1;
                }
                if i == chars.len() {
                    return Err(err("unterminated quoted name".into()));
                }
                i += 1;
                chars[s..i - 1].iter().collect()
            } else if i < chars.len() && (name_char(chars[i]) || chars[i] == '-') {
                let s = i;
                i += 1;
                while i < chars.len() && (name_char(chars[i]) || chars[i] == '-') {
                    i += 1;
                }
                chars[s..i].iter().collect()
            } else {
                if sigil == '%' {
                    out.push(Tok::P("%"));
                    continue;
                }
                return Err(err("`@` without a name".into()));
            };
            out.push(if sigil == '%' {
                Tok::Local(name)
            } else {
                Tok::Global(name)
            });
            continue;
        }
        if c.is_ascii_digit() {
            let s = i;
            if c == '0' && i + 1 < chars.len() && (chars[i + 1] == 'x' || chars[i + 1] == 'X') {
                i += 2;
                // A floating-point format letter (`0xH…`, `0xK…`, …).
                if i < chars.len() && matches!(chars[i], 'H' | 'K' | 'L' | 'M' | 'R') {
                    i += 1;
                }
                while i < chars.len() && chars[i].is_ascii_hexdigit() {
                    i += 1;
                }
            } else {
                while i < chars.len() && chars[i].is_ascii_digit() {
                    i += 1;
                }
                if i < chars.len() && chars[i] == '.' {
                    i += 1;
                    while i < chars.len() && chars[i].is_ascii_digit() {
                        i += 1;
                    }
                }
                if i < chars.len() && (chars[i] == 'e' || chars[i] == 'E') {
                    let mut j = i + 1;
                    if j < chars.len() && (chars[j] == '+' || chars[j] == '-') {
                        j += 1;
                    }
                    if j < chars.len() && chars[j].is_ascii_digit() {
                        i = j;
                        while i < chars.len() && chars[i].is_ascii_digit() {
                            i += 1;
                        }
                    }
                }
            }
            out.push(Tok::Num(chars[s..i].iter().collect()));
            continue;
        }
        if c == '"' {
            i += 1;
            let s = i;
            while i < chars.len() && chars[i] != '"' {
                i += 1;
            }
            if i == chars.len() {
                return Err(err("unterminated string".into()));
            }
            out.push(Tok::Str(chars[s..i].iter().collect()));
            i += 1;
            continue;
        }
        if c.is_ascii_alphabetic() || c == '_' || c == '$' {
            let w = word(&mut i);
            // `u<`, `u<=`, `u>`, `u>=`, `u>>`: unsigned operators of preconditions.
            if w == "u" && i < chars.len() && (chars[i] == '<' || chars[i] == '>') {
                let rest: String = chars[i..chars.len().min(i + 2)].iter().collect();
                let op = if rest.starts_with(">>") {
                    "u>>"
                } else if rest.starts_with("<=") {
                    "u<="
                } else if rest.starts_with(">=") {
                    "u>="
                } else if rest.starts_with('<') {
                    "u<"
                } else {
                    "u>"
                };
                i += op.len() - 1;
                out.push(Tok::P(op));
                continue;
            }
            out.push(Tok::Ident(w));
            continue;
        }
        // `/u`: unsigned division of constant expressions.
        if c == '/' && i + 1 < chars.len() && chars[i + 1] == 'u' {
            let after = chars.get(i + 2).copied();
            if !after.is_some_and(name_char) {
                out.push(Tok::P("/u"));
                i += 2;
                continue;
            }
        }
        let rest: String = chars[i..chars.len().min(i + 3)].iter().collect();
        match PUNCT.iter().find(|p| rest.starts_with(*p)) {
            Some(p) => {
                out.push(Tok::P(p));
                i += p.chars().count();
            }
            None => return Err(err(format!("unexpected character `{c}`"))),
        }
    }
    Ok(out)
}

/// A cursor over one line's tokens.
pub(crate) struct Cursor<'t> {
    pub(crate) toks: &'t [Tok],
    pub(crate) pos: usize,
    pub(crate) line: usize,
}

impl<'t> Cursor<'t> {
    pub(crate) fn new(toks: &'t [Tok], line: usize) -> Self {
        Cursor { toks, pos: 0, line }
    }

    pub(crate) fn err<T>(&self, m: impl Into<String>) -> Result<T, SyntaxError> {
        Err(SyntaxError {
            line: self.line,
            message: m.into(),
        })
    }

    pub(crate) fn peek(&self) -> Option<&'t Tok> {
        self.toks.get(self.pos)
    }

    pub(crate) fn peek_at(&self, k: usize) -> Option<&'t Tok> {
        self.toks.get(self.pos + k)
    }

    pub(crate) fn next(&mut self) -> Option<&'t Tok> {
        let t = self.toks.get(self.pos);
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    pub(crate) fn at_end(&self) -> bool {
        self.pos >= self.toks.len()
    }

    /// Consumes punctuation `p` if it is next.
    pub(crate) fn eat(&mut self, p: &str) -> bool {
        if matches!(self.peek(), Some(Tok::P(q)) if *q == p) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    /// Consumes the word `w` if it is next.
    pub(crate) fn eat_word(&mut self, w: &str) -> bool {
        if matches!(self.peek(), Some(Tok::Ident(q)) if q == w) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    /// The end of a statement: nothing left, or only metadata (`, !dbg !7`).
    pub(crate) fn end(&self) -> Result<(), SyntaxError> {
        match (self.peek(), self.peek_at(1)) {
            (None, _) | (Some(Tok::P(",")), Some(Tok::P("!"))) => Ok(()),
            (Some(t), _) => self.err(format!("unexpected `{t}`")),
        }
    }

    pub(crate) fn expect(&mut self, p: &str) -> Result<(), SyntaxError> {
        if self.eat(p) {
            Ok(())
        } else {
            let found = self
                .peek()
                .map_or("the end of the line".to_string(), |t| format!("`{t}`"));
            self.err(format!("expected `{p}`, found {found}"))
        }
    }

    /// The next word, if it is one.
    pub(crate) fn word(&mut self) -> Option<&'t str> {
        match self.peek() {
            Some(Tok::Ident(w)) => {
                self.pos += 1;
                Some(w)
            }
            _ => None,
        }
    }

    /// The next word if it is not followed by `(` (a function call) — for flags and keywords.
    pub(crate) fn peek_word(&self) -> Option<&'t str> {
        match self.peek() {
            Some(Tok::Ident(w)) => Some(w),
            _ => None,
        }
    }
}

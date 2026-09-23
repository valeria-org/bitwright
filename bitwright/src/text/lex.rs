//! Tokenizer for the expression syntax.

use super::SyntaxError;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Tok {
    Ident(String),
    /// Digits of an integer literal (underscores removed) and the radix.
    Int(String, u32),
    /// `#123`: an integer symbol key.
    HashKey(u64),
    /// `$7`: a fresh-symbol key.
    FreshKey(u64),
    /// `%3`: a let-bound name produced by the printer.
    LetName(u32),
    /// `"name"`: a symbol with a non-identifier name.
    Str(String),
    /// `@name` or `@name[k]`: output `k` (0 if absent) of an extension operation.
    Ext(String, u8),
    Plus,
    Minus,
    Star,
    Amp,
    Pipe,
    Caret,
    Tilde,
    Shl,
    LShr,
    AShr,
    Eq,
    Ne,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge,
    LAngle,
    RAngle,
    LParen,
    RParen,
    Comma,
    Colon,
    Semi,
    Assign,
    // Rule-file tokens (only produced in rule mode).
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    /// `#[`
    AttrOpen,
    /// `=>`
    FatArrow,
    /// `<=>`
    Iff,
    AndAnd,
    OrOr,
    Bang,
    /// `%` (modulus in width constraints)
    Percent,
    /// Plain `<=` (width constraints only)
    Le,
    /// Plain `>=` (width constraints only)
    Ge,
    /// `/// text`
    Doc(String),
    Eof,
}

#[derive(Clone, Debug)]
pub(crate) struct Token {
    pub(crate) tok: Tok,
    pub(crate) start: usize,
    pub(crate) end: usize,
}

pub(crate) fn lex(src: &str) -> Result<Vec<Token>, SyntaxError> {
    lex_mode(src, false)
}

/// Tokenizes; `rules` enables the rule-file tokens (braces, `=>`, `<=>`, `&&`, `||`, `!`,
/// attributes, doc comments, `%` as an operator).
pub(crate) fn lex_mode(src: &str, rules: bool) -> Result<Vec<Token>, SyntaxError> {
    let b = src.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    let err = |at: usize, msg: &str| SyntaxError::new(msg, at, at + 1);
    while i < b.len() {
        let c = b[i];
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if c == b'/' && b.get(i + 1) == Some(&b'/') {
            let start = i;
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
            if rules && src[start..].starts_with("///") {
                out.push(Token {
                    tok: Tok::Doc(src[start + 3..i].trim().to_string()),
                    start,
                    end: i,
                });
            }
            continue;
        }
        let start = i;
        let peek = |k: usize| b.get(i + k).copied();
        if c == b'@' {
            let mut j = i + 1;
            while j < b.len() && (b[j].is_ascii_alphanumeric() || b[j] == b'_' || b[j] == b'.') {
                j += 1;
            }
            let name = src[i + 1..j].to_string();
            if name.is_empty() {
                return Err(err(i, "expected an extension operation name after `@`"));
            }
            let mut k = 0u8;
            if b.get(j) == Some(&b'[') {
                let mut e = j + 1;
                while e < b.len() && b[e].is_ascii_digit() {
                    e += 1;
                }
                if b.get(e) != Some(&b']') || e == j + 1 {
                    return Err(err(j, "expected `[output]`"));
                }
                k = src[j + 1..e]
                    .parse()
                    .map_err(|_| SyntaxError::new("output index too large", j, e))?;
                j = e + 1;
            }
            out.push(Token {
                tok: Tok::Ext(name, k),
                start,
                end: j,
            });
            i = j;
            continue;
        }
        if rules {
            let two = (c, b.get(i + 1).copied(), b.get(i + 2).copied());
            let hit = match two {
                (b'<', Some(b'='), Some(b'>')) => Some((Tok::Iff, 3)),
                (b'<', Some(b'='), c) if !matches!(c, Some(b'u' | b's')) => Some((Tok::Le, 2)),
                (b'>', Some(b'='), c) if !matches!(c, Some(b'u' | b's')) => Some((Tok::Ge, 2)),
                (b'=', Some(b'>'), _) => Some((Tok::FatArrow, 2)),
                (b'&', Some(b'&'), _) => Some((Tok::AndAnd, 2)),
                (b'|', Some(b'|'), _) => Some((Tok::OrOr, 2)),
                (b'!', Some(b'='), _) => None,
                (b'!', _, _) => Some((Tok::Bang, 1)),
                (b'#', Some(b'['), _) => Some((Tok::AttrOpen, 2)),
                (b'{', _, _) => Some((Tok::LBrace, 1)),
                (b'}', _, _) => Some((Tok::RBrace, 1)),
                (b'[', _, _) => Some((Tok::LBracket, 1)),
                (b']', _, _) => Some((Tok::RBracket, 1)),
                (b'%', Some(d), _) if !d.is_ascii_digit() => Some((Tok::Percent, 1)),
                (b'%', None, _) => Some((Tok::Percent, 1)),
                _ => None,
            };
            if let Some((tok, len)) = hit {
                i += len;
                out.push(Token { tok, start, end: i });
                continue;
            }
        }
        let (tok, len) = match c {
            b'+' => (Tok::Plus, 1),
            b'-' => (Tok::Minus, 1),
            b'*' => (Tok::Star, 1),
            b'&' => (Tok::Amp, 1),
            b'|' => (Tok::Pipe, 1),
            b'^' => (Tok::Caret, 1),
            b'~' => (Tok::Tilde, 1),
            b'(' => (Tok::LParen, 1),
            b')' => (Tok::RParen, 1),
            b',' => (Tok::Comma, 1),
            b':' => (Tok::Colon, 1),
            b';' => (Tok::Semi, 1),
            b'=' if peek(1) == Some(b'=') => (Tok::Eq, 2),
            b'=' => (Tok::Assign, 1),
            b'!' if peek(1) == Some(b'=') => (Tok::Ne, 2),
            b'<' => match (peek(1), peek(2)) {
                (Some(b'<'), _) => (Tok::Shl, 2),
                (Some(b'='), Some(b'u')) => (Tok::Ule, 3),
                (Some(b'='), Some(b's')) => (Tok::Sle, 3),
                (Some(b'u'), _) => (Tok::Ult, 2),
                (Some(b's'), _) => (Tok::Slt, 2),
                (Some(b'='), _) => {
                    return Err(err(i, "write `<=u` (unsigned) or `<=s` (signed)"));
                }
                _ => (Tok::LAngle, 1),
            },
            b'>' => match (peek(1), peek(2)) {
                (Some(b'>'), Some(b'u')) => (Tok::LShr, 3),
                (Some(b'>'), Some(b's')) => (Tok::AShr, 3),
                (Some(b'>'), _) => {
                    return Err(err(
                        i,
                        "ambiguous shift: write `>>u` (logical) or `>>s` (arithmetic)",
                    ));
                }
                (Some(b'='), Some(b'u')) => (Tok::Uge, 3),
                (Some(b'='), Some(b's')) => (Tok::Sge, 3),
                (Some(b'u'), _) => (Tok::Ugt, 2),
                (Some(b's'), _) => (Tok::Sgt, 2),
                (Some(b'='), _) => {
                    return Err(err(i, "write `>=u` (unsigned) or `>=s` (signed)"));
                }
                _ => (Tok::RAngle, 1),
            },
            b'#' | b'$' | b'%' => {
                let mut j = i + 1;
                while j < b.len() && b[j].is_ascii_digit() {
                    j += 1;
                }
                let digits = &src[i + 1..j];
                if digits.is_empty() {
                    return Err(err(i, "expected digits"));
                }
                let tok = match c {
                    b'#' => Tok::HashKey(
                        digits
                            .parse()
                            .map_err(|_| SyntaxError::new("key too large", i, j))?,
                    ),
                    b'$' => Tok::FreshKey(
                        digits
                            .parse()
                            .map_err(|_| SyntaxError::new("key too large", i, j))?,
                    ),
                    _ => Tok::LetName(
                        digits
                            .parse()
                            .map_err(|_| SyntaxError::new("name too large", i, j))?,
                    ),
                };
                (tok, j - i)
            }
            b'"' => {
                let mut j = i + 1;
                let mut s = String::new();
                loop {
                    match b.get(j) {
                        None => return Err(SyntaxError::new("unterminated string", i, j)),
                        Some(b'"') => break,
                        Some(b'\\') => {
                            match b.get(j + 1) {
                                Some(b'"') => s.push('"'),
                                Some(b'\\') => s.push('\\'),
                                Some(b'n') => s.push('\n'),
                                Some(b't') => s.push('\t'),
                                Some(b'r') => s.push('\r'),
                                Some(b'0') => s.push('\0'),
                                Some(b'u') if b.get(j + 2) == Some(&b'{') => {
                                    let close = src[j + 3..]
                                        .find('}')
                                        .ok_or_else(|| err(j, "unterminated \\u{…} escape"))?;
                                    let hex = &src[j + 3..j + 3 + close];
                                    let ch = u32::from_str_radix(hex, 16)
                                        .ok()
                                        .and_then(char::from_u32)
                                        .ok_or_else(|| err(j, "invalid \\u{…} escape"))?;
                                    s.push(ch);
                                    j += 3 + close + 1;
                                    continue;
                                }
                                _ => return Err(err(j, "unsupported escape")),
                            }
                            j += 2;
                        }
                        Some(_) => {
                            let ch = src[j..].chars().next().unwrap_or('\u{fffd}');
                            s.push(ch);
                            j += ch.len_utf8();
                        }
                    }
                }
                (Tok::Str(s), j + 1 - i)
            }
            b'0'..=b'9' => {
                let (radix, body) = if c == b'0' && matches!(peek(1), Some(b'x' | b'X')) {
                    (16, i + 2)
                } else if c == b'0' && matches!(peek(1), Some(b'b' | b'B')) {
                    (2, i + 2)
                } else {
                    (10, i)
                };
                let mut j = body;
                let mut digits = String::new();
                while j < b.len() && (b[j].is_ascii_alphanumeric() || b[j] == b'_') {
                    if b[j] != b'_' {
                        if !(b[j] as char).is_digit(radix) {
                            return Err(err(j, "invalid digit"));
                        }
                        digits.push(b[j] as char);
                    }
                    j += 1;
                }
                if digits.is_empty() {
                    return Err(err(j, "expected digits"));
                }
                (Tok::Int(digits, radix), j - i)
            }
            c if c.is_ascii_alphabetic() || c == b'_' => {
                let mut j = i;
                while j < b.len() && (b[j].is_ascii_alphanumeric() || b[j] == b'_' || b[j] == b'.')
                {
                    j += 1;
                }
                (Tok::Ident(src[i..j].to_string()), j - i)
            }
            _ => {
                let ch = src[i..].chars().next().unwrap_or('?');
                return Err(SyntaxError::new(
                    &format!("unexpected character `{ch}`"),
                    i,
                    i + ch.len_utf8(),
                ));
            }
        };
        i += len;
        out.push(Token { tok, start, end: i });
    }
    out.push(Token {
        tok: Tok::Eof,
        start: b.len(),
        end: b.len(),
    });
    Ok(out)
}

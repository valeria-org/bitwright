//! Diagnostics with stable codes, byte spans and a rustc-style renderer.

use core::fmt;

/// How serious a diagnostic is.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[non_exhaustive]
pub enum Level {
    /// Informational.
    Note,
    /// Suspicious but accepted.
    Warning,
    /// Rejects the program.
    Error,
}

/// A compiler or checker message.
#[derive(Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub struct Diagnostic {
    /// Stable code, e.g. `BW0301`.
    pub code: &'static str,
    /// Severity.
    pub level: Level,
    /// The message.
    pub message: String,
    /// Byte span in the source.
    pub span: (usize, usize),
    /// Extra lines (counterexamples, hints).
    pub notes: Vec<String>,
}

impl Diagnostic {
    pub(crate) fn error(
        code: &'static str,
        message: impl Into<String>,
        span: (usize, usize),
    ) -> Self {
        Diagnostic {
            code,
            level: Level::Error,
            message: message.into(),
            span,
            notes: Vec::new(),
        }
    }

    pub(crate) fn warning(
        code: &'static str,
        message: impl Into<String>,
        span: (usize, usize),
    ) -> Self {
        Diagnostic {
            code,
            level: Level::Warning,
            message: message.into(),
            span,
            notes: Vec::new(),
        }
    }

    pub(crate) fn note_level(
        code: &'static str,
        message: impl Into<String>,
        span: (usize, usize),
    ) -> Self {
        Diagnostic {
            code,
            level: Level::Note,
            message: message.into(),
            span,
            notes: Vec::new(),
        }
    }

    #[allow(dead_code)]
    pub(crate) fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    /// Renders the diagnostic against its source, rustc style.
    pub fn render(&self, file: &str, src: &str) -> String {
        let (line, col, text) = locate(src, self.span.0);
        let level = match self.level {
            Level::Error => "error",
            Level::Warning => "warning",
            Level::Note => "note",
        };
        let width = self.span.1.saturating_sub(self.span.0).max(1);
        let width = width.min(text.len().saturating_sub(col - 1).max(1));
        let gutter = format!("{line}").len();
        let mut out = format!(
            "{level}[{}]: {}\n{:gutter$}--> {file}:{line}:{col}\n{:gutter$} |\n{line} | {text}\n{:gutter$} | {}{}\n",
            self.code,
            self.message,
            "",
            "",
            "",
            " ".repeat(col - 1),
            "^".repeat(width),
        );
        for n in &self.notes {
            out.push_str(&format!("{:gutter$} = {n}\n", ""));
        }
        out
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}] {} (at bytes {}..{})",
            self.code, self.message, self.span.0, self.span.1
        )?;
        for n in &self.notes {
            write!(f, "; {n}")?;
        }
        Ok(())
    }
}

/// 1-based line and column of a byte offset, and the line's text.
fn locate(src: &str, at: usize) -> (usize, usize, &str) {
    let at = at.min(src.len());
    let line_start = src[..at].rfind('\n').map_or(0, |i| i + 1);
    let line_end = src[at..].find('\n').map_or(src.len(), |i| at + i);
    let line = src[..at].matches('\n').count() + 1;
    let col = src[line_start..at].chars().count() + 1;
    (line, col, &src[line_start..line_end])
}

/// Failure to compile a rule program: every error and warning found.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct CompileError {
    /// The diagnostics (at least one is an error).
    pub diagnostics: Vec<Diagnostic>,
}

impl CompileError {
    /// Renders every diagnostic against the source.
    pub fn render(&self, file: &str, src: &str) -> String {
        self.diagnostics
            .iter()
            .map(|d| d.render(file, src))
            .collect()
    }
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for d in &self.diagnostics {
            writeln!(f, "{d}")?;
        }
        Ok(())
    }
}

impl std::error::Error for CompileError {}

/// What a diagnostic code means and how to fix it, for every code the compiler emits.
const EXPLANATIONS: &[(&str, &str)] = &[
    (
        "BW0001",
        "Syntax error. The rule file does not parse: a missing `=>` (rules) or `<=>` \
         (identities), a stray token, or an unterminated expression or string. The message \
         names what was expected at the marked position.",
    ),
    (
        "BW0002",
        "Unknown or misplaced attribute. Attributes (`#[example(..)]`, `#[allow(..)]`) and doc \
         comments belong on rules, not groups; `#[allow]` accepts only the allowable lints \
         (BW0402, BW0407). Errors can never be allowed.",
    ),
    (
        "BW0003",
        "Missing edition header. A rule file starts with `bitwright 1;`, so that a later \
         edition of the language can change meaning without misreading old files.",
    ),
    (
        "BW0004",
        "Duplicate definition. A group or a rule within a group is defined twice. Rule names \
         are `group::name` and must be unique, because proof ledgers and statistics key on them.",
    ),
    (
        "BW0100",
        "Limit exceeded. The source, a rule, an expression's nesting depth or a width \
         expression's magnitude is over the compiler's limits (`CompileLimits`). Split the \
         rule, or raise the limits when compiling trusted input.",
    ),
    (
        "BW0101",
        "Sort or width mismatch. Operand widths differ, a concatenation does not add up, a \
         condition is used as a value (combine conditions with `&&`, `||`, `!` instead), a \
         guard is not a condition or 1-bit value, or a literal's width cannot be inferred \
         (write `1:W`).",
    ),
    (
        "BW0102",
        "Bad width variable or constraint. A width is not one of the rule's width variables, \
         a width variable is repeated (at most 3 are allowed), or a `where` constraint is \
         malformed (`a op b` with `==`, `!=`, `<`, `>`, `<=`, `>=`, or `a % m == r`).",
    ),
    (
        "BW0103",
        "Bad name, literal or parameter. An unknown name, a reserved or repeated parameter or \
         `let` name, a literal over 512 bits, a `let` value in the pattern, or a parameter that \
         does not occur in the pattern (the template could not be instantiated).",
    ),
    (
        "BW0104",
        "Malformed predicate. Fact predicates take a parameter first (`zero_bits(x, m)`), \
         `disjoint` takes two parameters, `proves` takes one comparison of parameters, `let`s \
         and literals (`proves(b != c)`), and predicates belong in the guard after `if`.",
    ),
    (
        "BW0105",
        "Impure constant computation. A mask, a constant predicate's operand or a `let` may use \
         only constant parameters, literals and earlier `let`s, because it is computed when the \
         rule matches. A condition on a non-constant value must be a fact predicate, for \
         example `proves(x <u y)`.",
    ),
    (
        "BW0106",
        "Negated fact predicate. Facts only prove, they never refute: `!zero_bits(x, m)` would \
         hold whenever the fact engine merely failed to prove `zero_bits`, which is unsound. \
         Restate the condition positively.",
    ),
    (
        "BW0107",
        "Ill-typed at an admitted width. At some width assignment the constraints allow and \
         the pattern matches, a literal or width value does not fit, an extract is out of \
         range, or an extension narrows. Add a `where` constraint that excludes it. Also \
         reported when the pattern can never match at any width.",
    ),
    (
        "BW0302",
        "Non-terminating rule. A `rule` must strictly decrease the termination order (a \
         Knuth-Bendix order over its stored form) and may not duplicate a variable into more \
         occurrences than the pattern has, or it could loop. Make the result smaller, or \
         declare an `identity` (`<=>`), which equality saturation may use in both directions.",
    ),
    (
        "BW0304",
        "Invalid identity. An identity is an unconditional equation `lhs <=> rhs`: no guard, \
         no `let`, no capture kinds (`const`, `sym`, `nonconst`), no extension operations, \
         and every parameter on both sides.",
    ),
    (
        "BW0402",
        "Unreachable rule (allowable). Construction canonicalization already rewrites every \
         instance of the pattern (a constant on the left, `ugt` stored as a swapped `ult`, an \
         all-constant term folded), so the rule can never fire as written. Write the pattern \
         in stored form, or allow it where the rule serves another purpose (equality \
         saturation).",
    ),
    (
        "BW0407",
        "No example (allowable note). Every rule should carry at least one \
         `#[example(\"input\" => \"output\")]`. The checker applies the rule to each input \
         and compares the result with the output (`check::check_examples`, reported by \
         `bitwright check`); the built-in corpus has one for every rule.",
    ),
    (
        "BW0409",
        "Search-only identity (note). The identity does not decrease the termination order in \
         either direction, so the directed engine never uses it; only equality saturation does.",
    ),
];

/// What diagnostic `code` (for example `"BW0302"`) means and how to fix it.
pub fn explain(code: &str) -> Option<&'static str> {
    EXPLANATIONS
        .iter()
        .find(|(c, _)| c.eq_ignore_ascii_case(code))
        .map(|&(_, e)| e)
}

#[cfg(test)]
mod tests {
    #[test]
    fn every_emitted_code_is_explained() {
        let sources = [
            include_str!("compile.rs"),
            include_str!("ledger.rs"),
            include_str!("mod.rs"),
            include_str!("../check/mod.rs"),
        ];
        let mut seen = 0;
        for src in sources {
            for (i, _) in src.match_indices("\"BW") {
                let code = &src[i + 1..i + 7];
                if code.len() == 6 && code[2..].bytes().all(|b| b.is_ascii_digit()) {
                    assert!(super::explain(code).is_some(), "{code} has no explanation");
                    seen += 1;
                }
            }
        }
        assert!(seen > 50, "{seen}");
        assert!(super::explain("bw0302").is_some());
        assert!(super::explain("BW9999").is_none());
    }
}

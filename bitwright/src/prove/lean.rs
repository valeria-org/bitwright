//! Unsatisfiable sets of predicates as Lean 4 theorems, for Lean to prove again.

use core::fmt::Write;

use crate::SymbolKey;
use crate::error::Error;
use crate::expr::{Context, Expr, View};
use crate::ops::{BinOp, CmpOp, UnOp};

/// The most nodes (as a tree) a theorem's statement may have: shared subterms are written
/// out, and a statement Lean cannot read in reasonable time is no certificate.
const MAX_TREE: u32 = 20_000;

/// The claim that the 1-bit `predicates` do not hold together, as a Lean 4 theorem over
/// `BitVec` with the proof `by bv_decide`: a file `lean` checks on its own, with nothing of
/// bitwright in what it trusts. `comment` is written above the theorem (how the claim was
/// reached, say).
///
/// The statement is the predicates as given, each a bit-vector term equal to `1#1`, so it
/// can be read against what was asked; whether Lean's proof by bit-blasting succeeds is for
/// Lean to say, and for arithmetic at 64 bits it often does not: a word-level proof is not
/// something `bv_decide` finds again. An error names what Lean's `BitVec` has no counterpart
/// for (bit counts, byte swaps, the high half of a product, rotations by a variable,
/// floating point, extension operations) or says the statement is too large.
/// Rotations by a constant are written with `BitVec.rotateLeft` and `rotateRight`.
///
/// ```
/// use bitwright::{Context, ParseOptions, Width};
///
/// let mut cx = Context::new();
/// let o = ParseOptions::width(Width::W8);
/// let (a, b) = (cx.parse("x * 3 == 9", &o)?, cx.parse("x >u 3", &o)?);
/// let lean = bitwright::prove::lean_theorem(&mut cx, "no_other_root", &[a, b], "")?;
/// assert_eq!(
///     lean,
///     "import Std.Tactic.BVDecide\n\n\
///      theorem no_other_root (x : BitVec 8) :\n    \
///      ¬ ((BitVec.ofBool ((x * 3#8) == 9#8)) = 1#1 ∧\n      \
///      (BitVec.ofBool (BitVec.ult 3#8 x)) = 1#1) := by\n  bv_decide\n"
/// );
/// # Ok::<(), bitwright::Error>(())
/// ```
pub fn lean_theorem(
    cx: &mut Context,
    name: &str,
    predicates: &[Expr],
    comment: &str,
) -> Result<String, Error> {
    let unsupported = |what: &str| Error::Unsupported(format!("no Lean theorem: {what}"));
    if predicates.is_empty() {
        return Err(unsupported("nothing to state"));
    }
    let mut size = 0u32;
    for &p in predicates {
        if cx.width(p)?.bits() != 1 {
            return Err(unsupported("a predicate is not 1 bit"));
        }
        size = size.saturating_add(cx.tree_size(p)?);
    }
    if size > MAX_TREE {
        return Err(unsupported("the statement is too large to write out"));
    }
    let names = symbol_names(cx, predicates)?;
    let mut out = String::from("import Std.Tactic.BVDecide\n\n");
    for line in comment.lines() {
        let _ = writeln!(out, "-- {line}");
    }
    let _ = write!(out, "theorem {name}");
    for (_, ident, w) in &names {
        let _ = write!(out, " ({ident} : BitVec {w})");
    }
    out.push_str(" :\n    ¬ (");
    for (k, &p) in predicates.iter().enumerate() {
        if k > 0 {
            out.push_str(" ∧\n      ");
        }
        let t = term(cx, p, &names)?;
        let _ = write!(out, "{t} = 1#1");
    }
    out.push_str(") := by\n  bv_decide\n");
    Ok(out)
}

/// `a = b` for every value of the symbols, as a Lean 4 theorem (without the import line)
/// with the proof `by bv_decide`.
pub(crate) fn lean_equation(
    cx: &mut Context,
    name: &str,
    a: Expr,
    b: Expr,
) -> Result<String, Error> {
    let unsupported = |what: &str| Error::Unsupported(format!("no Lean theorem: {what}"));
    if cx.tree_size(a)?.saturating_add(cx.tree_size(b)?) > MAX_TREE {
        return Err(unsupported("the statement is too large to write out"));
    }
    let names = symbol_names(cx, &[a, b])?;
    let mut out = format!("theorem {name}");
    for (_, ident, w) in &names {
        let _ = write!(out, " ({ident} : BitVec {w})");
    }
    let (x, y) = (term(cx, a, &names)?, term(cx, b, &names)?);
    let _ = write!(out, " :\n    {x} = {y} := by\n  bv_decide\n");
    Ok(out)
}

/// The symbols of `es`, each with a Lean identifier that is its alone, and its width.
fn symbol_names(cx: &mut Context, es: &[Expr]) -> Result<Vec<(SymbolKey, String, u16)>, Error> {
    let mut names: Vec<(SymbolKey, String, u16)> = Vec::new();
    for id in cx.symbols_in(es)? {
        let (Some(key), Some(w)) = (cx.symbol_key(id).cloned(), cx.symbol_width(id)) else {
            continue;
        };
        let mut ident: String = match &key {
            SymbolKey::Str(s) => (s.chars())
                .map(|c| {
                    if c.is_ascii_alphanumeric() || c == '_' {
                        c
                    } else {
                        '_'
                    }
                })
                .collect(),
            SymbolKey::U64(k) => format!("v{k}"),
            SymbolKey::Fresh(k) => format!("fresh{k}"),
        };
        if !ident.starts_with(|c: char| c.is_ascii_alphabetic()) {
            ident.insert(0, 'v');
        }
        while names.iter().any(|(_, n, _)| *n == ident) || RESERVED.contains(&ident.as_str()) {
            ident.push('\'');
        }
        names.push((key, ident, w.bits()));
    }
    Ok(names)
}

/// Identifiers a symbol must not be written as.
const RESERVED: [&str; 12] = [
    "if", "then", "else", "let", "fun", "by", "theorem", "import", "at", "do", "in", "have",
];

/// `e` as a Lean term of type `BitVec w`, fully parenthesized where it is not atomic.
fn term(cx: &Context, e: Expr, names: &[(SymbolKey, String, u16)]) -> Result<String, Error> {
    let unsupported = |what: &str| Error::Unsupported(format!("no Lean theorem: {what}"));
    let w = cx.width(e)?.bits();
    let t = |x: Expr| term(cx, x, names);
    Ok(match cx.view(e)? {
        View::Const(v) => {
            // Decimal: any width, no leading zeros to count.
            let mut digits = vec![0u8];
            for limb in v.limbs().iter().rev() {
                for bit in (0..64).rev() {
                    let mut carry = (limb >> bit & 1) as u8;
                    for d in digits.iter_mut() {
                        let x = *d * 2 + carry;
                        *d = x % 10;
                        carry = x / 10;
                    }
                    if carry > 0 {
                        digits.push(carry);
                    }
                }
            }
            let s: String = digits.iter().rev().map(|d| char::from(b'0' + d)).collect();
            format!("{s}#{w}")
        }
        View::Sym(id) => {
            let key = cx
                .symbol_key(id)
                .ok_or_else(|| unsupported("a symbol without a key"))?;
            (names.iter().find(|(k, _, _)| k == key))
                .map(|(_, n, _)| n.clone())
                .ok_or_else(|| unsupported("a symbol not listed"))?
        }
        View::Un(op, a) => match op {
            UnOp::Not => format!("(~~~{})", t(a)?),
            UnOp::Neg => format!("(-{})", t(a)?),
            _ => return Err(unsupported("a bit count, byte swap or bit reversal")),
        },
        View::Bin(op @ (BinOp::RotL | BinOp::RotR), a, b) => {
            // By a constant: Lean's rotations take a number.
            let Some(by) = cx.as_const(b)?.and_then(|v| v.to_u64()) else {
                return Err(unsupported("a rotation by a variable"));
            };
            let f = if op == BinOp::RotL {
                "rotateLeft"
            } else {
                "rotateRight"
            };
            format!("(BitVec.{f} {} {})", t(a)?, by % u64::from(w))
        }
        View::Bin(op, a, b) => {
            let (x, y) = (t(a)?, t(b)?);
            match op {
                BinOp::Add => format!("({x} + {y})"),
                BinOp::Sub => format!("({x} - {y})"),
                BinOp::Mul => format!("({x} * {y})"),
                BinOp::And => format!("({x} &&& {y})"),
                BinOp::Or => format!("({x} ||| {y})"),
                BinOp::Xor => format!("({x} ^^^ {y})"),
                // SMT-LIB's division: by zero, all ones and the dividend.
                BinOp::UDiv => format!("(BitVec.smtUDiv {x} {y})"),
                BinOp::URem => format!("({x} % {y})"),
                BinOp::SDiv => format!("(BitVec.smtSDiv {x} {y})"),
                BinOp::SRem => format!("(BitVec.srem {x} {y})"),
                BinOp::Shl => format!("({x} <<< {y})"),
                BinOp::LShr => format!("({x} >>> {y})"),
                BinOp::AShr => format!("(BitVec.sshiftRight' {x} {y})"),
                _ => {
                    return Err(unsupported(
                        "the high half of a product, or a bit deposit or extract",
                    ));
                }
            }
        }
        View::Cmp(op, a, b) => {
            let (x, y) = (t(a)?, t(b)?);
            let p = match op {
                CmpOp::Eq => format!("{x} == {y}"),
                CmpOp::Ne => format!("{x} != {y}"),
                CmpOp::Ult => format!("BitVec.ult {x} {y}"),
                CmpOp::Ule => format!("BitVec.ule {x} {y}"),
                CmpOp::Slt => format!("BitVec.slt {x} {y}"),
                CmpOp::Sle => format!("BitVec.sle {x} {y}"),
            };
            format!("(BitVec.ofBool ({p}))")
        }
        View::Zext(a) => format!("(BitVec.zeroExtend {w} {})", t(a)?),
        View::Sext(a) => format!("(BitVec.signExtend {w} {})", t(a)?),
        View::Extract { lo, src } => format!("(BitVec.extractLsb' {lo} {w} {})", t(src)?),
        View::Concat { hi, lo } => format!("({} ++ {})", t(hi)?, t(lo)?),
        View::Select { cond, then, els } => {
            format!("(if {} = 1#1 then {} else {})", t(cond)?, t(then)?, t(els)?)
        }
        _ => return Err(unsupported("floating point or an extension operation")),
    })
}

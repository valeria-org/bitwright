//! An expression as a Lean 4 `BitVec` term, and an equation of two as an `example` that
//! `bv_decide` checks: the spellings of `bitwright::rules::lean`, for a context's expressions.

use std::fmt::Write as _;

use bw::{BinOp, CmpOp, Context, Expr, UnOp, View};

/// The Lean term of `e`; `Err` names what Lean's core `BitVec` has no counterpart for.
pub fn term(cx: &Context, e: Expr) -> Result<String, String> {
    let w = cx.width(e).map_err(|e| e.to_string())?.bits();
    let sub = |x: Expr| term(cx, x);
    Ok(match cx.view(e).map_err(|e| e.to_string())? {
        View::Const(v) => format!("({v:#x}#{w})"),
        View::Sym(s) => cx
            .symbol_key(s)
            .map(|k| ident(&k.to_string()))
            .unwrap_or_else(|| "_".to_string()),
        View::Un(op, a) => {
            let a = sub(a)?;
            match op {
                UnOp::Not => format!("(~~~{a})"),
                UnOp::Neg => format!("(-{a})"),
                // Written with slices and concatenation, which bv_decide understands.
                UnOp::Bswap if w % 8 == 0 => {
                    let bytes: Vec<String> = (0..w / 8)
                        .map(|i| format!("({a}.extractLsb' {} 8)", i * 8))
                        .collect();
                    format!("({})", bytes.join(" ++ "))
                }
                UnOp::BitRev => {
                    let bits: Vec<String> =
                        (0..w).map(|i| format!("({a}.extractLsb' {i} 1)")).collect();
                    format!("({})", bits.join(" ++ "))
                }
                UnOp::Popcnt => {
                    let bits: Vec<String> = (0..w)
                        .map(|i| format!("(({a}.extractLsb' {i} 1).zeroExtend {w})"))
                        .collect();
                    format!("({})", bits.join(" + "))
                }
                _ => return Err("a leading or trailing zero count".into()),
            }
        }
        View::Bin(op, a, b) => {
            let (ta, tb) = (sub(a)?, sub(b)?);
            match op {
                BinOp::Add => format!("({ta} + {tb})"),
                BinOp::Sub => format!("({ta} - {tb})"),
                BinOp::Mul => format!("({ta} * {tb})"),
                BinOp::UMulHi => format!(
                    "((({ta}.zeroExtend {w2}) * ({tb}.zeroExtend {w2})).extractLsb' {w} {w})",
                    w2 = 2 * w
                ),
                BinOp::SMulHi => format!(
                    "((({ta}.signExtend {w2}) * ({tb}.signExtend {w2})).extractLsb' {w} {w})",
                    w2 = 2 * w
                ),
                BinOp::UDiv => format!("({ta}.smtUDiv {tb})"),
                BinOp::URem => format!("({ta} % {tb})"),
                BinOp::SDiv => format!("({ta}.smtSDiv {tb})"),
                BinOp::SRem => format!("({ta}.srem {tb})"),
                BinOp::And => format!("({ta} &&& {tb})"),
                BinOp::Or => format!("({ta} ||| {tb})"),
                BinOp::Xor => format!("({ta} ^^^ {tb})"),
                BinOp::Shl => format!("({ta} <<< {tb})"),
                BinOp::LShr => format!("({ta} >>> {tb})"),
                BinOp::AShr => format!("({ta}.sshiftRight' {tb})"),
                BinOp::RotL | BinOp::RotR => {
                    let f = if op == BinOp::RotL {
                        "rotateLeft"
                    } else {
                        "rotateRight"
                    };
                    match cx.as_const(b).map_err(|e| e.to_string())? {
                        Some(k) => format!("({ta}.{f} {})", k.to_u64().unwrap_or(0) % u64::from(w)),
                        None => format!("({ta}.{f} ({tb}.toNat % {w}))"),
                    }
                }
                _ => return Err("pdep or pext".into()),
            }
        }
        View::Cmp(op, a, b) => {
            let (ta, tb) = (sub(a)?, sub(b)?);
            let c = match op {
                CmpOp::Eq => format!("({ta} == {tb})"),
                CmpOp::Ne => format!("({ta} != {tb})"),
                CmpOp::Ult => format!("({ta}.ult {tb})"),
                CmpOp::Ule => format!("({ta}.ule {tb})"),
                CmpOp::Slt => format!("({ta}.slt {tb})"),
                CmpOp::Sle => format!("({ta}.sle {tb})"),
                _ => return Err("a comparison Lean's BitVec lacks".into()),
            };
            format!("(BitVec.ofBool {c})")
        }
        View::Zext(a) => format!("({}.zeroExtend {w})", sub(a)?),
        View::Sext(a) => format!("({}.signExtend {w})", sub(a)?),
        View::Extract { lo, src } => format!("({}.extractLsb' {lo} {w})", sub(src)?),
        View::Concat { hi, lo } => format!("({} ++ {})", sub(hi)?, sub(lo)?),
        View::Select { cond, then, els } => format!(
            "(if {} == 1#1 then {} else {})",
            sub(cond)?,
            sub(then)?,
            sub(els)?
        ),
        View::Fp { .. } => return Err("floating point".into()),
        View::Ext { .. } => return Err("an extension operation".into()),
        _ => return Err("a node Lean's BitVec lacks".into()),
    })
}

/// `lhs = rhs` as a Lean `example` over the symbols of both, proved by `bv_decide`.
pub fn equation(cx: &mut Context, lhs: Expr, rhs: Expr) -> Result<String, String> {
    let l = term(cx, lhs)?;
    let r = term(cx, rhs)?;
    let mut s = String::from("import Std.Tactic.BVDecide\n\nexample");
    let mut syms = cx.symbols_in(&[lhs, rhs]).map_err(|e| e.to_string())?;
    syms.sort_by_key(|&s| cx.symbol_key(s).map(|k| k.to_string()));
    for sym in syms {
        let (Some(k), Some(w)) = (cx.symbol_key(sym), cx.symbol_width(sym)) else {
            continue;
        };
        let _ = write!(s, " ({} : BitVec {})", ident(&k.to_string()), w.bits());
    }
    let _ = write!(s, " :\n    {l}\n  = {r} := by\n  bv_decide\n");
    Ok(s)
}

/// A symbol's name as a Lean identifier.
fn ident(name: &str) -> String {
    if !name.is_empty()
        && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !name.starts_with(|c: char| c.is_ascii_digit())
    {
        name.to_string()
    } else {
        format!("«{name}»")
    }
}

//! Integers where bit-vectors bound them: `bv2nat` of a bit-vector, numerals, and sums,
//! differences, products, quotients and remainders by constants, and comparisons of those.
//!
//! The library has no theory of integers. But the integers a bit-vector script writes are
//! mostly of this kind (`(bv2nat x)`, `(mod (+ a b) 256)`, `((_ int2bv 32) n)`), and each has
//! a range: an integer term is read as a signed bit-vector wide enough that nothing it
//! computes wraps, so the arithmetic is the integers' own. An integer variable has no range
//! and is refused, and so is a term that would need more than 512 bits.

use super::*;

/// `e` sign-extended to `w` bits (it is of at most that many).
fn widen(cx: &mut Context, e: Expr, w: Width) -> Result<Expr, Error> {
    if cx.width(e)? == w {
        Ok(e)
    } else {
        Ok(cx.sext(e, w)?)
    }
}

fn bits(n: u32) -> Result<Width, Error> {
    u16::try_from(n)
        .ok()
        .and_then(|n| Width::new(n).ok())
        .ok_or_else(|| Error::Unsupported("an integer that needs more than 512 bits".into()))
}

impl<'a, 's> State<'a, 's> {
    /// A numeral: the integer, in as many bits as it needs and one for the sign.
    pub(super) fn int_literal(&mut self, sx: &Sx<'s>, id: u32, digits: &str) -> Result<Val, Error> {
        let mut limbs = [0u64; 8];
        for d in digits.bytes() {
            let mut carry = u128::from(d - b'0');
            for l in &mut limbs {
                let x = u128::from(*l) * 10 + carry;
                *l = x as u64;
                carry = x >> 64;
            }
            if carry != 0 {
                return Err(sx.err(id, "a numeral of more than 512 bits"));
            }
        }
        let used = (limbs.iter().rposition(|&l| l != 0))
            .map_or(0, |k| 64 * k as u32 + 64 - limbs[k].leading_zeros());
        let w = bits(used + 1)?;
        Ok(Val::Int(
            self.cx.constant(&BitVec::wrapping_from_limbs(w, &limbs))?,
        ))
    }

    /// Whether an application is of integers.
    pub(super) fn int_case(&self, op: &str, args: &[(u32, Val)]) -> bool {
        matches!(op, "bv2nat" | "ubv_to_int" | "sbv_to_int")
            || args.iter().any(|&(_, v)| matches!(v, Val::Int(_)))
    }

    fn int(&self, sx: &Sx<'s>, id: u32, v: Val) -> Result<Expr, Error> {
        match v {
            Val::Int(e) => Ok(e),
            _ => Err(sx.err(id, "expected an integer")),
        }
    }

    /// An operator over integers.
    pub(super) fn apply_int(
        &mut self,
        sx: &Sx<'s>,
        id: u32,
        op: &str,
        args: &[(u32, Val)],
    ) -> Result<Val, Error> {
        let arity = |ok: bool| {
            if ok {
                Ok(())
            } else {
                Err(sx.err(id, "wrong number of operands"))
            }
        };
        if matches!(op, "bv2nat" | "ubv_to_int" | "sbv_to_int") {
            arity(args.len() == 1)?;
            let x = self.bv(sx, args[0].0, args[0].1)?;
            let w = u32::from(self.cx.width(x)?.bits());
            // Unsigned: one more bit, zero, for the sign.
            return Ok(Val::Int(if op == "sbv_to_int" {
                x
            } else {
                self.cx.zext(x, bits(w + 1)?)?
            }));
        }
        if op == "ite" {
            arity(args.len() == 3)?;
            let c = self.boolean(sx, args[0].0, args[0].1)?;
            let (t, f) = (
                self.int(sx, args[1].0, args[1].1)?,
                self.int(sx, args[2].0, args[2].1)?,
            );
            let w = self.cx.width(t)?.max(self.cx.width(f)?);
            let (t, f) = (widen(self.cx, t, w)?, widen(self.cx, f, w)?);
            return Ok(Val::Int(self.cx.select(c, t, f)?));
        }
        let mut xs = Vec::with_capacity(args.len());
        for &(a, v) in args {
            xs.push(self.int(sx, a, v)?);
        }
        arity(!xs.is_empty())?;
        let width = |s: &Self, e: Expr| Ok::<u32, Error>(u32::from(s.cx.width(e)?.bits()));
        match op {
            "+" | "-" | "*" => {
                if op == "-" && xs.len() == 1 {
                    let w = bits(width(self, xs[0])? + 1)?;
                    let x = widen(self.cx, xs[0], w)?;
                    return Ok(Val::Int(self.cx.un(UnOp::Neg, x)?));
                }
                let mut acc = xs[0];
                for &x in &xs[1..] {
                    let (wa, wx) = (width(self, acc)?, width(self, x)?);
                    // A sum or difference has a bit more than the wider; a product, both.
                    let w = bits(if op == "*" { wa + wx } else { wa.max(wx) + 1 })?;
                    let (a, b) = (widen(self.cx, acc, w)?, widen(self.cx, x, w)?);
                    let bin = match op {
                        "+" => BinOp::Add,
                        "-" => BinOp::Sub,
                        _ => BinOp::Mul,
                    };
                    acc = self.cx.bin(bin, a, b)?;
                }
                Ok(Val::Int(acc))
            }
            "abs" => {
                arity(xs.len() == 1)?;
                let w = bits(width(self, xs[0])? + 1)?;
                let x = widen(self.cx, xs[0], w)?;
                let zero = self.cx.constant(&BitVec::zero(w))?;
                let negative = self.cx.cmp(CmpOpExt::Slt, x, zero)?;
                let neg = self.cx.un(UnOp::Neg, x)?;
                Ok(Val::Int(self.cx.select(negative, neg, x)?))
            }
            "div" | "mod" => {
                arity(xs.len() == 2)?;
                // By a constant that is not zero: what a division by zero is, the standard
                // leaves to the model.
                let Some(c) = self.cx.as_const(xs[1])?.filter(|c| !c.is_zero()) else {
                    return Err(Error::Unsupported(format!(
                        "{op} of integers by anything but a constant that is not zero"
                    )));
                };
                let w = bits(width(self, xs[0])?.max(u32::from(c.width().bits())) + 1)?;
                let (a, b) = (widen(self.cx, xs[0], w)?, widen(self.cx, xs[1], w)?);
                // The remainder is not negative: the truncating one, and the divisor's
                // magnitude more where that is.
                let zero = self.cx.constant(&BitVec::zero(w))?;
                let r0 = self.cx.bin(BinOp::SRem, a, b)?;
                let low = self.cx.cmp(CmpOpExt::Slt, r0, zero)?;
                let b_negative = self.cx.cmp(CmpOpExt::Slt, b, zero)?;
                let nb = self.cx.un(UnOp::Neg, b)?;
                let magnitude = self.cx.select(b_negative, nb, b)?;
                let raised = self.cx.bin(BinOp::Add, r0, magnitude)?;
                let r = self.cx.select(low, raised, r0)?;
                if op == "mod" {
                    return Ok(Val::Int(r));
                }
                let exact = self.cx.bin(BinOp::Sub, a, r)?;
                Ok(Val::Int(self.cx.bin(BinOp::SDiv, exact, b)?))
            }
            "<" | "<=" | ">" | ">=" | "=" | "distinct" => {
                arity(xs.len() >= 2)?;
                let mut w = Width::W1;
                for &x in &xs {
                    w = w.max(self.cx.width(x)?);
                }
                for x in &mut xs {
                    *x = widen(self.cx, *x, w)?;
                }
                let cmp = match op {
                    "<" => CmpOpExt::Slt,
                    "<=" => CmpOpExt::Sle,
                    ">" => CmpOpExt::Sgt,
                    ">=" => CmpOpExt::Sge,
                    "=" => CmpOpExt::Eq,
                    _ => CmpOpExt::Ne,
                };
                // A chain, but for `distinct`, which is of every pair.
                let mut acc = self.cx.bool(true)?;
                for i in 0..xs.len() {
                    let others = if op == "distinct" {
                        i + 1..xs.len()
                    } else {
                        i + 1..(i + 2).min(xs.len())
                    };
                    for j in others {
                        let e = self.cx.cmp(cmp, xs[i], xs[j])?;
                        acc = self.cx.bin(BinOp::And, acc, e)?;
                    }
                }
                Ok(Val::Bool(acc))
            }
            _ => Err(Error::Unsupported(format!("{op} of integers"))),
        }
    }

    /// `((_ int2bv n) i)`: the low `n` bits of the integer.
    pub(super) fn int_to_bv(&mut self, i: Expr, n: u32) -> Result<Val, Error> {
        let to = bits(n)?;
        let w = self.cx.width(i)?;
        Ok(Val::Bv(if to <= w {
            self.cx.extract(i, 0, to)?
        } else {
            self.cx.sext(i, to)?
        }))
    }
}

/// An integer's value as SMT-LIB writes it: a numeral, or `(- n)`.
#[cfg_attr(not(feature = "prove"), allow(dead_code))]
pub(in crate::smtlib) fn decimal(v: &BitVec) -> String {
    let negative = v.msb();
    let magnitude = if negative {
        BitVec::apply_un(UnOp::Neg, v).unwrap_or(*v)
    } else {
        *v
    };
    let mut limbs: Vec<u64> = magnitude.limbs().to_vec();
    let mut digits = Vec::new();
    while limbs.iter().any(|&l| l != 0) {
        let mut rem = 0u128;
        for l in limbs.iter_mut().rev() {
            let x = (rem << 64) | u128::from(*l);
            *l = (x / 10) as u64;
            rem = x % 10;
        }
        digits.push(b'0' + rem as u8);
    }
    if digits.is_empty() {
        digits.push(b'0');
    }
    digits.reverse();
    let text = String::from_utf8(digits).unwrap_or_default();
    if negative {
        format!("(- {text})")
    } else {
        text
    }
}

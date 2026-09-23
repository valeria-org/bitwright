//! Shared by the fuzz targets: a byte reader and a byte-encoded DAG builder.

use bitwright::{BinOp, BitVec, CmpOp, Context, Expr, UnOp, Width};

/// Reads bytes, never past the end (zeros after it).
pub struct Bytes<'a>(pub &'a [u8]);

impl Bytes<'_> {
    pub fn byte(&mut self) -> u8 {
        match self.0.split_first() {
            Some((&b, rest)) => {
                self.0 = rest;
                b
            }
            None => 0,
        }
    }

    pub fn u64(&mut self) -> u64 {
        (0..8).fold(0, |acc, _| acc << 8 | u64::from(self.byte()))
    }
}

/// `e` at width `w`: truncated or zero-extended.
pub fn fit(cx: &mut Context, e: Expr, w: Width) -> Expr {
    let ew = cx.width(e).unwrap();
    if ew == w {
        e
    } else if ew > w {
        cx.trunc(e, w).unwrap()
    } else {
        cx.zext(e, w).unwrap()
    }
}

pub fn build(cx: &mut Context, b: &mut Bytes<'_>) -> Option<Expr> {
    const WIDTHS: [u16; 8] = [1, 3, 8, 13, 32, 64, 65, 128];
    let w = Width::new(WIDTHS[usize::from(b.byte() % 8)]).unwrap();
    let mut stack: Vec<Expr> = Vec::new();
    for _ in 0..64 {
        if b.0.is_empty() {
            break;
        }
        let op = b.byte();
        let pop = |stack: &mut Vec<Expr>, cx: &mut Context| -> Expr {
            let e = stack
                .pop()
                .unwrap_or_else(|| cx.symbol(format!("x{}", w.bits()).as_str(), w).unwrap());
            fit(cx, e, w)
        };
        let e = match op % 12 {
            0 | 1 => {
                // The width is part of the name: several DAGs may share a context.
                let names = ["x", "y", "z", "t"];
                let name = format!("{}{}", names[usize::from(b.byte() % 4)], w.bits());
                cx.symbol(name.as_str(), w).unwrap()
            }
            2 => {
                let v = BitVec::wrapping_from_limbs(w, &[b.u64(), b.u64()]);
                cx.constant(&v).unwrap()
            }
            3 => {
                let op = UnOp::ALL[usize::from(b.byte()) % UnOp::ALL.len()];
                if op == UnOp::Bswap && w.bits() % 8 != 0 {
                    continue;
                }
                let a = pop(&mut stack, cx);
                cx.un(op, a).unwrap()
            }
            4..=7 => {
                let op = BinOp::ALL[usize::from(b.byte()) % BinOp::ALL.len()];
                let (y, x) = (pop(&mut stack, cx), pop(&mut stack, cx));
                cx.bin(op, x, y).unwrap()
            }
            8 => {
                let op = CmpOp::ALL[usize::from(b.byte()) % CmpOp::ALL.len()];
                let (y, x) = (pop(&mut stack, cx), pop(&mut stack, cx));
                let c = cx.cmp(op, x, y).unwrap();
                fit(cx, c, w)
            }
            9 => {
                let (f, t, c) = (
                    pop(&mut stack, cx),
                    pop(&mut stack, cx),
                    pop(&mut stack, cx),
                );
                let c = cx.trunc(c, Width::W1).unwrap_or(c);
                let c = fit(cx, c, Width::W1);
                cx.select(c, t, f).unwrap()
            }
            10 => {
                // Through a narrower or wider view and back.
                let a = pop(&mut stack, cx);
                let k = 1 + u16::from(b.byte()) % 128;
                let v = Width::new(k).unwrap();
                let lo = if k < w.bits() {
                    u16::from(b.byte()) % (w.bits() - k + 1)
                } else {
                    0
                };
                let mid = if k < w.bits() {
                    cx.extract(a, lo, v).unwrap()
                } else if b.byte() % 2 == 0 {
                    cx.zext(a, v).unwrap_or(a)
                } else {
                    cx.sext(a, v).unwrap_or(a)
                };
                fit(cx, mid, w)
            }
            _ => {
                // Share: duplicate a stack entry.
                match stack.last() {
                    Some(&e) => e,
                    None => continue,
                }
            }
        };
        stack.push(e);
    }
    stack.pop().map(|e| fit(cx, e, w))
}

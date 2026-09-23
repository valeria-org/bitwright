//! SMT-LIB 2.6 (QF_BV) export of expressions, and the operator translation shared with rule
//! obligations.

use core::fmt::Write as _;

use crate::error::Error;
use crate::expr::{Context, Expr, OpCode};
use crate::ops::{BinOp, CmpOp};
use crate::{BitVec, SymbolKey, Width};

/// A binary literal of exactly the value's width.
pub(crate) fn literal(v: &BitVec) -> String {
    let w = v.width().bits() as usize;
    let mut s = String::with_capacity(w + 2);
    s.push_str("#b");
    let limbs = v.limbs();
    for i in (0..w).rev() {
        let bit = (limbs[i / 64] >> (i % 64)) & 1;
        s.push(if bit == 1 { '1' } else { '0' });
    }
    s
}

/// Whether `s` has the form of a name the exporter generates (`n<digit>…`, `root<digit>…`,
/// `sym!…`, `ext!…`), which a symbol must not take.
fn generated(s: &str) -> bool {
    let digit_after = |p: &str| {
        s.strip_prefix(p)
            .is_some_and(|r| r.as_bytes().first().is_some_and(u8::is_ascii_digit))
    };
    digit_after("n") || digit_after("root") || s.starts_with("sym!") || s.starts_with("ext!")
}

/// Names SMT-LIB gives a meaning to: `|name|` is the same symbol as `name`, so a symbol spelled
/// as one of these would redeclare a reserved word or a Core or bit-vector theory symbol.
const RESERVED: &[&str] = &[
    // Reserved words.
    "!",
    "_",
    "as",
    "BINARY",
    "DECIMAL",
    "exists",
    "forall",
    "HEXADECIMAL",
    "let",
    "match",
    "NUMERAL",
    "par",
    "STRING",
    "assert",
    "check-sat",
    "declare-const",
    "declare-fun",
    "define-fun",
    "define-sort",
    "exit",
    "get-model",
    "get-value",
    "pop",
    "push",
    "reset",
    "set-info",
    "set-logic",
    "set-option",
    // Core theory.
    "Bool",
    "true",
    "false",
    "not",
    "and",
    "or",
    "xor",
    "=>",
    "=",
    "distinct",
    "ite",
    // Bit-vector theory and its common extensions.
    "BitVec",
    "concat",
    "extract",
    "repeat",
    "zero_extend",
    "sign_extend",
    "rotate_left",
    "rotate_right",
    "bvnot",
    "bvand",
    "bvor",
    "bvxor",
    "bvnand",
    "bvnor",
    "bvxnor",
    "bvcomp",
    "bvneg",
    "bvadd",
    "bvsub",
    "bvmul",
    "bvudiv",
    "bvurem",
    "bvsdiv",
    "bvsrem",
    "bvsmod",
    "bvshl",
    "bvlshr",
    "bvashr",
    "bvult",
    "bvule",
    "bvugt",
    "bvuge",
    "bvslt",
    "bvsle",
    "bvsgt",
    "bvsge",
];

/// Whether `s` can be written as `|s|`, read back unchanged, and mean a fresh symbol.
pub(crate) fn quotable(s: &str) -> bool {
    !s.is_empty()
        && s.chars()
            .all(|c| c != '|' && c != '\\' && (c == ' ' || c.is_ascii_graphic()))
        && !RESERVED.contains(&s)
        && !(s.starts_with("bv") && s[2..].bytes().all(|b| b.is_ascii_digit()) && s.len() > 2)
}

/// The SMT-LIB name of a symbol: `|name|` for a printable name without `|` or `\`, `|#k|` for
/// an integer key, `|$k|` for a fresh key. Other names, and names that would collide with those
/// forms, with the exporter's own names, with SMT-LIB's reserved words and theory symbols, or
/// with its reserved `@`/`.` prefixes, use `|sym!id|`.
pub(crate) fn symbol_name(key: &SymbolKey, id: u32) -> String {
    match key {
        SymbolKey::U64(k) => format!("|#{k}|"),
        SymbolKey::Fresh(k) => format!("|${k}|"),
        SymbolKey::Str(s)
            if quotable(s) && !s.starts_with(['#', '$', '@', '.']) && !generated(s) =>
        {
            format!("|{s}|")
        }
        _ => format!("|sym!{id}|"),
    }
}

pub(crate) fn sort(w: u16) -> String {
    format!("(_ BitVec {w})")
}

/// One operator application to translate.
pub(crate) struct App<'a> {
    /// A prefix for helper definitions, unique to this application.
    pub(crate) tag: &'a str,
    /// The result width.
    pub(crate) w: u16,
    /// The operands' SMT-LIB terms (names).
    pub(crate) args: &'a [String],
    /// The operands' widths.
    pub(crate) arg_w: &'a [u16],
    /// `Extract`'s low bit.
    pub(crate) lo: u32,
}

/// The SMT-LIB term for `op` applied as `app` describes. Operators without a QF_BV counterpart
/// are expanded, through helper definitions written to `out` (flat, however wide). Comparisons
/// give a 1-bit vector. `Const` and `Sym` are the caller's.
pub(crate) fn term(out: &mut String, op: OpCode, app: &App<'_>) -> Result<String, Error> {
    let (w, ww, tag) = (app.w, u32::from(app.w), app.tag);
    let arg = |k: usize| -> Result<&str, Error> {
        app.args
            .get(k)
            .map(String::as_str)
            .ok_or_else(|| Error::Contract(format!("{op:?} is missing an operand")))
    };
    Width::new(w).map_err(|_| Error::Contract("bad width".into()))?;
    // Small counts and indices, as `(_ bvN W)`: a literal's size stays logarithmic, not W.
    let wconst = |v: u64| {
        let v = if ww < 64 { v & ((1u64 << ww) - 1) } else { v };
        format!("(_ bv{v} {ww})")
    };
    let def = |out: &mut String, name: &str, s: u16, body: &str| {
        writeln!(out, "(define-fun {name} () {} {body})", sort(s)).ok();
    };
    let one_bit = |c: &str| format!("(ite {c} #b1 #b0)");
    Ok(match op {
        OpCode::Not => format!("(bvnot {})", arg(0)?),
        OpCode::Neg => format!("(bvneg {})", arg(0)?),
        OpCode::Popcnt => {
            // Σ zero_extend(bit k).
            let a = arg(0)?;
            let bit = |k: u32| {
                if ww == 1 {
                    format!("((_ extract {k} {k}) {a})")
                } else {
                    format!("((_ zero_extend {}) ((_ extract {k} {k}) {a}))", ww - 1)
                }
            };
            let mut acc = bit(0);
            for k in 1..ww {
                let h = format!("{tag}_p{k}");
                def(out, &h, w, &format!("(bvadd {acc} {})", bit(k)));
                acc = h;
            }
            acc
        }
        OpCode::Clz | OpCode::Ctz => {
            // Each helper tests one bit; the last test (the highest bit for clz, the lowest
            // for ctz) is outermost, so it decides.
            let a = arg(0)?;
            let mut prev = wconst(u64::from(ww));
            let bits: Vec<u32> = if op == OpCode::Clz {
                (0..ww).collect()
            } else {
                (0..ww).rev().collect()
            };
            for k in bits {
                let count = if op == OpCode::Clz { ww - 1 - k } else { k };
                let h = format!("{tag}_c{k}");
                def(
                    out,
                    &h,
                    w,
                    &format!(
                        "(ite (= ((_ extract {k} {k}) {a}) #b1) {} {prev})",
                        wconst(u64::from(count))
                    ),
                );
                prev = h;
            }
            prev
        }
        OpCode::Bswap | OpCode::BitRev => {
            // The low piece first (it becomes the high end), then each next piece below it.
            let a = arg(0)?;
            let size = if op == OpCode::Bswap { 8 } else { 1 };
            if ww % size != 0 {
                return Err(Error::Contract(
                    "bswap of a width not a multiple of 8".into(),
                ));
            }
            let piece = |k: u32| format!("((_ extract {} {}) {a})", k * size + size - 1, k * size);
            let mut acc = piece(0);
            for k in 1..ww / size {
                let h = format!("{tag}_r{k}");
                def(
                    out,
                    &h,
                    ((k + 1) * size) as u16,
                    &format!("(concat {acc} {})", piece(k)),
                );
                acc = h;
            }
            acc
        }
        OpCode::Zext | OpCode::Sext => {
            let from = u32::from(*app.arg_w.first().unwrap_or(&0));
            if from == 0 || from > ww {
                return Err(Error::Contract("bad extension".into()));
            }
            if from == ww {
                arg(0)?.to_string()
            } else {
                let f = if op == OpCode::Zext {
                    "zero_extend"
                } else {
                    "sign_extend"
                };
                format!("((_ {f} {}) {})", ww - from, arg(0)?)
            }
        }
        OpCode::Extract => format!("((_ extract {} {}) {})", app.lo + ww - 1, app.lo, arg(0)?),
        OpCode::Concat => format!("(concat {} {})", arg(0)?, arg(1)?),
        OpCode::Select => format!("(ite (= {} #b1) {} {})", arg(0)?, arg(1)?, arg(2)?),
        op => {
            if let Some(c) = op.as_cmp() {
                let (a, b) = (arg(0)?, arg(1)?);
                let f = match c {
                    CmpOp::Eq => format!("(= {a} {b})"),
                    CmpOp::Ne => format!("(not (= {a} {b}))"),
                    CmpOp::Ult => format!("(bvult {a} {b})"),
                    CmpOp::Ule => format!("(bvule {a} {b})"),
                    CmpOp::Slt => format!("(bvslt {a} {b})"),
                    CmpOp::Sle => format!("(bvsle {a} {b})"),
                };
                one_bit(&f)
            } else if let Some(bo) = op.as_bin() {
                bin(out, bo, app, &wconst)?
            } else {
                return Err(Error::Contract(format!("no SMT-LIB form for {op:?}")));
            }
        }
    })
}

fn bin(
    out: &mut String,
    bo: BinOp,
    app: &App<'_>,
    wconst: &dyn Fn(u64) -> String,
) -> Result<String, Error> {
    let (w, ww, tag) = (app.w, u32::from(app.w), app.tag);
    let [x, y] = app.args else {
        return Err(Error::Contract(format!("{bo:?} takes two operands")));
    };
    let simple = |f: &str| format!("({f} {x} {y})");
    Ok(match bo {
        BinOp::Add => simple("bvadd"),
        BinOp::Sub => simple("bvsub"),
        BinOp::Mul => simple("bvmul"),
        BinOp::UDiv => simple("bvudiv"),
        BinOp::URem => simple("bvurem"),
        BinOp::SDiv => simple("bvsdiv"),
        BinOp::SRem => simple("bvsrem"),
        BinOp::And => simple("bvand"),
        BinOp::Or => simple("bvor"),
        BinOp::Xor => simple("bvxor"),
        BinOp::Shl => simple("bvshl"),
        BinOp::LShr => simple("bvlshr"),
        BinOp::AShr => simple("bvashr"),
        BinOp::RotL | BinOp::RotR => {
            // By the count modulo the width; the complementary shift of W gives 0.
            let k = format!("(bvurem {y} {})", wconst(u64::from(ww)));
            let back = format!("(bvsub {} {k})", wconst(u64::from(ww)));
            let (s1, s2) = if bo == BinOp::RotL {
                ("bvshl", "bvlshr")
            } else {
                ("bvlshr", "bvshl")
            };
            format!("(bvor ({s1} {x} {k}) ({s2} {x} {back}))")
        }
        BinOp::UMulHi | BinOp::SMulHi if 2 * ww <= u32::from(Width::MAX_BITS) => {
            let ext = if bo == BinOp::UMulHi {
                "zero_extend"
            } else {
                "sign_extend"
            };
            format!(
                "((_ extract {} {ww}) (bvmul ((_ {ext} {ww}) {x}) ((_ {ext} {ww}) {y})))",
                2 * ww - 1
            )
        }
        BinOp::UMulHi | BinOp::SMulHi => {
            // A 2W-bit product would be wider than any bit-vector bitwright reads back: the
            // high half from half-word products instead, in at most W + 1 bits.
            let hi = wide_umulhi(out, tag, ww, x, y);
            if bo == BinOp::UMulHi {
                hi
            } else {
                // The signed high half: the unsigned one less b where a < 0 and a where b < 0.
                let zero = wconst(0);
                format!(
                    "(bvsub (bvsub {hi} (ite (bvslt {x} {zero}) {y} {zero})) \
                     (ite (bvslt {y} {zero}) {x} {zero}))"
                )
            }
        }
        BinOp::Pdep | BinOp::Pext => {
            // Unrolled over the mask's bits; `cnt` counts the mask bits seen.
            let (zero, one) = (wconst(0), wconst(1));
            let (mut acc, mut cnt) = (zero.clone(), zero);
            for k in 0..ww {
                let set = format!("(= ((_ extract {k} {k}) {y}) #b1)");
                let kc = wconst(u64::from(k));
                let (an, cn) = (format!("{tag}_a{k}"), format!("{tag}_n{k}"));
                let bit = if bo == BinOp::Pext {
                    // Bit k of x goes to position cnt.
                    format!("(bvshl (bvand (bvlshr {x} {kc}) {one}) {cnt})")
                } else {
                    // Bit cnt of x goes to position k.
                    format!("(bvshl (bvand (bvlshr {x} {cnt}) {one}) {kc})")
                };
                writeln!(
                    out,
                    "(define-fun {an} () {s} (ite {set} (bvor {acc} {bit}) {acc}))",
                    s = sort(w)
                )
                .ok();
                writeln!(
                    out,
                    "(define-fun {cn} () {s} (ite {set} (bvadd {cnt} {one}) {cnt}))",
                    s = sort(w)
                )
                .ok();
                acc = an;
                cnt = cn;
            }
            acc
        }
    })
}

/// The high `ww` bits of the product of the `ww`-bit terms `x` and `y`, without a 2W-bit
/// intermediate: for even W, the half-word algorithm (Hacker's Delight, `mulhu`), in which no
/// W-bit sum or product overflows; for odd W, that algorithm at W + 1 bits (the high W + 1 bits
/// of the product, doubled, plus bit W of the low half), truncated. Helpers go to `out`.
fn wide_umulhi(out: &mut String, tag: &str, ww: u32, x: &str, y: &str) -> String {
    let def = |out: &mut String, name: &str, s: u32, body: &str| {
        writeln!(out, "(define-fun {name} () (_ BitVec {s}) {body})").ok();
    };
    let even = if ww.is_multiple_of(2) { ww } else { ww + 1 };
    let (a, b) = if even == ww {
        (x.to_string(), y.to_string())
    } else {
        (
            format!("((_ zero_extend 1) {x})"),
            format!("((_ zero_extend 1) {y})"),
        )
    };
    let h = even / 2;
    let shift = format!("(_ bv{h} {even})");
    let mask = format!("((_ zero_extend {h}) (bvnot (_ bv0 {h})))");
    let lo = |t: &str| format!("(bvand {t} {mask})");
    let up = |t: &str| format!("(bvlshr {t} {shift})");
    let n = |k: &str| format!("{tag}_mh{k}");
    for (k, body) in [
        ("a", a.clone()),
        ("b", b.clone()),
        ("u0", lo(&n("a"))),
        ("u1", up(&n("a"))),
        ("v0", lo(&n("b"))),
        ("v1", up(&n("b"))),
        ("w0", format!("(bvmul {} {})", n("u0"), n("v0"))),
        (
            "t",
            format!("(bvadd (bvmul {} {}) {})", n("u1"), n("v0"), up(&n("w0"))),
        ),
        (
            "w1",
            format!("(bvadd (bvmul {} {}) {})", n("u0"), n("v1"), lo(&n("t"))),
        ),
        (
            "hi",
            format!(
                "(bvadd (bvadd (bvmul {} {}) {}) {})",
                n("u1"),
                n("v1"),
                up(&n("t")),
                up(&n("w1"))
            ),
        ),
    ] {
        def(out, &n(k), even, &body);
    }
    if even == ww {
        return n("hi");
    }
    // floor(a·b / 2^W) = 2·floor(a·b / 2^(W+1)) + bit W of a·b; it fits in W bits.
    format!(
        "((_ extract {} 0) (bvor (bvshl {} (_ bv1 {even})) (bvlshr (bvmul {} {}) (_ bv{ww} {even}))))",
        ww - 1,
        n("hi"),
        n("a"),
        n("b")
    )
}

/// Emits the definitions of every node below `roots` (one `define-fun` per node, operands first)
/// and a `define-fun` per root named `root0`, `root1`, …; symbols are declared.
pub(crate) fn emit(cx: &mut Context, roots: &[Expr]) -> Result<String, Error> {
    let ids = cx.ids(roots)?;
    let order = cx.post_order_ids(&ids);
    let mut out = String::new();
    let name = |i: u32| format!("n{i}");
    // Uninterpreted functions declared for extension outputs without an SMT-LIB definition.
    let mut declared: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for &i in &order {
        let n = cx.node(i);
        let body = match n.op {
            op if op.as_ext().is_some() => {
                let (_, k) = op.as_ext().unwrap_or((1, 0));
                let o = cx
                    .registry
                    .as_deref()
                    .and_then(|r| r.op_at(n.aux))
                    .ok_or_else(|| {
                        Error::Contract("an extension node without its operation".into())
                    })?;
                let kids: Vec<u32> = n.children().collect();
                let args: Vec<String> = kids.iter().map(|&c| name(c)).collect();
                let widths: Vec<Width> = kids.iter().map(|&c| cx.width_of(c)).collect();
                let arg_refs: Vec<&str> = args.iter().map(String::as_str).collect();
                match o.smtlib(k as u8, &arg_refs, &widths) {
                    Some(t) => {
                        if !one_term(&t) {
                            return Err(Error::Contract(format!(
                                "`{}` gave an SMT-LIB term that is not one balanced expression",
                                o.name()
                            )));
                        }
                        t
                    }
                    None => {
                        // `|ext!name#rev[k]@w1,w2|`: one uninterpreted function per operation,
                        // revision, output and argument widths (`ext!` names are reserved).
                        let ws: Vec<String> = widths.iter().map(|w| w.bits().to_string()).collect();
                        let f =
                            format!("|ext!{}#{}[{k}]@{}|", o.name(), o.revision(), ws.join(","));
                        if declared.insert(f.clone()) {
                            let sorts: Vec<String> =
                                widths.iter().map(|w| sort(w.bits())).collect();
                            writeln!(
                                out,
                                "(declare-fun {f} ({}) {})",
                                sorts.join(" "),
                                sort(n.width)
                            )
                            .ok();
                        }
                        format!("({f} {})", args.join(" "))
                    }
                }
            }
            OpCode::Const => {
                let v = cx
                    .const_val(i)
                    .ok_or_else(|| Error::Contract("a constant without a value".into()))?;
                literal(&v)
            }
            OpCode::Sym => {
                let id = crate::expr::SymbolId(n.a);
                let key = cx
                    .symbol_key(id)
                    .cloned()
                    .ok_or_else(|| Error::Contract("dangling symbol".into()))?;
                let sname = symbol_name(&key, n.a);
                writeln!(out, "(declare-const {sname} {})", sort(n.width)).ok();
                sname
            }
            op => {
                let kids: Vec<u32> = n.children().collect();
                let args: Vec<String> = kids.iter().map(|&k| name(k)).collect();
                let arg_w: Vec<u16> = kids.iter().map(|&k| cx.wid(k)).collect();
                let tag = name(i);
                let lo = if op == OpCode::Extract { n.b } else { 0 };
                term(
                    &mut out,
                    op,
                    &App {
                        tag: &tag,
                        w: n.width,
                        args: &args,
                        arg_w: &arg_w,
                        lo,
                    },
                )?
            }
        };
        writeln!(out, "(define-fun {} () {} {body})", name(i), sort(n.width)).ok();
    }
    for (k, &r) in ids.iter().enumerate() {
        writeln!(
            out,
            "(define-fun root{k} () {} {})",
            sort(cx.wid(r)),
            name(r)
        )
        .ok();
    }
    Ok(out)
}

/// Whether `t` is one SMT-LIB term: an atom, or one balanced parenthesized expression, with no
/// unterminated quoted symbol or string (so a host term cannot add commands to a script).
fn one_term(t: &str) -> bool {
    let t = t.trim();
    if t.is_empty() {
        return false;
    }
    let mut depth = 0i64;
    let mut closed_at_top = false;
    let mut chars = t.chars().peekable();
    while let Some(c) = chars.next() {
        if closed_at_top {
            return false;
        }
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth < 0 {
                    return false;
                }
                if depth == 0 {
                    closed_at_top = true;
                }
            }
            '|' => {
                if !chars.by_ref().any(|d| d == '|') {
                    return false;
                }
            }
            '"' => loop {
                match chars.next() {
                    None => return false,
                    Some('"') if chars.peek() == Some(&'"') => {
                        chars.next();
                    }
                    Some('"') => break,
                    _ => {}
                }
            },
            ';' => return false,
            c if c.is_whitespace() && depth == 0 => return false,
            _ => {}
        }
    }
    depth == 0
}

//! Ghidra's p-code: one operation per line, `[output =] OPCODE input, input, …`, each varnode
//! `(space, offset, size)` as Ghidra prints it (`(register, 0x20, 8)`, `(unique, 0x3100, 8)`,
//! `(const, 0x1, 8)`, `(ram, 0x404000, 4)`), or with a register name for the offset
//! (`(register, RSP, 8)`). An address and a colon may start a line; `#` or `;` starts a
//! comment.

use std::collections::HashMap;

use super::{Block, Registers, alias, at_line, memory};
use crate::memory::Endian;
use crate::{BinOp, BitVec, CmpOpExt, Context, Error, Expr, UnOp, Width};

#[derive(Clone, Debug)]
enum Offset {
    Num(u64),
    Name(String),
}

#[derive(Clone, Debug)]
struct Varnode {
    space: String,
    offset: Offset,
    size: u16,
}

#[derive(Clone, Debug)]
struct Op {
    line: usize,
    out: Option<Varnode>,
    code: String,
    ins: Vec<Varnode>,
}

fn number(s: &str) -> Option<u64> {
    let (neg, body) = match s.strip_prefix('-') {
        Some(b) => (true, b),
        None => (false, s),
    };
    let v = match body.strip_prefix("0x").or_else(|| body.strip_prefix("0X")) {
        Some(h) => u64::from_str_radix(h, 16).ok()?,
        None => body.parse::<u64>().ok()?,
    };
    Some(if neg { v.wrapping_neg() } else { v })
}

/// The varnodes and words of a line.
fn parse_line(line: usize, text: &str) -> Result<Option<Op>, Error> {
    let text = text.split(['#', ';']).next().unwrap_or("").trim();
    if text.is_empty() {
        return Ok(None);
    }
    // An address prefix: `0x401000:` or `401000:`.
    let text = match text.split_once(':') {
        Some((a, rest))
            if !a.contains('(') && a.trim().chars().all(|c| c.is_ascii_hexdigit() || c == 'x') =>
        {
            rest.trim()
        }
        _ => text,
    };
    let mut chars = text.char_indices().peekable();
    let mut items: Vec<Result<Varnode, String>> = Vec::new();
    while let Some(&(i, c)) = chars.peek() {
        if c.is_whitespace() || c == ',' {
            chars.next();
            continue;
        }
        if c == '(' {
            let close = text[i..]
                .find(')')
                .ok_or_else(|| at_line(line, "a varnode without `)`"))?;
            let inner = &text[i + 1..i + close];
            let parts: Vec<&str> = inner.split(',').map(str::trim).collect();
            let [space, off, size] = parts[..] else {
                return Err(at_line(
                    line,
                    format!("a varnode is (space, offset, size): ({inner})"),
                ));
            };
            let size: u16 = number(size)
                .and_then(|s| u16::try_from(s).ok())
                .filter(|&s| (1..=64).contains(&s))
                .ok_or_else(|| at_line(line, format!("bad size in ({inner})")))?;
            let offset = match number(off) {
                Some(n) => Offset::Num(n),
                None => Offset::Name(off.to_string()),
            };
            items.push(Ok(Varnode {
                space: space.to_string(),
                offset,
                size,
            }));
            for _ in 0..=close {
                chars.next();
            }
            continue;
        }
        if c == '=' {
            items.push(Err("=".into()));
            chars.next();
            continue;
        }
        let start = i;
        let mut end = text.len();
        while let Some(&(j, d)) = chars.peek() {
            if d.is_whitespace() || d == ',' || d == '(' || d == '=' {
                end = j;
                break;
            }
            chars.next();
        }
        items.push(Err(text[start..end].to_string()));
    }
    // [out] [=] CODE ins…
    let mut k = 0;
    let out = match items.first() {
        Some(Ok(v)) => {
            k = 1;
            Some(v.clone())
        }
        _ => None,
    };
    if matches!(items.get(k), Some(Err(s)) if s == "=") {
        k += 1;
    }
    let code = match items.get(k) {
        Some(Err(s)) => s.clone(),
        _ => return Err(at_line(line, "expected an operation")),
    };
    let mut ins = Vec::new();
    for it in &items[k + 1..] {
        match it {
            Ok(v) => ins.push(v.clone()),
            Err(s) => return Err(at_line(line, format!("unexpected `{s}`"))),
        }
    }
    Ok(Some(Op {
        line,
        out,
        code,
        ins,
    }))
}

struct State<'a> {
    cx: &'a mut Context,
    regs: Registers,
    /// Numeric register ranges merged into registers: (start, bytes).
    ranges: Vec<(u64, u64)>,
    temps: HashMap<(String, u64), Expr>,
    mem: Option<(crate::memory::Memory, crate::memory::Version)>,
    stores: Vec<(Expr, Expr)>,
    exits: Vec<(Expr, Expr)>,
    next: Option<Expr>,
}

impl State<'_> {
    /// The register a register varnode names, and the byte offset into it.
    fn register(&self, v: &Varnode) -> (String, u16) {
        match &v.offset {
            Offset::Name(n) => {
                let (base, off, _) = alias(n);
                (base, off)
            }
            Offset::Num(o) => {
                let (start, _) = self
                    .ranges
                    .iter()
                    .copied()
                    .find(|&(s, n)| *o >= s && *o < s + n)
                    .unwrap_or((*o, u64::from(v.size)));
                (format!("reg_{start:#x}"), (*o - start) as u16)
            }
        }
    }

    fn constant(&mut self, value: u64, size: u16) -> Result<Expr, Error> {
        self.cx
            .constant(&BitVec::wrapping_from_u64(Width::new(8 * size)?, value))
    }

    fn read(&mut self, line: usize, v: &Varnode) -> Result<Expr, Error> {
        let w = Width::new(8 * v.size)?;
        match (v.space.as_str(), &v.offset) {
            ("const", Offset::Num(k)) => self.constant(*k, v.size),
            ("register", _) => {
                let (base, off) = self.register(v);
                self.regs.read(self.cx, &base, off, v.size)
            }
            ("unique", Offset::Num(k)) => {
                let e = *self.temps.get(&("unique".into(), *k)).ok_or_else(|| {
                    at_line(line, format!("(unique, {k:#x}) is read before written"))
                })?;
                let ew = self.cx.width(e)?;
                if ew == w {
                    Ok(e)
                } else if ew > w {
                    self.cx.trunc(e, w)
                } else {
                    self.cx.zext(e, w)
                }
            }
            ("ram", Offset::Num(a)) => {
                let addr = self
                    .cx
                    .constant(&BitVec::wrapping_from_u64(Width::W64, *a))?;
                let cx = &mut *self.cx;
                let (m, ver) = {
                    if self.mem.is_none() {
                        let m = memory(Width::W64, Endian::Little);
                        let v = m.initial();
                        self.mem = Some((m, v));
                    }
                    self.mem.as_mut().expect("made")
                };
                m.load(cx, *ver, addr, v.size)
            }
            (s, _) => Err(at_line(
                line,
                format!("the space `{s}` (register, unique, const, ram)"),
            )),
        }
    }

    fn write(&mut self, line: usize, v: &Varnode, value: Expr) -> Result<(), Error> {
        let value = {
            let w = Width::new(8 * v.size)?;
            let vw = self.cx.width(value)?;
            if vw == w {
                value
            } else if vw > w {
                self.cx.trunc(value, w)?
            } else {
                self.cx.zext(value, w)?
            }
        };
        match (v.space.as_str(), &v.offset) {
            ("register", _) => {
                let (base, off) = self.register(v);
                self.regs.write(self.cx, &base, off, value)
            }
            ("unique", Offset::Num(k)) => {
                self.temps.insert(("unique".into(), *k), value);
                Ok(())
            }
            ("ram", Offset::Num(a)) => {
                let addr = self
                    .cx
                    .constant(&BitVec::wrapping_from_u64(Width::W64, *a))?;
                self.store(addr, value)
            }
            (s, _) => Err(at_line(line, format!("writing the space `{s}`"))),
        }
    }

    fn store(&mut self, addr: Expr, value: Expr) -> Result<(), Error> {
        let bits = self.cx.width(addr)?.bits();
        let cx = &mut *self.cx;
        if self.mem.is_none() {
            let m = memory(Width::new(bits)?, Endian::Little);
            let v = m.initial();
            self.mem = Some((m, v));
        }
        let (m, ver) = self.mem.as_mut().expect("made");
        *ver = m.store(cx, *ver, addr, value)?;
        self.stores.push((addr, value));
        Ok(())
    }

    /// A 1-bit condition as a p-code boolean (a byte, 0 or 1) of `size` bytes.
    fn boolean(&mut self, b: Expr, size: u16) -> Result<Expr, Error> {
        self.cx.zext(b, Width::new(8 * size)?)
    }

    /// `amount` as a shift amount at width `w` (a larger one saturates).
    fn amount(&mut self, amount: Expr, w: Width) -> Result<Expr, Error> {
        let aw = self.cx.width(amount)?;
        if aw == w {
            return Ok(amount);
        }
        if aw < w {
            return self.cx.zext(amount, w);
        }
        let limit = self
            .cx
            .constant(&BitVec::wrapping_from_u64(aw, u64::from(w.bits())))?;
        let big = self.cx.cmp(CmpOpExt::Uge, amount, limit)?;
        let low = self.cx.trunc(amount, w)?;
        let sat = self
            .cx
            .constant(&BitVec::wrapping_from_u64(w, u64::from(w.bits())))?;
        self.cx.select(big, sat, low)
    }

    fn op(&mut self, op: &Op) -> Result<bool, Error> {
        let line = op.line;
        let arity = |n: usize| -> Result<(), Error> {
            if op.ins.len() == n {
                Ok(())
            } else {
                Err(at_line(line, format!("{} takes {n} inputs", op.code)))
            }
        };
        let out_size = op.out.as_ref().map(|o| o.size);
        let result: Expr = match op.code.as_str() {
            "COPY" | "CAST" => {
                arity(1)?;
                self.read(line, &op.ins[0])?
            }
            "LOAD" => {
                arity(2)?;
                let addr = self.read(line, &op.ins[1])?;
                let bits = self.cx.width(addr)?.bits();
                let size = out_size.ok_or_else(|| at_line(line, "LOAD without an output"))?;
                let cx = &mut *self.cx;
                if self.mem.is_none() {
                    let m = memory(Width::new(bits)?, Endian::Little);
                    let v = m.initial();
                    self.mem = Some((m, v));
                }
                let (m, ver) = self.mem.as_mut().expect("made");
                m.load(cx, *ver, addr, size)?
            }
            "STORE" => {
                arity(3)?;
                let addr = self.read(line, &op.ins[1])?;
                let value = self.read(line, &op.ins[2])?;
                self.store(addr, value)?;
                return Ok(true);
            }
            "BRANCH" | "BRANCHIND" | "RETURN" => {
                let target = match (op.code.as_str(), op.ins.first()) {
                    ("BRANCH", Some(v)) => match (&v.space[..], &v.offset) {
                        ("ram", Offset::Num(a)) => self.constant(*a, v.size)?,
                        _ => return Err(at_line(line, "a branch inside an instruction")),
                    },
                    (_, Some(v)) => self.read(line, v)?,
                    (_, None) => {
                        return Err(at_line(line, format!("{} without a target", op.code)));
                    }
                };
                self.next = Some(target);
                return Ok(false);
            }
            "CBRANCH" => {
                arity(2)?;
                let target = match (&op.ins[0].space[..], &op.ins[0].offset) {
                    ("ram", Offset::Num(a)) => self.constant(*a, op.ins[0].size)?,
                    _ => return Err(at_line(line, "a branch inside an instruction")),
                };
                let c = self.read(line, &op.ins[1])?;
                let z = self.cx.zero(self.cx.width(c)?)?;
                let taken = self.cx.cmp(CmpOpExt::Ne, c, z)?;
                self.exits.push((taken, target));
                return Ok(true);
            }
            "CALL" | "CALLIND" | "CALLOTHER" => {
                return Err(at_line(
                    line,
                    format!("{} (calls are not modeled)", op.code),
                ));
            }
            code => {
                let mut a = Vec::with_capacity(op.ins.len());
                for v in &op.ins {
                    a.push(self.read(line, v)?);
                }
                let size =
                    out_size.ok_or_else(|| at_line(line, format!("{code} without an output")))?;
                let w = Width::new(8 * size)?;
                let bin = |s: &mut Self, b: BinOp| -> Result<Expr, Error> {
                    arity(2)?;
                    s.cx.bin(b, a[0], a[1])
                };
                let cmp = |s: &mut Self, c: CmpOpExt| -> Result<Expr, Error> {
                    arity(2)?;
                    let r = s.cx.cmp(c, a[0], a[1])?;
                    s.boolean(r, size)
                };
                match code {
                    "INT_ADD" => bin(self, BinOp::Add)?,
                    "INT_SUB" => bin(self, BinOp::Sub)?,
                    "INT_MULT" => bin(self, BinOp::Mul)?,
                    "INT_DIV" => bin(self, BinOp::UDiv)?,
                    "INT_SDIV" => bin(self, BinOp::SDiv)?,
                    "INT_REM" => bin(self, BinOp::URem)?,
                    "INT_SREM" => bin(self, BinOp::SRem)?,
                    "INT_AND" | "BOOL_AND" => bin(self, BinOp::And)?,
                    "INT_OR" | "BOOL_OR" => bin(self, BinOp::Or)?,
                    "INT_XOR" | "BOOL_XOR" => bin(self, BinOp::Xor)?,
                    "INT_LEFT" | "INT_RIGHT" | "INT_SRIGHT" => {
                        arity(2)?;
                        let aw = self.cx.width(a[0])?;
                        let s = self.amount(a[1], aw)?;
                        let b = match code {
                            "INT_LEFT" => BinOp::Shl,
                            "INT_RIGHT" => BinOp::LShr,
                            _ => BinOp::AShr,
                        };
                        self.cx.bin(b, a[0], s)?
                    }
                    "INT_EQUAL" => cmp(self, CmpOpExt::Eq)?,
                    "INT_NOTEQUAL" => cmp(self, CmpOpExt::Ne)?,
                    "INT_LESS" => cmp(self, CmpOpExt::Ult)?,
                    "INT_LESSEQUAL" => cmp(self, CmpOpExt::Ule)?,
                    "INT_SLESS" => cmp(self, CmpOpExt::Slt)?,
                    "INT_SLESSEQUAL" => cmp(self, CmpOpExt::Sle)?,
                    "INT_CARRY" => {
                        arity(2)?;
                        let c = self.cx.add_carry(a[0], a[1])?;
                        self.boolean(c, size)?
                    }
                    "INT_SCARRY" => {
                        arity(2)?;
                        let c = self.cx.sadd_overflow(a[0], a[1])?;
                        self.boolean(c, size)?
                    }
                    "INT_SBORROW" => {
                        arity(2)?;
                        let c = self.cx.ssub_overflow(a[0], a[1])?;
                        self.boolean(c, size)?
                    }
                    "INT_2COMP" => {
                        arity(1)?;
                        self.cx.un(UnOp::Neg, a[0])?
                    }
                    "INT_NEGATE" => {
                        arity(1)?;
                        self.cx.un(UnOp::Not, a[0])?
                    }
                    "BOOL_NEGATE" => {
                        arity(1)?;
                        let one = self.cx.one(self.cx.width(a[0])?)?;
                        self.cx.bin(BinOp::Xor, a[0], one)?
                    }
                    "INT_ZEXT" => {
                        arity(1)?;
                        self.cx.zext(a[0], w)?
                    }
                    "INT_SEXT" => {
                        arity(1)?;
                        self.cx.sext(a[0], w)?
                    }
                    "PIECE" => {
                        arity(2)?;
                        self.cx.concat(a[0], a[1])?
                    }
                    "SUBPIECE" => {
                        arity(2)?;
                        let k = match op.ins[1].offset {
                            Offset::Num(k) => k,
                            _ => return Err(at_line(line, "SUBPIECE's offset is a constant")),
                        };
                        let from = self.cx.width(a[0])?.bits();
                        let lo = (8 * k) as u16;
                        let len = w.bits().min(from.saturating_sub(lo));
                        if len == 0 {
                            self.cx.zero(w)?
                        } else {
                            let e = self.cx.extract(a[0], lo, Width::new(len)?)?;
                            self.cx.zext(e, w)?
                        }
                    }
                    "POPCOUNT" | "LZCOUNT" => {
                        arity(1)?;
                        let u = if code == "POPCOUNT" {
                            UnOp::Popcnt
                        } else {
                            UnOp::Clz
                        };
                        self.cx.un(u, a[0])?
                    }
                    "PTRADD" => {
                        arity(3)?;
                        let m = self.cx.bin(BinOp::Mul, a[1], a[2])?;
                        self.cx.bin(BinOp::Add, a[0], m)?
                    }
                    "PTRSUB" => bin(self, BinOp::Add)?,
                    _ => return Err(at_line(line, format!("the operation {code}"))),
                }
            }
        };
        match &op.out {
            Some(o) => self.write(line, o, result)?,
            None => return Err(at_line(line, format!("{} without an output", op.code))),
        }
        Ok(true)
    }
}

/// Reads a block of p-code (see the [module](self) documentation), until a `BRANCH` or
/// `RETURN` (a `CBRANCH` is an exit; the code after it runs as if it was not taken).
pub fn pcode(cx: &mut Context, text: &str) -> Result<Block, Error> {
    let mut ops = Vec::new();
    for (k, line) in text.lines().enumerate() {
        if let Some(op) = parse_line(k + 1, line)? {
            ops.push(op);
        }
    }
    // Numeric register ranges, merged where they overlap; every register's full size.
    let mut ranges: Vec<(u64, u64)> = Vec::new();
    for op in &ops {
        for v in op.out.iter().chain(&op.ins) {
            if v.space == "register"
                && let Offset::Num(o) = v.offset
            {
                ranges.push((o, u64::from(v.size)));
            }
        }
    }
    ranges.sort_unstable();
    let mut merged: Vec<(u64, u64)> = Vec::new();
    for (s, n) in ranges {
        match merged.last_mut() {
            Some((ms, mn)) if s < *ms + *mn => *mn = (*mn).max(s + n - *ms),
            _ => merged.push((s, n)),
        }
    }
    let mut st = State {
        cx,
        regs: Registers::new(),
        ranges: merged,
        temps: HashMap::new(),
        mem: None,
        stores: Vec::new(),
        exits: Vec::new(),
        next: None,
    };
    for op in &ops {
        for v in op.out.iter().chain(&op.ins) {
            if v.space == "register" {
                let (base, off) = st.register(v);
                let full = match &v.offset {
                    Offset::Name(n) => alias(n).2.map(|_| {
                        // A known register's full size.
                        super::X86_64
                            .iter()
                            .find(|(name, ..)| name.eq_ignore_ascii_case(&base))
                            .map_or(8, |&(.., s)| s)
                    }),
                    Offset::Num(_) => None,
                };
                st.regs.note(&base, off, v.size);
                if let Some(f) = full {
                    st.regs.note(&base, 0, f);
                }
            }
        }
    }
    for op in &ops {
        if !st.op(op)? {
            break;
        }
    }
    let (memory, version) = match st.mem.take() {
        Some(m) => m,
        None => {
            let m = memory(Width::W64, Endian::Little);
            let v = m.initial();
            (m, v)
        }
    };
    Ok(Block {
        inputs: st.regs.inputs.clone(),
        outputs: st.regs.outputs(),
        stores: st.stores,
        exits: st.exits,
        next: st.next,
        memory,
        version,
    })
}

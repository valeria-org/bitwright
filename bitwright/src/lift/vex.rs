//! VEX IR as pyvex prints an IRSB: the temporaries' types (`t0:Ity_I64 …`), then statements
//! (`t1 = GET:I64(rdi)`, `t2 = Add64(t1,0x0000000000000001)`, `PUT(rax) = t2`,
//! `t3 = LDle:I32(t1)`, `STle(t1) = t4`, `if (t5) { PUT(rip) = 0x401010; Ijk_Boring }`,
//! `NEXT: PUT(rip) = t6; Ijk_Ret`), statement numbers (`03 |`) optional. A helper call
//! (`amd64g_calculate_condition(…)`) is an unknown value.

use std::collections::HashMap;

use super::{Block, Registers, alias, at_line, memory};
use crate::memory::{Endian, Memory, Version};
use crate::{BinOp, BitVec, CmpOpExt, Context, Error, Expr, UnOp, Width};

struct State<'a> {
    cx: &'a mut Context,
    regs: Registers,
    temps: HashMap<u32, Expr>,
    types: HashMap<u32, u16>,
    mem: Option<(Memory, Version)>,
    stores: Vec<(Expr, Expr)>,
    exits: Vec<(Expr, Expr)>,
    next: Option<Expr>,
    opaque: u32,
}

/// The width of a type name (`I64`, `Ity_I64`, `I1`).
fn type_bits(t: &str) -> Option<u16> {
    let t = t.strip_prefix("Ity_").unwrap_or(t);
    let n: u16 = t.strip_prefix('I')?.parse().ok()?;
    matches!(n, 1 | 8 | 16 | 32 | 64 | 128).then_some(n)
}

/// A register argument: `rdi`, or `offset=16`, with its base and byte offset.
fn register(arg: &str) -> (String, u16) {
    let arg = arg.trim();
    if let Some(o) = arg.strip_prefix("offset=") {
        return (format!("offset_{o}"), 0);
    }
    let (base, off, _) = alias(arg);
    (base, off)
}

/// Splits the arguments of `name(a,b,c)` (no nesting in flat VEX).
fn args(s: &str) -> Option<(&str, Vec<&str>)> {
    let open = s.find('(')?;
    let close = s.rfind(')')?;
    let inner = &s[open + 1..close];
    let parts = if inner.trim().is_empty() {
        Vec::new()
    } else {
        inner.split(',').map(str::trim).collect()
    };
    Some((s[..open].trim(), parts))
}

impl State<'_> {
    fn mem(&mut self, bits: u16, big: bool) -> Result<(), Error> {
        if self.mem.is_none() {
            let m = memory(
                Width::new(bits)?,
                if big { Endian::Big } else { Endian::Little },
            );
            let v = m.initial();
            self.mem = Some((m, v));
        }
        Ok(())
    }

    /// An atom: a temporary or a constant (of `bits` when known, else from its digits).
    fn atom(&mut self, line: usize, s: &str, bits: Option<u16>) -> Result<Expr, Error> {
        let s = s.trim();
        if let Some(t) = s.strip_prefix('t')
            && let Ok(k) = t.parse::<u32>()
        {
            return self
                .temps
                .get(&k)
                .copied()
                .ok_or_else(|| at_line(line, format!("t{k} is read before written")));
        }
        // A constant: `0x…`, maybe with a type suffix (`0x1:I8`).
        let (num, suffix) = match s.split_once(':') {
            Some((n, t)) => (n, type_bits(t)),
            None => (s, None),
        };
        let hex = num
            .strip_prefix("0x")
            .ok_or_else(|| at_line(line, format!("`{s}` is not a temporary or a constant")))?;
        let v = u128::from_str_radix(hex, 16)
            .map_err(|_| at_line(line, format!("bad constant {s}")))?;
        let bits = suffix.or(bits).unwrap_or(match hex.len() {
            32 => 128,
            16 => 64,
            8 => 32,
            4 => 16,
            2 => 8,
            _ => 64,
        });
        self.cx
            .constant(&BitVec::wrapping_from_u128(Width::new(bits)?, v))
    }

    fn fit(&mut self, e: Expr, bits: u16) -> Result<Expr, Error> {
        let w = self.cx.width(e)?.bits();
        let to = Width::new(bits)?;
        match w.cmp(&bits) {
            core::cmp::Ordering::Equal => Ok(e),
            core::cmp::Ordering::Less => self.cx.zext(e, to),
            core::cmp::Ordering::Greater => self.cx.trunc(e, to),
        }
    }

    /// The value of an expression of a `tN = …` statement.
    fn expr(&mut self, line: usize, rhs: &str, want: Option<u16>) -> Result<Expr, Error> {
        let rhs = rhs.trim();
        // GET:I64(reg)
        if let Some(rest) = rhs.strip_prefix("GET:") {
            let (ty, a) = args(rest).ok_or_else(|| at_line(line, "GET(…)"))?;
            let bits = type_bits(ty).ok_or_else(|| at_line(line, format!("type {ty}")))?;
            let (base, off) = register(a.first().copied().unwrap_or(""));
            return self.regs.read(self.cx, &base, off, bits / 8);
        }
        // LDle:I32(addr)
        if rhs.starts_with("LDle:") || rhs.starts_with("LDbe:") {
            let big = rhs.starts_with("LDbe");
            let (ty, a) = args(&rhs[5..]).ok_or_else(|| at_line(line, "LD(…)"))?;
            let bits = type_bits(ty).ok_or_else(|| at_line(line, format!("type {ty}")))?;
            let addr = self.atom(line, a.first().copied().unwrap_or(""), Some(64))?;
            let abits = self.cx.width(addr)?.bits();
            self.mem(abits, big)?;
            let cx = &mut *self.cx;
            let (m, v) = self.mem.as_mut().expect("made");
            return m.load(cx, *v, addr, bits.div_ceil(8));
        }
        let Some((name, a)) = args(rhs) else {
            return self.atom(line, rhs, want);
        };
        // A helper call: `helper[…](…):Ity_I64`.
        if name.contains('[') || rhs.contains("):Ity_") || name.contains("calculate") {
            let ty = rhs
                .rsplit(':')
                .next()
                .and_then(type_bits)
                .or(want)
                .unwrap_or(64);
            let key = format!("{}.{}", name.split('[').next().unwrap_or(name), self.opaque);
            self.opaque += 1;
            return self.cx.symbol(key.as_str(), Width::new(ty)?);
        }
        if name == "ITE" {
            let c = self.atom(line, a[0], Some(1))?;
            let c = self.fit(c, 1)?;
            let t = self.atom(line, a[1], want)?;
            let tw = self.cx.width(t)?.bits();
            let e = self.atom(line, a[2], Some(tw))?;
            return self.cx.select(c, t, e);
        }
        self.operation(line, name, &a)
    }

    fn operation(&mut self, line: usize, name: &str, a: &[&str]) -> Result<Expr, Error> {
        let digits_at = name.find(|c: char| c.is_ascii_digit());
        // Conversions: 8Uto32, 64to32, 64HIto32, 32HLto64, 1Uto64.
        if name.chars().next().is_some_and(|c| c.is_ascii_digit()) {
            let (from, rest) = name.split_at(
                name.find(|c: char| !c.is_ascii_digit())
                    .unwrap_or(name.len()),
            );
            let from: u16 = from.parse().map_err(|_| at_line(line, name))?;
            let (kind, to) = if let Some(t) = rest.strip_prefix("Uto") {
                ("u", t)
            } else if let Some(t) = rest.strip_prefix("Sto") {
                ("s", t)
            } else if let Some(t) = rest.strip_prefix("HIto") {
                ("hi", t)
            } else if let Some(t) = rest.strip_prefix("HLto") {
                ("hl", t)
            } else if let Some(t) = rest.strip_prefix("to") {
                ("t", t)
            } else {
                return Err(at_line(line, format!("the operation {name}")));
            };
            let to: u16 = to.parse().map_err(|_| at_line(line, name))?;
            let to_w = Width::new(to)?;
            if kind == "hl" {
                let hi = self.atom(line, a[0], Some(from / 2))?;
                let lo = self.atom(line, a[1], Some(from / 2))?;
                return self.cx.concat(hi, lo);
            }
            let x = self.atom(line, a[0], Some(from))?;
            let x = self.fit(x, from)?;
            return match kind {
                "u" => self.cx.zext(x, to_w),
                "s" => self.cx.sext(x, to_w),
                "hi" => self.cx.extract(x, from - to, to_w),
                _ => self.cx.trunc(x, to_w),
            };
        }
        let Some(d) = digits_at else {
            return Err(at_line(line, format!("the operation {name}")));
        };
        let (base, rest) = name.split_at(d);
        let digits_end = rest
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(rest.len());
        let bits: u16 = rest[..digits_end]
            .parse()
            .map_err(|_| at_line(line, name))?;
        let suffix = &rest[digits_end..];
        let w = Width::new(bits)?;
        let arg = |s: &mut Self, k: usize, b: u16| -> Result<Expr, Error> {
            let e = s.atom(line, a.get(k).copied().unwrap_or(""), Some(b))?;
            s.fit(e, b)
        };
        let bin = |s: &mut Self, op: BinOp| -> Result<Expr, Error> {
            let x = arg(s, 0, bits)?;
            let y = arg(s, 1, bits)?;
            s.cx.bin(op, x, y)
        };
        let cmp = |s: &mut Self, c: CmpOpExt| -> Result<Expr, Error> {
            let x = arg(s, 0, bits)?;
            let y = arg(s, 1, bits)?;
            s.cx.cmp(c, x, y)
        };
        Ok(match (base, suffix) {
            ("Add", "") => bin(self, BinOp::Add)?,
            ("Sub", "") => bin(self, BinOp::Sub)?,
            ("Mul", "") => bin(self, BinOp::Mul)?,
            ("And", "") => bin(self, BinOp::And)?,
            ("Or", "") => bin(self, BinOp::Or)?,
            ("Xor", "") => bin(self, BinOp::Xor)?,
            ("Shl" | "Shr" | "Sar", "") => {
                let x = arg(self, 0, bits)?;
                let s = self.atom(line, a.get(1).copied().unwrap_or(""), Some(8))?;
                let s = self.fit(s, bits)?;
                let op = match base {
                    "Shl" => BinOp::Shl,
                    "Shr" => BinOp::LShr,
                    _ => BinOp::AShr,
                };
                self.cx.bin(op, x, s)?
            }
            ("Not", "") => {
                let x = arg(self, 0, bits)?;
                self.cx.un(UnOp::Not, x)?
            }
            ("CmpEQ" | "CasCmpEQ", "") => cmp(self, CmpOpExt::Eq)?,
            ("CmpNE" | "CasCmpNE" | "ExpCmpNE", "") => cmp(self, CmpOpExt::Ne)?,
            ("CmpLT", "S") => cmp(self, CmpOpExt::Slt)?,
            ("CmpLT", "U") => cmp(self, CmpOpExt::Ult)?,
            ("CmpLE", "S") => cmp(self, CmpOpExt::Sle)?,
            ("CmpLE", "U") => cmp(self, CmpOpExt::Ule)?,
            ("CmpNEZ", "") => {
                let x = arg(self, 0, bits)?;
                let z = self.cx.zero(w)?;
                self.cx.cmp(CmpOpExt::Ne, x, z)?
            }
            ("MullU" | "MullS", "") => {
                let x = arg(self, 0, bits)?;
                let y = arg(self, 1, bits)?;
                if base == "MullU" {
                    self.cx.mul_wide_u(x, y)?
                } else {
                    self.cx.mul_wide_s(x, y)?
                }
            }
            ("DivU", "") => bin(self, BinOp::UDiv)?,
            ("DivS", "") => bin(self, BinOp::SDiv)?,
            ("Clz", "") => {
                let x = arg(self, 0, bits)?;
                self.cx.un(UnOp::Clz, x)?
            }
            ("Ctz", "") => {
                let x = arg(self, 0, bits)?;
                self.cx.un(UnOp::Ctz, x)?
            }
            ("PopCount", "") => {
                let x = arg(self, 0, bits)?;
                self.cx.un(UnOp::Popcnt, x)?
            }
            _ => return Err(at_line(line, format!("the operation {name}"))),
        })
    }

    fn statement(&mut self, line: usize, s: &str) -> Result<bool, Error> {
        let s = s.trim();
        if s.is_empty()
            || s.starts_with("------")
            || s.starts_with("AbiHint")
            || s.starts_with("MBusEvent")
        {
            return Ok(true);
        }
        if let Some(rest) = s.strip_prefix("NEXT:") {
            // NEXT: PUT(rip) = t6; Ijk_Ret
            let assign = rest.split(';').next().unwrap_or("");
            let value = assign.split_once('=').map_or(assign, |(_, v)| v);
            self.next = Some(self.atom(line, value, Some(64))?);
            return Ok(false);
        }
        if let Some(rest) = s.strip_prefix("if (") {
            // if (t5) { PUT(rip) = 0x401010; Ijk_Boring }
            let (cond, body) = rest
                .split_once(')')
                .ok_or_else(|| at_line(line, "if (…)"))?;
            let c = self.atom(line, cond, Some(1))?;
            let c = self.fit(c, 1)?;
            let inner = body.trim().trim_start_matches('{').trim_end_matches('}');
            let assign = inner.split(';').next().unwrap_or("");
            let value = assign.split_once('=').map_or(assign, |(_, v)| v);
            let target = self.atom(line, value, Some(64))?;
            self.exits.push((c, target));
            return Ok(true);
        }
        let (lhs, rhs) = s
            .split_once(" = ")
            .ok_or_else(|| at_line(line, format!("`{s}`")))?;
        let lhs = lhs.trim();
        if let Some(t) = lhs.strip_prefix('t')
            && let Ok(k) = t.parse::<u32>()
        {
            if rhs.trim_start().starts_with("DIRTY") {
                return Err(at_line(line, "a DIRTY helper"));
            }
            let want = self.types.get(&k).copied();
            let mut v = self.expr(line, rhs, want)?;
            if let Some(b) = want {
                v = self.fit(v, b)?;
            }
            self.temps.insert(k, v);
            return Ok(true);
        }
        if let Some(r) = lhs.strip_prefix("PUT(") {
            let reg = r.trim_end_matches(')');
            let (base, off) = register(reg);
            let v = self.atom(line, rhs, None)?;
            self.regs.write(self.cx, &base, off, v)?;
            return Ok(true);
        }
        if lhs.starts_with("STle(") || lhs.starts_with("STbe(") {
            let big = lhs.starts_with("STbe");
            let addr = self.atom(line, &lhs[5..lhs.len() - 1], Some(64))?;
            let v = self.atom(line, rhs, None)?;
            let abits = self.cx.width(addr)?.bits();
            self.mem(abits, big)?;
            let cx = &mut *self.cx;
            let (m, ver) = self.mem.as_mut().expect("made");
            *ver = m.store(cx, *ver, addr, v)?;
            self.stores.push((addr, v));
            return Ok(true);
        }
        Err(at_line(line, format!("the statement `{s}`")))
    }
}

/// Reads an IRSB (see [`lift`](crate::lift)).
pub fn vex(cx: &mut Context, text: &str) -> Result<Block, Error> {
    let mut st = State {
        cx,
        regs: Registers::new(),
        temps: HashMap::new(),
        types: HashMap::new(),
        mem: None,
        stores: Vec::new(),
        exits: Vec::new(),
        next: None,
        opaque: 0,
    };
    let mut lines: Vec<(usize, String)> = Vec::new();
    for (k, raw) in text.lines().enumerate() {
        let mut l = raw.trim();
        if l.starts_with("IRSB") || l == "}" || l.is_empty() {
            continue;
        }
        // Statement numbers: `03 | …`.
        if let Some((num, rest)) = l.split_once('|')
            && num.trim().chars().all(|c| c.is_ascii_digit())
        {
            l = rest.trim();
        }
        // The temporaries' types.
        if l.split_whitespace()
            .all(|w| w.starts_with('t') && w.contains(":Ity_"))
        {
            for w in l.split_whitespace() {
                if let Some((t, ty)) = w.split_once(':')
                    && let (Ok(n), Some(b)) = (t[1..].parse::<u32>(), type_bits(ty))
                {
                    st.types.insert(n, b);
                }
            }
            continue;
        }
        lines.push((k + 1, l.to_string()));
    }
    // Registers' full sizes: each access (a GET's type; a PUT's value, unknown here: 8 bytes
    // for the names x86-64 has).
    for (_, l) in &lines {
        for part in l.split("GET:").skip(1) {
            if let Some((ty, a)) = args(part)
                && let Some(b) = type_bits(ty)
            {
                let (base, off) = register(a.first().copied().unwrap_or(""));
                st.regs.note(&base, off, b.div_ceil(8));
            }
        }
        if let Some(r) = l.strip_prefix("PUT(").and_then(|r| r.split(')').next()) {
            let (base, off) = register(r);
            if super::X86_64
                .iter()
                .any(|(n, ..)| n.eq_ignore_ascii_case(&base))
            {
                st.regs.note(&base, 0, 8);
            }
            let _ = off;
        }
    }
    for (_, l) in &lines {
        for part in l.split("GET:").skip(1) {
            if let Some((_, a)) = args(part) {
                let (base, _) = register(a.first().copied().unwrap_or(""));
                if super::X86_64
                    .iter()
                    .any(|(n, ..)| n.eq_ignore_ascii_case(&base))
                {
                    st.regs.note(&base, 0, 8);
                }
            }
        }
    }
    for (n, l) in &lines {
        if !st.statement(*n, l)? {
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

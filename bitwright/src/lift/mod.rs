//! Front ends for lifted code: the IR a lifter or disassembler produces, read into expressions
//! (the registers' final values, the stores to memory, the conditions of exits), ready to
//! simplify.
//!
//! - [`pcode`]: Ghidra's p-code, one operation per line, varnodes written `(space, offset,
//!   size)` as Ghidra prints them (or with register names).
//! - [`vex`]: VEX IR (Valgrind's and angr's), as pyvex prints an IRSB.
//! - [`llvm`](fn@llvm): LLVM IR functions (feature `prove`), loads and stores included.
//!
//! Registers are named values whose parts are read and written by byte range (x86-64's
//! `eax`, `ax`, `al`, `ah` are parts of `rax`); memory is a [`Memory`]. The straight-line code
//! of one block is read; a conditional exit is recorded, and code after it runs as if the exit
//! was not taken.
//!
//! ```
//! use bitwright::engine::{Engine, Strategy};
//! use bitwright::lift::pcode;
//! use bitwright::Context;
//!
//! let mut cx = Context::new();
//! let block = pcode(
//!     &mut cx,
//!     "(unique, 0x100, 8) = INT_XOR (register, RDI, 8) , (register, RSI, 8)
//!      (unique, 0x108, 8) = INT_AND (register, RDI, 8) , (register, RSI, 8)
//!      (unique, 0x110, 8) = INT_ADD (unique, 0x108, 8) , (unique, 0x108, 8)
//!      (register, RAX, 8) = INT_ADD (unique, 0x100, 8) , (unique, 0x110, 8)",
//! )?;
//! let rax = block.register("RAX").unwrap();
//! let engine = Engine::builder().builtin().strategy(Strategy::deobfuscate()).build()?;
//! let out = engine.simplify(&mut cx, rax)?;
//! assert_eq!(cx.display(out.expr).to_string(), "RDI + RSI");
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

use std::collections::HashMap;

use crate::memory::{Endian, Memory, Version};
use crate::{Context, Error, Expr, Width};

mod pcode;
mod vex;

pub use pcode::pcode;
pub use vex::vex;

#[cfg(feature = "prove")]
mod llvm;
#[cfg(feature = "prove")]
pub use llvm::llvm;

/// What a block of lifted code does.
#[derive(Debug)]
#[non_exhaustive]
pub struct Block {
    /// Registers read before written: name and the symbol of the value it had.
    pub inputs: Vec<(String, Expr)>,
    /// Registers written: name and final value, in the order first written.
    pub outputs: Vec<(String, Expr)>,
    /// Stores to memory, in order: address and value.
    pub stores: Vec<(Expr, Expr)>,
    /// Conditional exits, in order: the condition (1 bit) and the target.
    pub exits: Vec<(Expr, Expr)>,
    /// The address the block continues at, when it says (a return value for a function).
    pub next: Option<Expr>,
    /// The memory the block read and wrote.
    pub memory: Memory,
    /// Its version after the block.
    pub version: Version,
}

impl Block {
    /// The final value of register `name` (an output, else an input), any case.
    pub fn register(&self, name: &str) -> Option<Expr> {
        let find = |list: &[(String, Expr)]| {
            list.iter()
                .find(|(n, _)| n.eq_ignore_ascii_case(name))
                .map(|&(_, e)| e)
        };
        find(&self.outputs).or_else(|| find(&self.inputs))
    }
}

/// x86-64's general-purpose registers and their parts: (name, base, byte offset, bytes).
const X86_64: &[(&str, &str, u16, u16)] = &[
    ("rax", "rax", 0, 8),
    ("eax", "rax", 0, 4),
    ("ax", "rax", 0, 2),
    ("al", "rax", 0, 1),
    ("ah", "rax", 1, 1),
    ("rbx", "rbx", 0, 8),
    ("ebx", "rbx", 0, 4),
    ("bx", "rbx", 0, 2),
    ("bl", "rbx", 0, 1),
    ("bh", "rbx", 1, 1),
    ("rcx", "rcx", 0, 8),
    ("ecx", "rcx", 0, 4),
    ("cx", "rcx", 0, 2),
    ("cl", "rcx", 0, 1),
    ("ch", "rcx", 1, 1),
    ("rdx", "rdx", 0, 8),
    ("edx", "rdx", 0, 4),
    ("dx", "rdx", 0, 2),
    ("dl", "rdx", 0, 1),
    ("dh", "rdx", 1, 1),
    ("rsi", "rsi", 0, 8),
    ("esi", "rsi", 0, 4),
    ("si", "rsi", 0, 2),
    ("sil", "rsi", 0, 1),
    ("rdi", "rdi", 0, 8),
    ("edi", "rdi", 0, 4),
    ("di", "rdi", 0, 2),
    ("dil", "rdi", 0, 1),
    ("rbp", "rbp", 0, 8),
    ("ebp", "rbp", 0, 4),
    ("bp", "rbp", 0, 2),
    ("bpl", "rbp", 0, 1),
    ("rsp", "rsp", 0, 8),
    ("esp", "rsp", 0, 4),
    ("sp", "rsp", 0, 2),
    ("spl", "rsp", 0, 1),
];

/// The base register and byte range a register name stands for (x86-64's parts, and
/// `r8`…`r15` with their `d`, `w`, `b` parts), else the name itself from byte 0.
pub(crate) fn alias(name: &str) -> (String, u16, Option<u16>) {
    let lower = name.to_ascii_lowercase();
    if let Some(&(_, base, off, size)) = X86_64.iter().find(|(n, ..)| *n == lower) {
        return (keep_case(name, base), off, Some(size));
    }
    if let Some(rest) = lower.strip_prefix('r')
        && let Some(end) = rest.find(|c: char| !c.is_ascii_digit())
        && let Ok(k) = rest[..end].parse::<u8>()
        && (8..=15).contains(&k)
    {
        let size = match &rest[end..] {
            "d" => 4,
            "w" => 2,
            "b" | "l" => 1,
            _ => return (name.to_string(), 0, None),
        };
        return (keep_case(name, &format!("r{k}")), 0, Some(size));
    }
    (name.to_string(), 0, None)
}

/// `base` in the case `name` was written in (Ghidra writes `RAX`, pyvex `rax`).
fn keep_case(name: &str, base: &str) -> String {
    if name.chars().any(|c| c.is_ascii_uppercase()) {
        base.to_ascii_uppercase()
    } else {
        base.to_string()
    }
}

/// The registers of a block: each base register's value, read and written by byte range.
pub(crate) struct Registers {
    /// Each register's full size in bytes (from every access, seen before reading the code).
    size: HashMap<String, u16>,
    /// Current values.
    value: HashMap<String, Expr>,
    pub(crate) inputs: Vec<(String, Expr)>,
    written: Vec<String>,
}

impl Registers {
    pub(crate) fn new() -> Self {
        Registers {
            size: HashMap::new(),
            value: HashMap::new(),
            inputs: Vec::new(),
            written: Vec::new(),
        }
    }

    /// Notes an access to bytes `[off, off + size)` of `base` (before reading the code), so
    /// each register gets one symbol of its full size.
    pub(crate) fn note(&mut self, base: &str, off: u16, size: u16) {
        let s = self.size.entry(base.to_string()).or_insert(0);
        *s = (*s).max(off + size);
    }

    fn full(&mut self, cx: &mut Context, base: &str) -> Result<Expr, Error> {
        if let Some(&v) = self.value.get(base) {
            return Ok(v);
        }
        let bytes = self.size.get(base).copied().unwrap_or(8);
        let s = cx.symbol(base, Width::new(8 * bytes)?)?;
        self.inputs.push((base.to_string(), s));
        self.value.insert(base.to_string(), s);
        Ok(s)
    }

    /// Bytes `[off, off + size)` of `base`.
    pub(crate) fn read(
        &mut self,
        cx: &mut Context,
        base: &str,
        off: u16,
        size: u16,
    ) -> Result<Expr, Error> {
        let v = self.full(cx, base)?;
        let w = cx.width(v)?.bits();
        if off == 0 && 8 * size == w {
            return Ok(v);
        }
        cx.extract(v, 8 * off, Width::new(8 * size)?)
    }

    /// Writes bytes `[off, off + size)` of `base`.
    pub(crate) fn write(
        &mut self,
        cx: &mut Context,
        base: &str,
        off: u16,
        value: Expr,
    ) -> Result<(), Error> {
        let v = self.full(cx, base)?;
        let w = cx.width(v)?.bits();
        let vw = cx.width(value)?.bits();
        let new = if off == 0 && vw == w {
            value
        } else {
            let lo_bits = 8 * off;
            let hi_lo = lo_bits + vw;
            let mut acc = value;
            if lo_bits > 0 {
                let lo = cx.extract(v, 0, Width::new(lo_bits)?)?;
                acc = cx.concat(acc, lo)?;
            }
            if hi_lo < w {
                let hi = cx.extract(v, hi_lo, Width::new(w - hi_lo)?)?;
                acc = cx.concat(hi, acc)?;
            }
            acc
        };
        self.value.insert(base.to_string(), new);
        if !self.written.iter().any(|n| n == base) {
            self.written.push(base.to_string());
        }
        Ok(())
    }

    pub(crate) fn outputs(&self) -> Vec<(String, Expr)> {
        self.written
            .iter()
            .map(|n| (n.clone(), self.value[n]))
            .collect()
    }
}

/// A new memory for a front end: byte cells, addresses of `addr` bits.
pub(crate) fn memory(addr: Width, endian: Endian) -> Memory {
    Memory::new("mem", addr, Width::W8, endian)
}

/// An error with a line number.
pub(crate) fn at_line(line: usize, m: impl core::fmt::Display) -> Error {
    Error::Unsupported(format!("line {line}: {m}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::Engine;

    fn simplified(cx: &mut Context, e: Expr) -> String {
        let out = Engine::standard().simplify(cx, e).unwrap();
        cx.display(out.expr).to_string()
    }

    #[test]
    fn pcode_blocks() {
        let mut cx = Context::new();
        // x86-64: push rbp; mov rbp, rsp; mov [rbp-8], rdi; mov eax, [rbp-8]; add eax, 1;
        // pop rbp — with numeric register offsets as Ghidra prints them.
        let b = pcode(
            &mut cx,
            "0x1000: (unique, 0xe80, 8) = COPY (register, 0x28, 8)
             (register, 0x20, 8) = INT_SUB (register, 0x20, 8) , (const, 0x8, 8)
             STORE (const, 0x1b1, 4) , (register, 0x20, 8) , (unique, 0xe80, 8)
             (register, 0x28, 8) = COPY (register, 0x20, 8)
             (unique, 0x3100, 8) = INT_ADD (register, 0x28, 8) , (const, 0xfffffffffffffff8, 8)
             STORE (const, 0x1b1, 4) , (unique, 0x3100, 8) , (register, 0x38, 8)
             (unique, 0x3100, 8) = INT_ADD (register, 0x28, 8) , (const, 0xfffffffffffffff8, 8)
             (register, 0x0, 4) = LOAD (const, 0x1b1, 4) , (unique, 0x3100, 8)
             (register, 0x0, 4) = INT_ADD (register, 0x0, 4) , (const, 0x1, 4)
             (register, 0x28, 8) = LOAD (const, 0x1b1, 4) , (register, 0x20, 8)
             (register, 0x20, 8) = INT_ADD (register, 0x20, 8) , (const, 0x8, 8)
             RETURN (register, 0x288, 8)",
        )
        .unwrap();
        // eax is the low half of rdi plus 1; rbp and rsp are restored.
        let rax = b.register("reg_0x0").unwrap();
        let eax = cx.extract(rax, 0, Width::W32).unwrap();
        assert_eq!(simplified(&mut cx, eax), "trunc<32>(reg_0x38) + 1");
        let rbp = b.register("reg_0x28").unwrap();
        assert_eq!(simplified(&mut cx, rbp), "reg_0x28");
        let rsp = b.register("reg_0x20").unwrap();
        assert_eq!(simplified(&mut cx, rsp), "reg_0x20");
        assert_eq!(b.stores.len(), 2);
        assert!(b.next.is_some());
        // Named registers, parts of them, and a conditional exit.
        let mut cx = Context::new();
        let b = pcode(
            &mut cx,
            "(register, AL, 1) = INT_ADD (register, AL, 1) , (register, AH, 1)
             (unique, 0x10, 1) = INT_EQUAL (register, AL, 1) , (const, 0x0, 1)
             CBRANCH (ram, 0x401020, 8) , (unique, 0x10, 1)
             (register, RCX, 8) = INT_ZEXT (register, AX, 2)",
        )
        .unwrap();
        let rcx = b.register("RCX").unwrap();
        assert_eq!(
            simplified(&mut cx, rcx),
            "concat(extract<8, 56>(RAX), extract<8, 8>(RAX) + trunc<8>(RAX)) & 65535"
        );
        assert_eq!(b.exits.len(), 1);
    }

    #[test]
    fn vex_blocks() {
        let mut cx = Context::new();
        // x ^ y + 2 · (x & y), lifted.
        let b = vex(
            &mut cx,
            "IRSB {
               t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I1

               00 | ------ IMark(0x401000, 3, 0) ------
               01 | t0 = GET:I64(rdi)
               02 | t1 = GET:I64(rsi)
               03 | t2 = Xor64(t0,t1)
               04 | t3 = And64(t0,t1)
               05 | t4 = Shl64(t3,0x01)
               06 | t5 = Add64(t2,t4)
               07 | PUT(rax) = t5
               08 | STle(t0) = t5
               09 | t6 = CmpEQ64(t5,0x0000000000000000)
               10 | if (t6) { PUT(rip) = 0x0000000000401010; Ijk_Boring }
               NEXT: PUT(rip) = 0x0000000000401008; Ijk_Boring
             }",
        )
        .unwrap();
        let rax = b.register("rax").unwrap();
        assert_eq!(simplified(&mut cx, rax), "rdi + rsi");
        assert_eq!(b.stores.len(), 1);
        assert_eq!(b.exits.len(), 1);
        // A 32-bit part and a load through the store.
        let mut cx = Context::new();
        let b = vex(
            &mut cx,
            "t0 = GET:I64(rsp)
             STle(t0) = 0x0000002a
             t1 = LDle:I32(t0)
             t2 = 32Uto64(t1)
             PUT(rax) = t2
             PUT(ecx) = t1",
        )
        .unwrap();
        assert_eq!(simplified(&mut cx, b.register("rax").unwrap()), "42:64");
        let rcx = b.register("rcx").unwrap();
        assert_eq!(
            simplified(&mut cx, rcx),
            "concat(extract<32, 32>(rcx), 42:32)"
        );
    }

    #[cfg(feature = "prove")]
    #[test]
    fn llvm_functions() {
        let mut cx = Context::new();
        let b = llvm(
            &mut cx,
            "define i32 @f(ptr %p, i32 %x, i32 %y) {
               %a = xor i32 %x, %y
               %b = and i32 %x, %y
               %c = shl i32 %b, 1
               %s = getelementptr inbounds i32, ptr %p, i64 1
               store i32 %a, ptr %s, align 4
               store i32 %c, ptr %p, align 4
               %l0 = load i32, ptr %p, align 4
               %l1 = load i32, ptr %s, align 4
               %r = add i32 %l1, %l0
               ret i32 %r
             }",
            None,
        )
        .unwrap();
        let ret = b.register("ret").unwrap();
        assert_eq!(simplified(&mut cx, ret), "x + y");
        assert_eq!(b.stores.len(), 2);
    }
}

//! Memory as expressions: loads and stores over an array from addresses to cells, resolved at
//! construction into the operators bitwright already has, so the simplifier, the facts, the
//! prover and SMT-LIB export work on them unchanged.
//!
//! A load reads each cell through the stores made before it, newest first: a store whose
//! address is equal (the builder or the facts decide it) gives the cell; one whose address is
//! different is skipped; one that may be either becomes a `select` on the address equality.
//! What no store covers comes from the base: known contents where the address is in a region
//! of them, and otherwise an unknown cell, a fresh symbol per read, made consistent with the
//! earlier reads of unknown cells by selecting on address equality too (so two reads at equal
//! addresses are equal, whatever the addresses are written as).
//!
//! ```
//! use bitwright::memory::{Endian, Memory};
//! use bitwright::{Context, ParseOptions, Width};
//!
//! let mut cx = Context::new();
//! let o = ParseOptions::width(Width::W64);
//! let (sp, x) = (cx.parse("sp", &o)?, cx.parse("x", &o)?);
//! let mut mem = Memory::new("mem", Width::W64, Width::W8, Endian::Little);
//! let m0 = mem.initial();
//! // Spill x to [sp - 8], then read it back and add 1.
//! let slot = cx.parse("sp - 8", &o)?;
//! let m1 = mem.store(&mut cx, m0, slot, x)?;
//! let back = mem.load(&mut cx, m1, slot, 8)?;
//! assert_eq!(back, x);
//! // A read at [sp] is not the spill: an unknown cell of memory before it.
//! let other = mem.load(&mut cx, m1, sp, 1)?;
//! assert_eq!(cx.display(other).to_string(), "mem.0");
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

use std::collections::HashMap;

use crate::{BinOp, BitVec, CmpOpExt, Context, Error, Expr, Query, SymbolKey, Truth, View, Width};

/// How a value wider than a cell lies in consecutive cells.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Endian {
    /// The first cell holds the least significant part.
    Little,
    /// The first cell holds the most significant part.
    Big,
}

/// A version of a memory: its state after some stores.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Version(u32);

#[derive(Clone)]
struct Store {
    parent: Option<Version>,
    addr: Expr,
    cell: Expr,
}

/// A region of known contents.
#[derive(Clone)]
struct Region {
    start: BitVec,
    cells: Vec<BitVec>,
}

/// A memory (see the [module](self) documentation).
#[derive(Clone)]
pub struct Memory {
    name: String,
    addr: Width,
    cell: Width,
    endian: Endian,
    /// Unknown cells read as zero, not as symbols.
    zeroed: bool,
    regions: Vec<Region>,
    /// Version `k + 1` is store `k`; version 0 has no stores.
    stores: Vec<Store>,
    /// Reads of unknown cells: address and symbol, in order.
    reads: Vec<(Expr, Expr)>,
    /// Loads already built, by version and address.
    cache: HashMap<(Version, Expr), Expr>,
}

impl core::fmt::Debug for Memory {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Memory")
            .field("name", &self.name)
            .field("addr", &self.addr)
            .field("cell", &self.cell)
            .field("endian", &self.endian)
            .field("regions", &self.regions.len())
            .field("stores", &self.stores.len())
            .field("reads", &self.reads.len())
            .finish()
    }
}

impl Memory {
    /// A memory named `name` (its unknown cells are the symbols `name.0`, `name.1`, …) from
    /// addresses of width `addr` to cells of width `cell`, all of it unknown.
    pub fn new(name: &str, addr: Width, cell: Width, endian: Endian) -> Memory {
        Memory {
            name: name.to_string(),
            addr,
            cell,
            endian,
            zeroed: false,
            regions: Vec::new(),
            stores: Vec::new(),
            reads: Vec::new(),
            cache: HashMap::new(),
        }
    }

    /// Unknown cells read as zero instead (memory that starts cleared).
    pub fn zeroed(mut self) -> Memory {
        self.zeroed = true;
        self
    }

    /// Known contents from address `start` on, one value per cell (for example a binary's
    /// read-only data). Regions must not overlap.
    pub fn with_region(mut self, start: u128, cells: &[BitVec]) -> Result<Memory, Error> {
        for c in cells {
            if c.width() != self.cell {
                return Err(crate::WidthError::Mismatch {
                    left: self.cell.bits(),
                    right: c.width().bits(),
                }
                .into());
            }
        }
        let start = BitVec::from_u128(self.addr, start)?;
        self.regions.push(Region {
            start,
            cells: cells.to_vec(),
        });
        Ok(self)
    }

    /// Known contents of byte cells from address `start` on.
    pub fn with_bytes(self, start: u128, bytes: &[u8]) -> Result<Memory, Error> {
        let cells: Vec<BitVec> = bytes
            .iter()
            .map(|&b| BitVec::wrapping_from_u64(Width::W8, u64::from(b)))
            .collect();
        self.with_region(start, &cells)
    }

    /// The memory before any store.
    pub fn initial(&self) -> Version {
        Version(0)
    }

    /// The address width.
    pub fn addr_width(&self) -> Width {
        self.addr
    }

    /// The cell width.
    pub fn cell_width(&self) -> Width {
        self.cell
    }

    fn parent(&self, v: Version) -> Option<(Version, &Store)> {
        if v.0 == 0 {
            return None;
        }
        let s = &self.stores[v.0 as usize - 1];
        Some((s.parent.unwrap_or(Version(0)), s))
    }

    /// An address as a base (none for a constant) plus a constant offset.
    fn split(cx: &Context, e: Expr) -> Result<(Option<Expr>, BitVec), Error> {
        Ok(match cx.view(e)? {
            View::Const(c) => (None, c),
            View::Bin(BinOp::Add, a, b) => match cx.view(b)? {
                View::Const(c) => {
                    let (base, off) = Self::split(cx, a)?;
                    (base, BitVec::apply_bin(BinOp::Add, &off, &c)?)
                }
                _ => (Some(e), BitVec::zero(cx.width(e)?)),
            },
            _ => (Some(e), BitVec::zero(cx.width(e)?)),
        })
    }

    /// `addr + k`, written as its base plus one offset (so an address has one form however it
    /// was reached).
    fn offset(&self, cx: &mut Context, addr: Expr, k: u64) -> Result<Expr, Error> {
        let (base, off) = Self::split(cx, addr)?;
        let off = BitVec::apply_bin(BinOp::Add, &off, &BitVec::wrapping_from_u64(self.addr, k))?;
        let c = cx.constant(&off)?;
        match base {
            None => Ok(c),
            Some(b) if off.is_zero() => Ok(b),
            Some(b) => cx.bin(BinOp::Add, b, c),
        }
    }

    /// The cells of a value, in address order.
    fn cells_of(&self, cx: &mut Context, value: Expr) -> Result<Vec<Expr>, Error> {
        let w = cx.width(value)?.bits();
        let c = self.cell.bits();
        if w % c != 0 {
            return Err(Error::Unsupported(format!(
                "a {w}-bit value is not a whole number of {c}-bit cells"
            )));
        }
        let n = w / c;
        let mut out = Vec::with_capacity(n as usize);
        for k in 0..n {
            // Little-endian: cell k holds bits [k·c, (k + 1)·c).
            let lo = match self.endian {
                Endian::Little => k * c,
                Endian::Big => (n - 1 - k) * c,
            };
            out.push(if n == 1 {
                value
            } else {
                cx.extract(value, lo, self.cell)?
            });
        }
        Ok(out)
    }

    /// Stores `value` (a whole number of cells) at `addr` in version `at`: the new version.
    pub fn store(
        &mut self,
        cx: &mut Context,
        at: Version,
        addr: Expr,
        value: Expr,
    ) -> Result<Version, Error> {
        self.check_addr(cx, addr)?;
        let cells = self.cells_of(cx, value)?;
        let mut v = at;
        for (k, cell) in cells.into_iter().enumerate() {
            let a = self.offset(cx, addr, k as u64)?;
            self.stores.push(Store {
                parent: Some(v),
                addr: a,
                cell,
            });
            v = Version(self.stores.len() as u32);
        }
        Ok(v)
    }

    fn check_addr(&self, cx: &Context, addr: Expr) -> Result<(), Error> {
        let w = cx.width(addr)?;
        if w != self.addr {
            return Err(crate::WidthError::Mismatch {
                left: self.addr.bits(),
                right: w.bits(),
            }
            .into());
        }
        Ok(())
    }

    /// Loads `cells` consecutive cells at `addr` from version `at`, as one value.
    pub fn load(
        &mut self,
        cx: &mut Context,
        at: Version,
        addr: Expr,
        cells: u16,
    ) -> Result<Expr, Error> {
        self.check_addr(cx, addr)?;
        if cells == 0 {
            return Err(Error::Unsupported("a load of no cells".into()));
        }
        let mut parts = Vec::with_capacity(cells as usize);
        for k in 0..cells {
            let a = self.offset(cx, addr, u64::from(k))?;
            parts.push(self.cell_at(cx, at, a)?);
        }
        // Least significant first; adjacent pieces of one value merge back into it.
        if self.endian == Endian::Big {
            parts.reverse();
        }
        let mut runs: Vec<(Expr, u16, u16)> = Vec::new();
        for p in parts {
            let w = cx.width(p)?.bits();
            let (src, lo) = match cx.view(p)? {
                View::Extract { lo, src } => (src, lo),
                _ => (p, 0),
            };
            match runs.last_mut() {
                Some((s, l, n)) if *s == src && *l + *n == lo => *n += w,
                _ => runs.push((src, lo, w)),
            }
        }
        let mut v: Option<Expr> = None;
        for (src, lo, n) in runs {
            let piece = if lo == 0 && n == cx.width(src)?.bits() {
                src
            } else {
                cx.extract(src, lo, Width::new(n)?)?
            };
            v = Some(match v {
                None => piece,
                Some(low) => cx.concat(piece, low)?,
            });
        }
        Ok(v.expect("at least one cell"))
    }

    /// Whether `a = b` is decided: `Ok(true)`, `Ok(false)`, or `Err` with the 1-bit equality
    /// to select on. One base: the offsets decide; else the builder or the facts may.
    fn same(cx: &mut Context, a: Expr, b: Expr) -> Result<Result<bool, Expr>, Error> {
        let ((ba, oa), (bb, ob)) = (Self::split(cx, a)?, Self::split(cx, b)?);
        if ba == bb {
            return Ok(Ok(oa == ob));
        }
        let eq = cx.cmp(CmpOpExt::Eq, a, b)?;
        if let Some(v) = cx.as_const(eq)? {
            return Ok(Ok(!v.is_zero()));
        }
        Ok(match cx.prove(Query::Eq(a, b))? {
            Truth::True => Ok(true),
            Truth::False => Ok(false),
            _ => Err(eq),
        })
    }

    /// The cell at `a` in version `at`.
    fn cell_at(&mut self, cx: &mut Context, at: Version, a: Expr) -> Result<Expr, Error> {
        if let Some(&e) = self.cache.get(&(at, a)) {
            return Ok(e);
        }
        // Stores newest first; undecided ones become selects around what is below them.
        let mut pending: Vec<(Expr, Expr)> = Vec::new();
        let mut found = None;
        let mut v = at;
        while let Some((parent, s)) = self.parent(v) {
            let (sa, sc) = (s.addr, s.cell);
            match Self::same(cx, a, sa)? {
                Ok(true) => {
                    found = Some(sc);
                    break;
                }
                Ok(false) => {}
                Err(eq) => pending.push((eq, sc)),
            }
            v = parent;
        }
        let mut value = match found {
            Some(c) => c,
            None => self.base(cx, a)?,
        };
        for &(eq, c) in pending.iter().rev() {
            value = cx.select(eq, c, value)?;
        }
        self.cache.insert((at, a), value);
        Ok(value)
    }

    /// The cell at `a` before any store.
    fn base(&mut self, cx: &mut Context, a: Expr) -> Result<Expr, Error> {
        // Known contents: a constant address in a region is its cell; an address that may
        // be in one selects its cell by the offset.
        let mut known: Vec<(Expr, Expr)> = Vec::new();
        for r in 0..self.regions.len() {
            let len = self.regions[r].cells.len() as u128;
            let start = self.regions[r].start;
            // The offset into the region, as its base plus one constant.
            let neg = BitVec::apply_un(crate::UnOp::Neg, &start)?;
            let off = match neg.to_u128() {
                Some(k) => self.offset(cx, a, k as u64)?,
                None => {
                    let s = cx.constant(&start)?;
                    cx.bin(BinOp::Sub, a, s)?
                }
            };
            let lim = cx.constant(&BitVec::wrapping_from_u128(self.addr, len))?;
            let inside = cx.cmp(CmpOpExt::Ult, off, lim)?;
            let decided = match cx.as_const(inside)? {
                Some(v) => Some(!v.is_zero()),
                None => match cx.prove(Query::Cmp(CmpOpExt::Ult, off, lim))? {
                    Truth::True => Some(true),
                    Truth::False => Some(false),
                    _ => None,
                },
            };
            match decided {
                Some(false) => continue,
                Some(true) => {
                    let off_v = cx.as_const(off)?;
                    if let Some(k) = off_v.and_then(|k| k.to_u64()) {
                        return cx.constant(&self.regions[r].cells[k as usize]);
                    }
                    return self.table(cx, r, off);
                }
                None => {
                    let t = self.table(cx, r, off)?;
                    known.push((inside, t));
                }
            }
        }
        let mut value = self.unknown(cx, a)?;
        for (inside, t) in known.into_iter().rev() {
            value = cx.select(inside, t, value)?;
        }
        Ok(value)
    }

    /// Region `r`'s cell at offset `off` (a tree of selects on the offset's bits).
    fn table(&mut self, cx: &mut Context, r: usize, off: Expr) -> Result<Expr, Error> {
        let n = self.regions[r].cells.len();
        if n > 4096 {
            return Err(Error::Unsupported(format!(
                "a load at an unknown offset into a region of {n} cells (at most 4096)"
            )));
        }
        let bits = (usize::BITS - (n.max(2) - 1).leading_zeros()) as u16;
        let cells: Vec<BitVec> = self.regions[r].cells.clone();
        let zero = BitVec::zero(self.cell);
        // Level 0: the cells (padded); each level selects on one offset bit.
        let mut level: Vec<Expr> = Vec::with_capacity(1 << bits);
        for k in 0..(1usize << bits) {
            level.push(cx.constant(cells.get(k).unwrap_or(&zero))?);
        }
        for b in 0..bits {
            let bit = cx.bit(off, b)?;
            level = level
                .chunks(2)
                .map(|p| cx.select(bit, p[1], p[0]))
                .collect::<Result<_, _>>()?;
        }
        Ok(level[0])
    }

    /// An unknown cell at `a`: the cell an earlier read at an equal address got, else a fresh
    /// symbol.
    fn unknown(&mut self, cx: &mut Context, a: Expr) -> Result<Expr, Error> {
        if self.zeroed {
            return cx.zero(self.cell);
        }
        let mut pending: Vec<(Expr, Expr)> = Vec::new();
        for k in 0..self.reads.len() {
            let (ra, rs) = self.reads[k];
            match Self::same(cx, a, ra)? {
                Ok(true) => return Ok(rs),
                Ok(false) => {}
                Err(eq) => pending.push((eq, rs)),
            }
        }
        let key = SymbolKey::from(format!("{}.{}", self.name, self.reads.len()).as_str());
        let s = cx.symbol(key, self.cell)?;
        self.reads.push((a, s));
        // Earlier reads first: the first one at an equal address answers.
        let mut value = s;
        for &(eq, rs) in pending.iter().rev() {
            value = cx.select(eq, rs, value)?;
        }
        Ok(value)
    }

    /// The reads of unknown cells so far: each one's address and symbol, in order.
    pub fn reads(&self) -> &[(Expr, Expr)] {
        &self.reads
    }

    /// Values for the symbols of the unknown cells read so far, from a memory image and the
    /// values of the other symbols (a read's address may depend on them, and on earlier reads):
    /// each address is evaluated in turn and the image asked for its cell (`None`: 0).
    pub fn bind(
        &self,
        cx: &mut Context,
        env: &[(SymbolKey, BitVec)],
        image: &dyn Fn(&BitVec) -> Option<BitVec>,
    ) -> Result<Vec<(SymbolKey, BitVec)>, Error> {
        let mut out: Vec<(SymbolKey, BitVec)> = env.to_vec();
        for &(a, s) in &self.reads {
            let addr = cx.eval(&[a], &out[..])?.remove(0);
            let v = image(&addr).unwrap_or_else(|| BitVec::zero(self.cell));
            let id = cx
                .symbol_id(s)?
                .ok_or_else(|| Error::Contract("a read without its symbol".into()))?;
            let key = cx
                .symbol_key(id)
                .cloned()
                .ok_or_else(|| Error::Contract("a symbol without its key".into()))?;
            out.push((key, v));
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseOptions, Width};

    fn setup() -> (Context, ParseOptions) {
        (Context::new(), ParseOptions::width(Width::W32))
    }

    #[test]
    fn forwarding_and_overlap() {
        let (mut cx, o) = setup();
        let mut m = Memory::new("m", Width::W32, Width::W8, Endian::Little);
        let p = cx.parse("p", &o).unwrap();
        let x = cx.parse("x", &o).unwrap();
        let v1 = m.store(&mut cx, m.initial(), p, x).unwrap();
        // The whole value back, and its middle bytes at p + 1.
        assert_eq!(m.load(&mut cx, v1, p, 4).unwrap(), x);
        let p1 = cx.parse("p + 1", &o).unwrap();
        let mid = m.load(&mut cx, v1, p1, 2).unwrap();
        assert_eq!(cx.display(mid).to_string(), "extract<8, 16>(x)");
        // Past the store: unknown bytes of the memory before it.
        let p4 = cx.parse("p + 4", &o).unwrap();
        let after = m.load(&mut cx, v1, p4, 1).unwrap();
        assert_eq!(cx.display(after).to_string(), "m.0");
        // A later store shadows an earlier one; the earlier version is unchanged.
        let y = cx.parse("y", &o).unwrap();
        let yb = cx.trunc(y, Width::W8).unwrap();
        let v2 = m.store(&mut cx, v1, p, yb).unwrap();
        let low = m.load(&mut cx, v2, p, 1).unwrap();
        assert_eq!(low, yb);
        let old = m.load(&mut cx, v1, p, 1).unwrap();
        assert_eq!(cx.display(old).to_string(), "trunc<8>(x)");
    }

    #[test]
    fn aliasing_is_a_select_and_reads_are_consistent() {
        let (mut cx, o) = setup();
        let mut m = Memory::new("m", Width::W32, Width::W8, Endian::Little);
        let (p, q) = (cx.parse("p", &o).unwrap(), cx.parse("q", &o).unwrap());
        let x8 = cx.parse("x", &ParseOptions::width(Width::W8)).unwrap();
        let v1 = m.store(&mut cx, m.initial(), p, x8).unwrap();
        let at_q = m.load(&mut cx, v1, q, 1).unwrap();
        assert_eq!(cx.display(at_q).to_string(), "select(p == q, x, m.0)");
        // Two reads of unknown memory at addresses that may be equal agree when they are
        // (proved by the native prover, when it is built).
        #[cfg(feature = "prove")]
        {
            let r1 = m.load(&mut cx, m.initial(), p, 1).unwrap();
            let r2 = m.load(&mut cx, m.initial(), q, 1).unwrap();
            let same = cx.cmp(CmpOpExt::Eq, p, q).unwrap();
            let eq = cx.cmp(CmpOpExt::Eq, r1, r2).unwrap();
            let claim = {
                let n = cx.un(crate::UnOp::Not, same).unwrap();
                cx.bin(BinOp::Or, n, eq).unwrap()
            };
            assert!(matches!(
                crate::prove::valid(&mut cx, claim, &crate::prove::Config::default()).unwrap(),
                crate::prove::Outcome::Proved(_)
            ));
        }
    }

    #[test]
    fn known_regions_and_images() {
        let (mut cx, o) = setup();
        // A lookup table at 0x1000: an S-box of 16 entries.
        let sbox: Vec<u8> = (0..16u8).map(|i| i.wrapping_mul(7) ^ 5).collect();
        let mut m = Memory::new("m", Width::W32, Width::W8, Endian::Little)
            .with_bytes(0x1000, &sbox)
            .unwrap();
        let k = cx.parse("0x1000 + 3", &o).unwrap();
        let c = m.load(&mut cx, m.initial(), k, 1).unwrap();
        assert_eq!(
            cx.as_const(c).unwrap().unwrap().to_u64(),
            Some(u64::from(sbox[3]))
        );
        // At an index known to be in range, a table; evaluated, the entries.
        let i = cx.parse("0x1000 + (i & 15)", &o).unwrap();
        let t = m.load(&mut cx, m.initial(), i, 1).unwrap();
        assert!(m.reads().is_empty());
        for idx in 0..16u64 {
            let env = [(
                SymbolKey::from("i"),
                BitVec::wrapping_from_u64(Width::W32, idx),
            )];
            let v = cx.eval(&[t], &env[..]).unwrap()[0];
            assert_eq!(v.to_u64(), Some(u64::from(sbox[idx as usize])));
        }
        // Anywhere: the table if inside, an unknown cell if not; bound from an image.
        let j = cx.parse("j", &o).unwrap();
        let u = m.load(&mut cx, m.initial(), j, 2).unwrap();
        let image = |a: &BitVec| {
            a.to_u64()
                .map(|a| BitVec::wrapping_from_u64(Width::W8, a ^ 0xaa))
        };
        for addr in [0x1000u64, 0x100f, 0x2000] {
            let env = [(
                SymbolKey::from("j"),
                BitVec::wrapping_from_u64(Width::W32, addr),
            )];
            let bound = m.bind(&mut cx, &env, &image).unwrap();
            let v = cx.eval(&[u], &bound[..]).unwrap()[0].to_u64().unwrap();
            let byte = |a: u64| {
                if (0x1000..0x1010).contains(&a) {
                    u64::from(sbox[(a - 0x1000) as usize])
                } else {
                    (a ^ 0xaa) & 0xff
                }
            };
            assert_eq!(v, byte(addr) | byte(addr + 1) << 8, "{addr:#x}");
        }
    }

    #[test]
    fn big_endian_and_simplification() {
        let (mut cx, o) = setup();
        let mut m = Memory::new("m", Width::W32, Width::W8, Endian::Big);
        let p = cx.parse("sp - 16", &o).unwrap();
        let x = cx.parse("x", &o).unwrap();
        let v = m.store(&mut cx, m.initial(), p, x).unwrap();
        let first = m.load(&mut cx, v, p, 1).unwrap();
        assert_eq!(cx.display(first).to_string(), "extract<24, 8>(x)");
        // A spilled value reloaded and used is the value.
        let back = m.load(&mut cx, v, p, 4).unwrap();
        let one = cx.one(Width::W32).unwrap();
        let e = cx.bin(BinOp::Add, back, one).unwrap();
        assert_eq!(cx.display(e).to_string(), "x + 1");
    }
}

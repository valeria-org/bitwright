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
use std::sync::atomic::{AtomicU64, Ordering};

use crate::{BinOp, BitVec, CmpOpExt, Context, Error, Expr, Query, SymbolKey, Truth, View, Width};

/// How a value wider than a cell lies in consecutive cells.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Endian {
    /// The first cell holds the least significant part.
    Little,
    /// The first cell holds the most significant part.
    Big,
}

/// A version of a memory: its state after some stores. A clone accepts the versions shared
/// at the time of cloning, but not versions created later on a different clone branch.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Version(u32, u64);

fn fresh_version(index: u32) -> Version {
    static NEXT: AtomicU64 = AtomicU64::new(1);
    Version(index, NEXT.fetch_add(1, Ordering::Relaxed))
}

#[derive(Clone)]
struct Store {
    version: Version,
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
    initial: Version,
    /// Version `k + 1` is store `k`; version 0 has no stores.
    stores: Vec<Store>,
    /// Reads of unknown cells: address and symbol, in order.
    reads: Vec<(Expr, Expr)>,
    /// Next named read to try; occupied symbol names are skipped.
    next_read: usize,
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

const MAX_BULK_CELLS: u16 = 4096;

impl Memory {
    /// A memory named `name` (its unknown cells use unused symbols `name.0`, `name.1`, …)
    /// from addresses of width `addr` to cells of width `cell`, all of it unknown.
    pub fn new(name: &str, addr: Width, cell: Width, endian: Endian) -> Memory {
        Memory {
            name: name.to_string(),
            addr,
            cell,
            endian,
            zeroed: false,
            regions: Vec::new(),
            initial: fresh_version(0),
            stores: Vec::new(),
            reads: Vec::new(),
            next_read: 0,
            cache: HashMap::new(),
        }
    }

    /// Unknown cells read as zero instead (memory that starts cleared). Previously returned
    /// load expressions retain their original contents.
    pub fn zeroed(mut self) -> Memory {
        self.zeroed = true;
        self.cache.clear();
        self
    }

    /// Known contents from address `start` on, one value per cell (for example a binary's
    /// read-only data). Regions must not overlap, including themselves when addresses wrap.
    /// Previously returned load expressions retain their original contents.
    pub fn with_region(mut self, start: u128, cells: &[BitVec]) -> Result<Memory, Error> {
        if self.addr.bits() < 128 && cells.len() as u128 > (1u128 << self.addr.bits()) {
            return Err(Error::Unsupported(
                "a known region exceeds the memory's address space".into(),
            ));
        }
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
        self.cache.clear();
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
        self.initial
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
        Some((s.parent.unwrap_or(self.initial), s))
    }

    fn check_version(&self, v: Version) -> Result<(), Error> {
        let known = if v.0 == 0 {
            v == self.initial
        } else {
            self.stores
                .get(v.0 as usize - 1)
                .is_some_and(|s| s.version == v)
        };
        if known {
            Ok(())
        } else {
            Err(Error::Unsupported(
                "a version from another memory or clone branch".into(),
            ))
        }
    }

    /// An address as a base (none for a constant) plus a constant offset.
    fn split(cx: &Context, mut e: Expr) -> Result<(Option<Expr>, BitVec), Error> {
        let mut off = BitVec::zero(cx.width(e)?);
        loop {
            match cx.view(e)? {
                View::Const(c) => return Ok((None, BitVec::apply_bin(BinOp::Add, &off, &c)?)),
                View::Bin(BinOp::Add, a, b) => match (cx.view(a)?, cx.view(b)?) {
                    (_, View::Const(c)) => {
                        off = BitVec::apply_bin(BinOp::Add, &off, &c)?;
                        e = a;
                    }
                    (View::Const(c), _) => {
                        off = BitVec::apply_bin(BinOp::Add, &off, &c)?;
                        e = b;
                    }
                    _ => return Ok((Some(e), off)),
                },
                View::Bin(BinOp::Sub, a, b) => match cx.view(b)? {
                    View::Const(c) => {
                        off = BitVec::apply_bin(BinOp::Sub, &off, &c)?;
                        e = a;
                    }
                    _ => return Ok((Some(e), off)),
                },
                _ => return Ok((Some(e), off)),
            }
        }
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

    fn push_cell(&mut self, parent: Version, addr: Expr, cell: Expr) -> Version {
        let next = fresh_version(self.stores.len() as u32 + 1);
        self.stores.push(Store {
            version: next,
            parent: Some(parent),
            addr,
            cell,
        });
        next
    }

    /// Drops stores in `newest_first` whose address is overwritten by a later store in the
    /// same branch, returning the surviving stores oldest-to-newest.
    fn dedup_branch(
        cx: &mut Context,
        newest_first: Vec<(Expr, Expr)>,
    ) -> Result<Vec<(Expr, Expr)>, Error> {
        let mut kept: Vec<(Expr, Expr)> = Vec::with_capacity(newest_first.len());
        'scan: for (addr, cell) in newest_first {
            for &(later_addr, _) in &kept {
                if matches!(Self::same(cx, addr, later_addr)?, Ok(true)) {
                    continue 'scan;
                }
            }
            kept.push((addr, cell));
        }
        kept.reverse();
        Ok(kept)
    }

    /// Stores `value` (a whole number of cells) at `addr` in version `at`: the new version.
    pub fn store(
        &mut self,
        cx: &mut Context,
        at: Version,
        addr: Expr,
        value: Expr,
    ) -> Result<Version, Error> {
        self.check_version(at)?;
        self.check_addr(cx, addr)?;
        let cells = self.cells_of(cx, value)?;
        let mut v = at;
        for (k, cell) in cells.into_iter().enumerate() {
            let a = self.offset(cx, addr, k as u64)?;
            v = self.push_cell(v, a, cell);
        }
        Ok(v)
    }

    /// Stores `cell_value` (one cell) into `cells` consecutive cells starting at `addr` in
    /// version `at`.
    pub fn memset(
        &mut self,
        cx: &mut Context,
        at: Version,
        addr: Expr,
        cell_value: Expr,
        cells: u16,
    ) -> Result<Version, Error> {
        self.check_version(at)?;
        self.check_addr(cx, addr)?;
        let vw = cx.width(cell_value)?;
        if vw != self.cell {
            return Err(crate::WidthError::Mismatch {
                left: self.cell.bits(),
                right: vw.bits(),
            }
            .into());
        }
        if cells > MAX_BULK_CELLS {
            return Err(Error::Unsupported(format!(
                "a memset of {cells} cells (at most {MAX_BULK_CELLS})"
            )));
        }
        let mut v = at;
        for k in 0..cells {
            let a = self.offset(cx, addr, u64::from(k))?;
            v = self.push_cell(v, a, cell_value);
        }
        Ok(v)
    }

    /// Copies `cells` consecutive cells from `src` to `dst` in version `at`.
    ///
    /// Source cells are snapshotted from `at` before any destination cell is written, so
    /// overlapping ranges behave like `memmove`.
    pub fn memcpy(
        &mut self,
        cx: &mut Context,
        at: Version,
        dst: Expr,
        src: Expr,
        cells: u16,
    ) -> Result<Version, Error> {
        self.check_version(at)?;
        self.check_addr(cx, dst)?;
        self.check_addr(cx, src)?;
        if cells > MAX_BULK_CELLS {
            return Err(Error::Unsupported(format!(
                "a memcpy of {cells} cells (at most {MAX_BULK_CELLS})"
            )));
        }
        if cells == 0 || matches!(Self::same(cx, dst, src)?, Ok(true)) {
            return Ok(at);
        }
        let mut snapshot = Vec::with_capacity(cells as usize);
        for k in 0..cells {
            let s = self.offset(cx, src, u64::from(k))?;
            snapshot.push(self.cell_at(cx, at, s)?);
        }
        let mut v = at;
        for (k, cell) in snapshot.into_iter().enumerate() {
            let d = self.offset(cx, dst, k as u64)?;
            v = self.push_cell(v, d, cell);
        }
        Ok(v)
    }

    /// Joins two versions of this memory under the 1-bit condition `cond`: a load from the
    /// returned version reads `v_then` when `cond` is 1 and `v_else` when `cond` is 0.
    pub fn merge(
        &mut self,
        cx: &mut Context,
        cond: Expr,
        v_then: Version,
        v_else: Version,
    ) -> Result<Version, Error> {
        self.check_version(v_then)?;
        self.check_version(v_else)?;
        let cw = cx.width(cond)?;
        if cw != Width::W1 {
            return Err(crate::WidthError::Mismatch {
                left: 1,
                right: cw.bits(),
            }
            .into());
        }
        if v_then == v_else {
            return Ok(v_then);
        }
        if let Some(c) = cx.as_const(cond)? {
            return Ok(if !c.is_zero() { v_then } else { v_else });
        }

        let mut then_rev: Vec<(Expr, Expr)> = Vec::new();
        let mut else_rev: Vec<(Expr, Expr)> = Vec::new();
        let (mut a, mut b) = (v_then, v_else);
        while a != b {
            if a.0 >= b.0 {
                let (p, s) = self.parent(a).expect("checked non-initial version");
                then_rev.push((s.addr, s.cell));
                a = p;
            } else {
                let (p, s) = self.parent(b).expect("checked non-initial version");
                else_rev.push((s.addr, s.cell));
                b = p;
            }
        }
        let lca = a;

        let then_stores = Self::dedup_branch(cx, then_rev)?;
        let else_stores = Self::dedup_branch(cx, else_rev)?;

        let mut paired_then = vec![false; then_stores.len()];
        let mut has_then_match = vec![false; else_stores.len()];
        let mut skip_else = vec![false; else_stores.len()];
        let mut direct_else: Vec<Option<Expr>> = vec![None; then_stores.len()];

        for (ei, &(ae, ce)) in else_stores.iter().enumerate() {
            let mut matched_ti = None;
            for (ti, &(at, _)) in then_stores.iter().enumerate() {
                if !paired_then[ti] && matches!(Self::same(cx, ae, at)?, Ok(true)) {
                    matched_ti = Some(ti);
                    break;
                }
            }
            if let Some(ti) = matched_ti {
                paired_then[ti] = true;
                has_then_match[ei] = true;
                let at = then_stores[ti].0;
                let mut can_fuse = true;
                for &(ae_later, _) in &else_stores[ei + 1..] {
                    if !matches!(Self::same(cx, ae, ae_later)?, Ok(false))
                        || !matches!(Self::same(cx, at, ae_later)?, Ok(false))
                    {
                        can_fuse = false;
                        break;
                    }
                }
                if can_fuse {
                    for &(at_earlier, _) in &then_stores[..ti] {
                        if !matches!(Self::same(cx, ae, at_earlier)?, Ok(false))
                            || !matches!(Self::same(cx, at, at_earlier)?, Ok(false))
                        {
                            can_fuse = false;
                            break;
                        }
                    }
                }
                if can_fuse {
                    skip_else[ei] = true;
                    direct_else[ti] = Some(ce);
                }
            }
        }

        let mut v = lca;
        for (ei, &(ae, ce)) in else_stores.iter().enumerate() {
            if skip_else[ei] {
                continue;
            }
            let cell = if has_then_match[ei] {
                ce
            } else {
                let keep = self.cell_at(cx, v, ae)?;
                cx.select(cond, keep, ce)?
            };
            v = self.push_cell(v, ae, cell);
        }

        for (ti, &(at, ct)) in then_stores.iter().enumerate() {
            let else_val = match direct_else[ti] {
                Some(ce) => ce,
                None => self.cell_at(cx, v, at)?,
            };
            let cell = cx.select(cond, ct, else_val)?;
            v = self.push_cell(v, at, cell);
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
        self.check_version(at)?;
        self.check_addr(cx, addr)?;
        if cells == 0 {
            return Err(Error::Unsupported("a load of no cells".into()));
        }
        let bits = u32::from(cells) * u32::from(self.cell.bits());
        if bits > u32::from(Width::MAX_BITS) {
            return Err(crate::WidthError::Invalid { bits }.into());
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

    /// Decides `a == b` algebraically when linear reassociation, disjoint bitwise offsets,
    /// 2-adic stride alignment, bounded single-term ranges, or bit-provenance settle it without
    /// introducing a symbolic `select`.
    fn decide_linear_or_bits(cx: &mut Context, a: Expr, b: Expr) -> Result<Option<bool>, Error> {
        let w = cx.width(a)?;
        let one = BitVec::one(w);
        let neg_one = BitVec::ones(w);
        let mut konst = BitVec::zero(w);
        let mut terms: Vec<(Expr, BitVec)> = Vec::new();
        let mut todo: Vec<(Expr, BitVec)> = vec![(b, neg_one), (a, one)];
        let mut steps = 0usize;
        let mut exact = true;

        while let Some((cur, scale)) = todo.pop() {
            if scale.is_zero() {
                continue;
            }
            steps += 1;
            if steps > 64 {
                exact = false;
                break;
            }
            match cx.view(cur)? {
                View::Const(c) => {
                    let prod = BitVec::bin_unchecked(BinOp::Mul, &c, &scale);
                    konst = BitVec::bin_unchecked(BinOp::Add, &konst, &prod);
                }
                View::Bin(BinOp::Add, u, v) => {
                    todo.push((v, scale));
                    todo.push((u, scale));
                }
                View::Bin(BinOp::Sub, u, v) => {
                    todo.push((v, BitVec::un_unchecked(crate::UnOp::Neg, &scale)));
                    todo.push((u, scale));
                }
                View::Un(crate::UnOp::Neg, u) => {
                    todo.push((u, BitVec::un_unchecked(crate::UnOp::Neg, &scale)));
                }
                View::Un(crate::UnOp::Not, u) => {
                    // `~u == -u - 1`
                    konst = BitVec::bin_unchecked(BinOp::Sub, &konst, &scale);
                    todo.push((u, BitVec::un_unchecked(crate::UnOp::Neg, &scale)));
                }
                View::Bin(BinOp::Mul, u, v) => match (cx.as_const(u)?, cx.as_const(v)?) {
                    (_, Some(c)) => todo.push((u, BitVec::bin_unchecked(BinOp::Mul, &scale, &c))),
                    (Some(c), _) => todo.push((v, BitVec::bin_unchecked(BinOp::Mul, &scale, &c))),
                    _ => {
                        if let Some(slot) = terms.iter_mut().find(|t| t.0 == cur) {
                            slot.1 = BitVec::bin_unchecked(BinOp::Add, &slot.1, &scale);
                        } else if terms.len() < 16 {
                            terms.push((cur, scale));
                        } else {
                            exact = false;
                            break;
                        }
                    }
                },
                View::Bin(BinOp::Shl, u, v) => {
                    if let Some(sv) = cx.as_const(v)? {
                        let factor = BitVec::bin_unchecked(BinOp::Shl, &one, &sv);
                        if !factor.is_zero() {
                            todo.push((u, BitVec::bin_unchecked(BinOp::Mul, &scale, &factor)));
                        }
                    } else if let Some(slot) = terms.iter_mut().find(|t| t.0 == cur) {
                        slot.1 = BitVec::bin_unchecked(BinOp::Add, &slot.1, &scale);
                    } else if terms.len() < 16 {
                        terms.push((cur, scale));
                    } else {
                        exact = false;
                        break;
                    }
                }
                View::Bin(op @ (BinOp::Or | BinOp::Xor), u, v) => {
                    let (fu, fv) = (cx.facts(u)?, cx.facts(v)?);
                    let overlap = BitVec::bin_unchecked(
                        BinOp::And,
                        &fu.known().maybe_one(),
                        &fv.known().maybe_one(),
                    );
                    if overlap.is_zero() {
                        // Disjoint bit supports: `u | v == u + v` and `u ^ v == u + v`.
                        todo.push((v, scale));
                        todo.push((u, scale));
                    } else {
                        let _ = op;
                        if let Some(slot) = terms.iter_mut().find(|t| t.0 == cur) {
                            slot.1 = BitVec::bin_unchecked(BinOp::Add, &slot.1, &scale);
                        } else if terms.len() < 16 {
                            terms.push((cur, scale));
                        } else {
                            exact = false;
                            break;
                        }
                    }
                }
                _ => {
                    if let Some(slot) = terms.iter_mut().find(|t| t.0 == cur) {
                        slot.1 = BitVec::bin_unchecked(BinOp::Add, &slot.1, &scale);
                    } else if terms.len() < 16 {
                        terms.push((cur, scale));
                    } else {
                        exact = false;
                        break;
                    }
                }
            }
        }

        if exact {
            terms.retain(|(_, c)| !c.is_zero());
            if terms.is_empty() {
                return Ok(Some(konst.is_zero()));
            }
            if !konst.is_zero() {
                // 2-adic stride check: if every `coeff_i * atom_i` has more trailing zeros than
                // `konst`, `sum coeff_i * atom_i + konst == 0 (mod 2^W)` has no solution.
                let k_tz = crate::facts::known::trailing_zeros(&konst);
                let mut min_tz = u32::from(w.bits());
                for (atom, coeff) in &terms {
                    let c_tz = crate::facts::known::trailing_zeros(coeff);
                    let a_tz = cx.facts(*atom)?.known().trailing_known_zeros();
                    min_tz = min_tz.min(c_tz.saturating_add(a_tz));
                }
                if k_tz < min_tz {
                    return Ok(Some(false));
                }
                // Single residual term `t == target`: reject when outside `t`'s unsigned interval
                // or incompatible with `t`'s known bits (e.g. `sp + zext(byte)` vs `sp + 300`).
                if let [(atom, coeff)] = &terms[..] {
                    let target = if *coeff == one {
                        Some(BitVec::un_unchecked(crate::UnOp::Neg, &konst))
                    } else if *coeff == neg_one {
                        Some(konst)
                    } else {
                        None
                    };
                    if let Some(t) = target {
                        let f = cx.facts(*atom)?;
                        if !f.urange().contains(&t)
                            || !BitVec::bin_unchecked(BinOp::And, &f.known().known_zero(), &t)
                                .is_zero()
                            || BitVec::bin_unchecked(BinOp::And, &f.known().known_one(), &t)
                                != f.known().known_one()
                        {
                            return Ok(Some(false));
                        }
                    }
                }
            }
        }

        let (ia, ib) = (cx.id(a)?, cx.id(b)?);
        if let Some(ans) = crate::engine::pass::shuffle::decide_eq_by_runs(cx, ia, ib, 32) {
            return Ok(Some(ans));
        }
        Ok(None)
    }

    /// Whether `a = b` is decided: `Ok(true)`, `Ok(false)`, or `Err` with the 1-bit equality
    /// to select on. One base: the offsets decide; else linear/stride/bit analysis, the builder,
    /// or the facts may.
    fn same(cx: &mut Context, a: Expr, b: Expr) -> Result<Result<bool, Expr>, Error> {
        let ((ba, oa), (bb, ob)) = (Self::split(cx, a)?, Self::split(cx, b)?);
        if ba == bb {
            return Ok(Ok(oa == ob));
        }
        if let (Some(ea), Some(eb)) = (ba, bb) {
            let (iba, ibb) = (cx.id(ea)?, cx.id(eb)?);
            if oa == ob {
                if let Some(ans) = crate::engine::pass::shuffle::decide_eq_by_runs(cx, iba, ibb, 32)
                {
                    return Ok(Ok(ans));
                }
            } else {
                let delta = BitVec::bin_unchecked(BinOp::Sub, &oa, &ob);
                let low_eq = crate::engine::pass::shuffle::common_low_bits(cx, iba, ibb, 32);
                if crate::facts::known::trailing_zeros(&delta) < low_eq {
                    return Ok(Ok(false));
                }
            }
        }
        if let Some(ans) = Self::decide_linear_or_bits(cx, a, b)? {
            return Ok(Ok(ans));
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
            let off = match neg.to_u64() {
                Some(k) => self.offset(cx, a, k)?,
                None => {
                    let s = cx.constant(&start)?;
                    cx.bin(BinOp::Sub, a, s)?
                }
            };
            let inside = if self.addr.bits() < 128 && len == (1u128 << self.addr.bits()) {
                // A full address space has no representable exclusive upper bound.
                cx.one(Width::W1)?
            } else {
                let lim = cx.constant(&BitVec::from_u128(self.addr, len)?)?;
                cx.cmp(CmpOpExt::Ult, off, lim)?
            };
            let decided = match cx.as_const(inside)? {
                Some(v) => Some(!v.is_zero()),
                None => match cx.prove(Query::IsNonZero(inside))? {
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
        let mut found = None;
        for &(ra, rs) in &self.reads {
            match Self::same(cx, a, ra)? {
                Ok(true) => {
                    found = Some(rs);
                    break;
                }
                Ok(false) => {}
                Err(eq) => pending.push((eq, rs)),
            }
        }
        let s = match found {
            Some(s) => s,
            None => {
                let key = loop {
                    let key = SymbolKey::from(format!("{}.{}", self.name, self.next_read));
                    self.next_read += 1;
                    if cx.find_symbol(&key).is_none() {
                        break key;
                    }
                };
                let s = cx.symbol(key, self.cell)?;
                self.reads.push((a, s));
                s
            }
        };
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
    fn versions_reject_other_memories_and_diverged_clone_branches() {
        let mut cx = Context::new();
        let a = cx.zero(Width::W8).unwrap();
        let x = cx.constant_u64(Width::W8, 42).unwrap();
        let y = cx.constant_u64(Width::W8, 99).unwrap();
        let mut left = Memory::new("left", Width::W8, Width::W8, Endian::Little);
        let mut right = Memory::new("right", Width::W8, Width::W8, Endian::Little);
        let initial = left.initial();
        let shared = left.store(&mut cx, initial, a, x).unwrap();
        assert!(right.load(&mut cx, shared, a, 1).is_err());
        assert!(right.store(&mut cx, shared, a, y).is_err());
        assert!(right.stores.is_empty());
        let other = right.store(&mut cx, right.initial(), a, y).unwrap();
        assert_ne!(shared, other);
        assert!(right.load(&mut cx, shared, a, 1).is_err());
        assert!(left.load(&mut cx, other, a, 1).is_err());
        assert!(right.load(&mut cx, initial, a, 1).is_err());
        let mut fork = left.clone();
        assert_eq!(fork.load(&mut cx, shared, a, 1).unwrap(), x);
        let lv = left.store(&mut cx, shared, a, y).unwrap();
        let rv = fork.store(&mut cx, shared, a, x).unwrap();
        assert_ne!(lv, rv);
        assert!(fork.load(&mut cx, lv, a, 1).is_err());
        assert!(left.load(&mut cx, rv, a, 1).is_err());
        assert!(fork.store(&mut cx, lv, a, x).is_err());
        assert_eq!(left.load(&mut cx, lv, a, 1).unwrap(), y);
        assert_eq!(fork.load(&mut cx, rv, a, 1).unwrap(), x);
        assert_eq!(left.load(&mut cx, shared, a, 1).unwrap(), x);
    }

    #[test]
    fn oversized_loads_fail_before_creating_cells() {
        for (w, cells) in [
            (Width::W8, 65),
            (Width::W1, 513),
            (Width::W512, 2),
            (Width::W8, u16::MAX),
            (Width::W512, u16::MAX),
        ] {
            let mut cx = Context::new();
            let a = cx.symbol("address", Width::W64).unwrap();
            let mut m = Memory::new("m", Width::W64, w, Endian::Little);
            let before = cx.len();
            assert!(matches!(m.load(&mut cx, m.initial(), a, cells),
                Err(Error::Width(crate::WidthError::Invalid { bits }))
                    if bits == u32::from(w.bits()) * u32::from(cells)));
            assert_eq!(cx.len(), before);
            assert!(m.reads().is_empty());
            assert!(m.cache.is_empty());
        }
        let mut cx = Context::new();
        let a = cx.zero(Width::W8).unwrap();
        let mut m = Memory::new("m", Width::W8, Width::W8, Endian::Little).zeroed();
        let full = m.load(&mut cx, m.initial(), a, 64).unwrap();
        assert_eq!(cx.as_const(full).unwrap(), Some(BitVec::zero(Width::W512)));
    }

    #[test]
    fn reused_reads_preserve_aliases_across_versions() {
        let mut cx = Context::new();
        let mut m = Memory::new("m", Width::W8, Width::W8, Endian::Little);
        let p = cx.symbol("p", Width::W8).unwrap();
        let q = cx.symbol("q", Width::W8).unwrap();
        m.load(&mut cx, m.initial(), p, 1).unwrap();
        let before = m.load(&mut cx, m.initial(), q, 1).unwrap();
        let zero = cx.zero(Width::W8).unwrap();
        let version = m.store(&mut cx, m.initial(), zero, zero).unwrap();
        let after = m.load(&mut cx, version, q, 1).unwrap();
        assert_eq!(m.reads().len(), 2);
        for p in 0..4 {
            for q in 0..4 {
                let env: Vec<_> = [("p", p), ("q", q), ("m.0", 42), ("m.1", 99)]
                    .into_iter()
                    .map(|(key, v)| {
                        (
                            SymbolKey::from(key),
                            BitVec::wrapping_from_u64(Width::W8, v),
                        )
                    })
                    .collect();
                let values = cx.eval(&[before, after], &env[..]).unwrap();
                let old = if p == q { 42 } else { 99 };
                let new = if q == 0 { 0 } else { old };
                assert_eq!(values[0].to_u64(), Some(old), "p={p}, q={q}");
                assert_eq!(values[1].to_u64(), Some(new), "p={p}, q={q}");
            }
        }
    }

    #[test]
    fn unknown_reads_skip_occupied_symbol_names() {
        let mut cx = Context::new();
        // Both equal-width and incompatible-width caller symbols must remain independent.
        cx.symbol("m.0", Width::W8).unwrap();
        cx.symbol("m.1", Width::W32).unwrap();
        let mut m = Memory::new("m", Width::W8, Width::W8, Endian::Little);
        for (address, value) in [(0, 42), (1, 99)] {
            let address = cx.constant_u64(Width::W8, address).unwrap();
            let read = m.load(&mut cx, m.initial(), address, 1).unwrap();
            let bound = m
                .bind(&mut cx, &[], &|a| {
                    Some(BitVec::wrapping_from_u64(
                        Width::W8,
                        if a.is_zero() { 42 } else { 99 },
                    ))
                })
                .unwrap();
            assert_eq!(
                cx.eval(&[read], &bound[..]).unwrap()[0].to_u64(),
                Some(value)
            );
        }
        let keys: Vec<_> = m
            .reads()
            .iter()
            .map(|&(_, s)| {
                cx.symbol_key(cx.symbol_id(s).unwrap().unwrap())
                    .unwrap()
                    .clone()
            })
            .collect();
        assert_eq!(keys, [SymbolKey::from("m.2"), SymbolKey::from("m.3")]);
    }

    #[test]
    fn deep_addresses_normalize_without_recursion() {
        for width in [Width::W8, Width::W64, Width::W512] {
            let mut cx = Context::new();
            let p = cx.symbol("p", width).unwrap();
            let one = cx.one(width).unwrap();
            let mut address = p;
            for _ in 0..10_000 {
                address = cx.add(address, one).unwrap();
            }
            let offset = cx
                .constant(&BitVec::wrapping_from_u64(width, 10_000))
                .unwrap();
            let flat = cx.add(p, offset).unwrap();
            let value = cx.constant_u64(Width::W8, 42).unwrap();
            let mut m = Memory::new("m", width, Width::W8, Endian::Little);
            let version = m.store(&mut cx, m.initial(), address, value).unwrap();
            assert_eq!(m.load(&mut cx, version, flat, 1).unwrap(), value);
            assert_eq!(m.load(&mut cx, version, address, 1).unwrap(), value);
        }
    }

    #[test]
    fn changing_initial_contents_refreshes_cached_loads() {
        let mut cx = Context::new();
        let mut m = Memory::new("m", Width::W8, Width::W8, Endian::Little);
        let zero = cx.zero(Width::W8).unwrap();
        let one = cx.one(Width::W8).unwrap();
        let value = cx.constant_u64(Width::W8, 99).unwrap();
        let version = m.store(&mut cx, m.initial(), one, value).unwrap();
        let old = m.load(&mut cx, m.initial(), zero, 1).unwrap();
        m.load(&mut cx, version, zero, 1).unwrap();
        m = m.with_bytes(0, &[42]).unwrap();
        for at in [m.initial(), version] {
            let read = m.load(&mut cx, at, zero, 1).unwrap();
            assert_eq!(cx.as_const(read).unwrap().unwrap().to_u64(), Some(42));
        }
        assert!(matches!(cx.view(old).unwrap(), View::Sym(_)));
        assert_eq!(m.load(&mut cx, version, one, 1).unwrap(), value);
        let two = cx.constant_u64(Width::W8, 2).unwrap();
        m.load(&mut cx, version, two, 1).unwrap();
        m = m.zeroed();
        assert_eq!(m.load(&mut cx, version, two, 1).unwrap(), zero);
        assert_eq!(m.load(&mut cx, version, one, 1).unwrap(), value);
    }

    #[test]
    fn known_regions_preserve_wide_offsets_and_address_wrap() {
        for bits in [8, 64, 65, 128, 129, 256, 512] {
            let w = Width::new(bits).unwrap();
            let mut starts = vec![1];
            if bits > 64 {
                starts.push((1u128 << 64) + 3);
            }
            if bits <= 128 {
                starts.push(if bits == 128 {
                    u128::MAX - 1
                } else {
                    (1u128 << bits) - 2
                });
            }
            for start in starts {
                let mut cx = Context::new();
                let mut m = Memory::new("m", w, Width::W8, Endian::Little)
                    .zeroed()
                    .with_bytes(start, &[42, 99, 17])
                    .unwrap();
                let p = cx.symbol("p", w).unwrap();
                let symbolic = m.load(&mut cx, m.initial(), p, 1).unwrap();
                for (offset, want) in [(0, 42), (1, 99), (2, 17), (3, 0)] {
                    let address = BitVec::apply_bin(
                        BinOp::Add,
                        &BitVec::from_u128(w, start).unwrap(),
                        &BitVec::from_u64(w, offset).unwrap(),
                    )
                    .unwrap();
                    let a = cx.constant(&address).unwrap();
                    let direct = m.load(&mut cx, m.initial(), a, 1).unwrap();
                    assert_eq!(cx.as_const(direct).unwrap().unwrap().to_u64(), Some(want));
                    let env = [(SymbolKey::from("p"), address)];
                    assert_eq!(
                        cx.eval(&[symbolic], &env[..]).unwrap()[0].to_u64(),
                        Some(want)
                    );
                }
            }
        }
    }

    #[test]
    fn known_regions_can_cover_the_whole_address_space() {
        for bits in 1..=8 {
            let w = Width::new(bits).unwrap();
            let size = 1usize << bits;
            let bytes: Vec<u8> = (0..size)
                .map(|i| (i as u8).wrapping_mul(37).wrapping_add(11))
                .collect();
            let start = size / 2;
            let mut cx = Context::new();
            let mut m = Memory::new("m", w, Width::W8, Endian::Little)
                .with_bytes(start as u128, &bytes)
                .unwrap();
            let p = cx.symbol("p", w).unwrap();
            let symbolic = m.load(&mut cx, m.initial(), p, 1).unwrap();
            assert!(m.reads().is_empty());
            for address in 0..size {
                let want = u64::from(bytes[(address + size - start) % size]);
                let value = BitVec::from_u64(w, address as u64).unwrap();
                let a = cx.constant(&value).unwrap();
                let direct = m.load(&mut cx, m.initial(), a, 1).unwrap();
                assert_eq!(cx.as_const(direct).unwrap().unwrap().to_u64(), Some(want));
                let env = [(SymbolKey::from("p"), value)];
                assert_eq!(
                    cx.eval(&[symbolic], &env[..]).unwrap()[0].to_u64(),
                    Some(want)
                );
            }
        }
        assert!(
            Memory::new("m", Width::W1, Width::W8, Endian::Little)
                .with_bytes(0, &[1, 2, 3])
                .is_err()
        );
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

    #[test]
    fn linear_stride_and_bit_alias_disambiguation() {
        for &bits in &[32u16, 64] {
            let w = Width::new(bits).unwrap();
            let o = ParseOptions::width(w);
            let mut cx = Context::new();
            let mut m = Memory::new("m", w, Width::W8, Endian::Little);

            let val_a = cx.parse("a", &ParseOptions::width(Width::W32)).unwrap();
            let val_b = cx.parse("b", &ParseOptions::width(Width::W32)).unwrap();

            // 1. Reassociated multi-term sums: `(x + 4) + y` vs `(y + 8) + x` are disjoint,
            //    while `(y + 4) + x` aliases `(x + 4) + y` exactly.
            let p1 = cx.parse("(x + 4) + y", &o).unwrap();
            let p2 = cx.parse("(y + 8) + x", &o).unwrap();
            let p1_eq = cx.parse("(y + 4) + x", &o).unwrap();
            let v1 = m.store(&mut cx, m.initial(), p1, val_a).unwrap();
            let v2 = m.store(&mut cx, v1, p2, val_b).unwrap();
            assert_eq!(m.load(&mut cx, v2, p1_eq, 4).unwrap(), val_a);
            assert_eq!(m.load(&mut cx, v2, p2, 4).unwrap(), val_b);

            // 2. Subtracted stack offsets: `(sp - 16) + 8` aliases `sp - 8` and not `sp - 16`.
            let s16 = cx.parse("sp - 16", &o).unwrap();
            let s8_alt = cx.parse("(sp - 16) + 8", &o).unwrap();
            let s8 = cx.parse("sp - 8", &o).unwrap();
            let vs1 = m.store(&mut cx, m.initial(), s16, val_a).unwrap();
            let vs2 = m.store(&mut cx, vs1, s8_alt, val_b).unwrap();
            assert_eq!(m.load(&mut cx, vs2, s16, 4).unwrap(), val_a);
            assert_eq!(m.load(&mut cx, vs2, s8, 4).unwrap(), val_b);

            // 3. Disjoint bitwise OR offset: `sp + (i << 3)` vs `sp + ((i << 3) | 4)`.
            let b0 = cx.parse("sp + (i << 3)", &o).unwrap();
            let b4 = cx.parse("sp + ((i << 3) | 4)", &o).unwrap();
            let vb1 = m.store(&mut cx, m.initial(), b0, val_a).unwrap();
            let vb2 = m.store(&mut cx, vb1, b4, val_b).unwrap();
            assert_eq!(m.load(&mut cx, vb2, b0, 4).unwrap(), val_a);

            // 4. 2-adic stride GCD mismatch: `sp + i * 12` vs `sp + j * 12 + 2` for 2-byte cells
            //    (`12` has ctz 2, offsets `+0,+1` vs `+2,+3` differ by `1, 2, 3`, none divisible by 4).
            let h_a = cx.parse("ha", &ParseOptions::width(Width::W16)).unwrap();
            let h_b = cx.parse("hb", &ParseOptions::width(Width::W16)).unwrap();
            let st1 = cx.parse("sp + i * 12", &o).unwrap();
            let st2 = cx.parse("sp + j * 12 + 2", &o).unwrap();
            let vst1 = m.store(&mut cx, m.initial(), st1, h_a).unwrap();
            let vst2 = m.store(&mut cx, vst1, st2, h_b).unwrap();
            assert_eq!(m.load(&mut cx, vst2, st1, 2).unwrap(), h_a);

            // 5. Bounded zero-extended byte offset `sp + zext(idx8)` vs `sp + 300` (cannot alias).
            let idx8 = cx.symbol("idx8", Width::W8).unwrap();
            let z_idx = cx.zext(idx8, w).unwrap();
            let sp = cx.parse("sp", &o).unwrap();
            let z_addr = cx.bin(BinOp::Add, sp, z_idx).unwrap();
            let far_addr = cx.parse("sp + 300", &o).unwrap();
            let vz1 = m.store(&mut cx, m.initial(), z_addr, val_a).unwrap();
            let vz2 = m.store(&mut cx, vz1, far_addr, h_b).unwrap();
            // Even `z_addr + 3` is at most `sp + 258 < sp + 300`.
            assert_eq!(m.load(&mut cx, vz2, z_addr, 4).unwrap(), val_a);

            // 6. Bit-provenance complement: `p ^ 4` vs `p` (4-byte store never overlaps `p ^ 4`).
            let px0 = cx.parse("p", &o).unwrap();
            let px4 = cx.parse("p ^ 4", &o).unwrap();
            let vpx1 = m.store(&mut cx, m.initial(), px0, h_a).unwrap();
            let vpx2 = m.store(&mut cx, vpx1, px4, h_b).unwrap();
            // Single-byte load at `p` vs `p ^ 4`: bit 2 is opposite, so `p != p ^ 4` unconditionally.
            let b_at_p = m.load(&mut cx, vpx2, px0, 1).unwrap();
            assert!(
                !cx.display(b_at_p).to_string().contains("select"),
                "{}",
                cx.display(b_at_p)
            );

            // 7. Soundness guard: `sp + i * 4` vs `sp + j * 4 + 4` CAN alias when `j == i - 1`,
            //    so `select` MUST be preserved and evaluate to `val_b` at `(i = 5, j = 4)`.
            let ov1 = cx.parse("sp + i * 4", &o).unwrap();
            let ov2 = cx.parse("sp + j * 4 + 4", &o).unwrap();
            let vov1 = m.store(&mut cx, m.initial(), ov1, val_a).unwrap();
            let vov2 = m.store(&mut cx, vov1, ov2, val_b).unwrap();
            let loaded = m.load(&mut cx, vov2, ov1, 4).unwrap();
            assert!(cx.display(loaded).to_string().contains("select"));
            let env = [
                (SymbolKey::from("sp"), BitVec::wrapping_from_u64(w, 0x1000)),
                (SymbolKey::from("i"), BitVec::wrapping_from_u64(w, 5)),
                (SymbolKey::from("j"), BitVec::wrapping_from_u64(w, 4)),
                (
                    SymbolKey::from("a"),
                    BitVec::wrapping_from_u64(Width::W32, 0x11223344),
                ),
                (
                    SymbolKey::from("b"),
                    BitVec::wrapping_from_u64(Width::W32, 0x55667788),
                ),
            ];
            assert_eq!(
                cx.eval(&[loaded], &env[..]).unwrap()[0].to_u64(),
                Some(0x55667788)
            );
        }
    }

    #[test]
    fn merge_same_slot_has_no_spurious_reads_and_validates_inputs() {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let mut m = Memory::new("mem", Width::W64, Width::W8, Endian::Little);
        let slot = cx.parse("sp - 8", &o).unwrap();
        let x = cx.parse("x", &o).unwrap();
        let y = cx.parse("y", &o).unwrap();
        let cond = cx.symbol("c", Width::W1).unwrap();

        let vt = m.store(&mut cx, m.initial(), slot, x).unwrap();
        let ve = m.store(&mut cx, m.initial(), slot, y).unwrap();
        let vm = m.merge(&mut cx, cond, vt, ve).unwrap();
        assert!(m.reads().is_empty());

        let loaded = m.load(&mut cx, vm, slot, 8).unwrap();
        assert!(m.reads().is_empty());
        let simp = crate::engine::Engine::standard()
            .simplify(&mut cx, loaded)
            .unwrap()
            .expr;
        let want = cx.select(cond, x, y).unwrap();
        assert_eq!(simp, want);

        // Constant conditions and identical versions take fast paths.
        assert_eq!(m.merge(&mut cx, cond, vt, vt).unwrap(), vt);
        let one = cx.one(Width::W1).unwrap();
        let zero = cx.zero(Width::W1).unwrap();
        assert_eq!(m.merge(&mut cx, one, vt, ve).unwrap(), vt);
        assert_eq!(m.merge(&mut cx, zero, vt, ve).unwrap(), ve);

        // Non-1-bit condition and versions from other memories fail cleanly.
        assert!(m.merge(&mut cx, x, vt, ve).is_err());
        let other = Memory::new("other", Width::W64, Width::W8, Endian::Little);
        let vo = other.initial();
        assert!(m.merge(&mut cx, cond, vt, vo).is_err());
        assert!(m.merge(&mut cx, cond, vo, ve).is_err());
    }

    #[test]
    fn merge_exhaustive_symbolic_aliasing_and_nested_diamonds() {
        let mut cx = Context::new();
        let aw = Width::new(2).unwrap();
        let cw = Width::new(4).unwrap();
        let c0 = cx.constant_u64(aw, 0).unwrap();
        let c1 = cx.constant_u64(aw, 1).unwrap();
        let p = cx.symbol("p", aw).unwrap();
        let q = cx.symbol("q", aw).unwrap();
        let p_plus_1 = cx.add(p, c1).unwrap();
        let p_xor_1 = cx.bin(BinOp::Xor, p, c1).unwrap();
        let r = cx.symbol("r", aw).unwrap();
        let cond1 = cx.symbol("c1", Width::W1).unwrap();
        let cond2 = cx.symbol("c2", Width::W1).unwrap();

        let v_pre = cx.symbol("vp", cw).unwrap();
        let v_a = cx.symbol("va", cw).unwrap();
        let v_b = cx.symbol("vb", cw).unwrap();
        let v_c = cx.symbol("vc", cw).unwrap();
        let v_d = cx.symbol("vd", cw).unwrap();

        let addrs = [c0, p, q, p_plus_1, p_xor_1];
        // Test crossed-order stores, duplicate stores within a branch, one-sided branches,
        // shared non-initial LCA prefix, and nested merges.
        let branch_plans: &[(&[usize], &[usize])] = &[
            (&[1], &[]),
            (&[], &[2]),
            (&[1, 2], &[2, 1]),
            (&[1, 3, 1], &[2, 1]),
            (&[0, 4], &[4, 2]),
            (&[1, 2], &[3, 2]),
        ];

        for &(t_plan, e_plan) in branch_plans {
            let mut m = Memory::new("m", aw, cw, Endian::Little);
            let lca = m.store(&mut cx, m.initial(), c0, v_pre).unwrap();
            let mut vt = lca;
            for (k, &ai) in t_plan.iter().enumerate() {
                let val = if k % 2 == 0 { v_a } else { v_b };
                vt = m.store(&mut cx, vt, addrs[ai], val).unwrap();
            }
            let mut ve = lca;
            for (k, &ai) in e_plan.iter().enumerate() {
                let val = if k % 2 == 0 { v_c } else { v_d };
                ve = m.store(&mut cx, ve, addrs[ai], val).unwrap();
            }
            let vm1 = m.merge(&mut cx, cond1, vt, ve).unwrap();
            // Nested merge on top of vm1 vs an extra store on lca.
            let v_alt = m.store(&mut cx, lca, q, v_d).unwrap();
            let vm2 = m.merge(&mut cx, cond2, vm1, v_alt).unwrap();

            let load_t = m.load(&mut cx, vt, r, 1).unwrap();
            let load_e = m.load(&mut cx, ve, r, 1).unwrap();
            let load_alt = m.load(&mut cx, v_alt, r, 1).unwrap();
            let load_m1 = m.load(&mut cx, vm1, r, 1).unwrap();
            let load_m2 = m.load(&mut cx, vm2, r, 1).unwrap();

            let image = |a: &BitVec| {
                Some(BitVec::wrapping_from_u64(
                    cw,
                    (a.to_u64().unwrap() * 3 + 1) & 0xf,
                ))
            };

            for pv in 0..4u64 {
                for qv in 0..4u64 {
                    for rv in 0..4u64 {
                        for b1 in 0..2u64 {
                            for b2 in 0..2u64 {
                                let base_env = [
                                    (SymbolKey::from("p"), BitVec::wrapping_from_u64(aw, pv)),
                                    (SymbolKey::from("q"), BitVec::wrapping_from_u64(aw, qv)),
                                    (SymbolKey::from("r"), BitVec::wrapping_from_u64(aw, rv)),
                                    (
                                        SymbolKey::from("c1"),
                                        BitVec::wrapping_from_u64(Width::W1, b1),
                                    ),
                                    (
                                        SymbolKey::from("c2"),
                                        BitVec::wrapping_from_u64(Width::W1, b2),
                                    ),
                                    (SymbolKey::from("vp"), BitVec::wrapping_from_u64(cw, 2)),
                                    (SymbolKey::from("va"), BitVec::wrapping_from_u64(cw, 5)),
                                    (SymbolKey::from("vb"), BitVec::wrapping_from_u64(cw, 9)),
                                    (SymbolKey::from("vc"), BitVec::wrapping_from_u64(cw, 12)),
                                    (SymbolKey::from("vd"), BitVec::wrapping_from_u64(cw, 14)),
                                ];
                                let env = m.bind(&mut cx, &base_env, &image).unwrap();
                                let out = cx
                                    .eval(&[load_t, load_e, load_alt, load_m1, load_m2], &env[..])
                                    .unwrap();
                                let want_m1 = if b1 != 0 { out[0] } else { out[1] };
                                let want_m2 = if b2 != 0 { want_m1 } else { out[2] };
                                assert_eq!(
                                    out[3], want_m1,
                                    "plan={t_plan:?}/{e_plan:?} p={pv} q={qv} r={rv} c1={b1}"
                                );
                                assert_eq!(
                                    out[4], want_m2,
                                    "nested plan={t_plan:?}/{e_plan:?} p={pv} q={qv} r={rv} c1={b1} c2={b2}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn memset_and_memcpy_handle_overlap_and_bounds() {
        let (mut cx, o) = setup();
        let mut m = Memory::new("m", Width::W32, Width::W8, Endian::Little);
        let p = cx.parse("p", &o).unwrap();
        let p1 = cx.parse("p + 1", &o).unwrap();
        let q = cx.parse("p + 16", &o).unwrap();
        let x = cx
            .constant(&BitVec::wrapping_from_u64(Width::W32, 0x04030201))
            .unwrap();
        let fill = cx.constant_u64(Width::W8, 0xaa).unwrap();

        // Zero-length ops are identity.
        let v0 = m.initial();
        assert_eq!(m.memset(&mut cx, v0, p, fill, 0).unwrap(), v0);
        assert_eq!(m.memcpy(&mut cx, v0, q, p, 0).unwrap(), v0);
        assert_eq!(m.memcpy(&mut cx, v0, p, p, 8).unwrap(), v0);
        assert!(m.reads().is_empty());

        // Non-overlapping memcpy coalesces multi-byte symbols cleanly.
        let sym32 = cx.symbol("val", Width::W32).unwrap();
        let vs = m.store(&mut cx, v0, p, sym32).unwrap();
        let vc = m.memcpy(&mut cx, vs, q, p, 4).unwrap();
        assert_eq!(m.load(&mut cx, vc, q, 4).unwrap(), sym32);

        // Forward overlap (`dst = p + 1`, `src = p`, 3 bytes) preserves `memmove` snapshot:
        // `[01, 02, 03, 04]` -> `[01, 01, 02, 03]`.
        let v1 = m.store(&mut cx, v0, p, x).unwrap();
        let v_fwd = m.memcpy(&mut cx, v1, p1, p, 3).unwrap();
        let got_fwd = m.load(&mut cx, v_fwd, p, 4).unwrap();
        assert_eq!(
            cx.as_const(got_fwd).unwrap().unwrap().to_u64(),
            Some(0x03020101)
        );

        // Backward overlap (`dst = p`, `src = p + 1`, 3 bytes):
        // `[01, 02, 03, 04]` -> `[02, 03, 04, 04]`.
        let v_bwd = m.memcpy(&mut cx, v1, p, p1, 3).unwrap();
        let got_bwd = m.load(&mut cx, v_bwd, p, 4).unwrap();
        assert_eq!(
            cx.as_const(got_bwd).unwrap().unwrap().to_u64(),
            Some(0x04040302)
        );

        // memset fills consecutive bytes.
        let v_set = m.memset(&mut cx, v1, p1, fill, 2).unwrap();
        let got_set = m.load(&mut cx, v_set, p, 4).unwrap();
        assert_eq!(
            cx.as_const(got_set).unwrap().unwrap().to_u64(),
            Some(0x04aaaa01)
        );

        // Bounds and width checks.
        assert!(m.memset(&mut cx, v0, p, x, 2).is_err());
        assert!(m.memset(&mut cx, v0, p, fill, 4097).is_err());
        assert!(m.memcpy(&mut cx, v0, q, p, 4097).is_err());
    }
}

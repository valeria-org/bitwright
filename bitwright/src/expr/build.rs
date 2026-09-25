//! Building expressions, with construction-time canonicalization.
//!
//! Every stored node is canonical; there is no raw mode. The rules below are O(1), sound
//! under bitwright's total semantics (they are tested exhaustively at small widths against the
//! independent reference evaluator), and never increase the node count of the result.
//!
//! 1. Validation of arity and widths (errors, never panics).
//! 2. Folding when every operand is a constant.
//! 3. Canonical operand order for commutative operators (constants on the right); `ugt/uge/
//!    sgt/sge` become swapped `ult/ule/slt/sle`.
//! 4. Normalized spellings: `x - c -> x + (-c)`, `0 - x -> -x`, rotate counts reduced modulo
//!    the width, `rotr` by a constant becomes `rotl`, `not(cmp)` becomes the inverse compare,
//!    `x ^ ones -> ~x`, `select(~c, a, b) -> select(c, b, a)`.
//! 5. Identities: neutral and absorbing constants, `x ^ x`, `x - x`, idempotence of `&`/`|`,
//!    involutions (`~~x`, `--x`, `bswap∘bswap`, `bitrev∘bitrev`), reflexive and trivially
//!    decided compares, `select` with a constant condition or equal arms.
//! 6. Cast collapse: nested extensions, extract of an extract, extract that stays inside the
//!    operand of an extension or a concatenation, concatenation of adjacent extracts, and
//!    `concat(0, x) -> zext(x)`.

use super::{Context, Expr, Node, OpCode};
use crate::error::{Error, WidthError};
use crate::ops::{BinOp, CmpOp, CmpOpExt, UnOp};
use crate::{BitVec, Width};

impl Context {
    // ----- predicates on stored nodes -------------------------------------------------------

    fn is_const_where(&self, i: u32, f: impl Fn(&BitVec) -> bool) -> bool {
        self.const_val(i).is_some_and(|v| f(&v))
    }

    /// The value of an inline (at most 64-bit) constant node without building a `BitVec`.
    fn small_const(&self, i: u32) -> Option<u64> {
        let n = self.node(i);
        (n.op == OpCode::Const && n.aux & super::AUX_POOLED == 0)
            .then(|| u64::from(n.a) | (u64::from(n.b) << 32))
    }

    fn is_zero(&self, i: u32) -> bool {
        match self.small_const(i) {
            Some(v) => v == 0,
            None => self.is_const_where(i, BitVec::is_zero),
        }
    }

    fn is_ones(&self, i: u32) -> bool {
        self.is_const_where(i, BitVec::is_ones)
    }

    fn is_one(&self, i: u32) -> bool {
        match self.small_const(i) {
            Some(v) => v == 1,
            None => self.is_const_where(i, |v| v.to_u64() == Some(1)),
        }
    }

    fn c_zero(&mut self, w: u16) -> Result<u32, Error> {
        self.mk_const(&BitVec::zero(Width::new(w)?))
    }

    fn c_bool(&mut self, b: bool) -> Result<u32, Error> {
        self.mk_const(&BitVec::from_bool(b))
    }

    fn c_uint(&mut self, w: u16, v: u64) -> Result<u32, Error> {
        self.mk_const(&BitVec::wrapping_from_u64(Width::new(w)?, v))
    }

    // ----- canonicalizing constructors on indices -------------------------------------------

    pub(crate) fn c_un(&mut self, op: UnOp, a: u32) -> Result<u32, Error> {
        let n = self.node(a);
        let w = n.width;
        if op == UnOp::Bswap && !w.is_multiple_of(8) {
            return Err(WidthError::NotByteMultiple { bits: w }.into());
        }
        if let Some(v) = self.const_val(a) {
            return self.mk_const(&BitVec::un_unchecked(op, &v));
        }
        match op {
            UnOp::Not => {
                if n.op == OpCode::Not {
                    return Ok(n.a);
                }
                if let Some(c) = n.op.as_cmp() {
                    let (q, swap) = c.negated().canonical();
                    let (x, y) = if swap { (n.b, n.a) } else { (n.a, n.b) };
                    return self.c_cmp(q, x, y);
                }
            }
            UnOp::Neg if n.op == OpCode::Neg => return Ok(n.a),
            UnOp::Bswap if n.op == OpCode::Bswap || w == 8 => {
                return Ok(if w == 8 { a } else { n.a });
            }
            UnOp::BitRev if n.op == OpCode::BitRev || w == 1 => {
                return Ok(if w == 1 { a } else { n.a });
            }
            UnOp::Popcnt if w == 1 => return Ok(a),
            _ => {}
        }
        self.mk(Node::new(OpCode::from_un(op), w, a, 0, 0))
    }

    pub(crate) fn c_bin(&mut self, op: BinOp, a: u32, b: u32) -> Result<u32, Error> {
        let (wa, wb) = (self.wid(a), self.wid(b));
        if wa != wb {
            return Err(WidthError::Mismatch {
                left: wa,
                right: wb,
            }
            .into());
        }
        let w = wa;
        if let (Some(x), Some(y)) = (self.const_val(a), self.const_val(b)) {
            return self.mk_const(&BitVec::bin_unchecked(op, &x, &y));
        }
        // Commutative operators: constants right, otherwise the canonical order.
        let (a, b) = if op.is_commutative() && self.order(a, b).is_gt() {
            (b, a)
        } else {
            (a, b)
        };
        match op {
            BinOp::Sub => {
                if a == b {
                    return self.c_zero(w);
                }
                if let Some(c) = self.const_val(b) {
                    if c.is_zero() {
                        return Ok(a);
                    }
                    let neg = self.mk_const(&BitVec::un_unchecked(UnOp::Neg, &c))?;
                    return self.c_bin(BinOp::Add, a, neg);
                }
                if self.is_zero(a) {
                    return self.c_un(UnOp::Neg, b);
                }
            }
            BinOp::Add if self.is_zero(b) => return Ok(a),
            BinOp::Mul => {
                if self.is_zero(b) {
                    return Ok(b);
                }
                if self.is_one(b) {
                    return Ok(a);
                }
            }
            BinOp::And => {
                if self.is_zero(b) || a == b {
                    return Ok(b);
                }
                if self.is_ones(b) {
                    return Ok(a);
                }
            }
            BinOp::Or => {
                if self.is_ones(b) || a == b {
                    return Ok(b);
                }
                if self.is_zero(b) {
                    return Ok(a);
                }
            }
            BinOp::Xor => {
                if a == b {
                    return self.c_zero(w);
                }
                if self.is_zero(b) {
                    return Ok(a);
                }
                if self.is_ones(b) {
                    return self.c_un(UnOp::Not, a);
                }
            }
            BinOp::UMulHi => {
                if self.is_zero(b) {
                    return Ok(b);
                }
                if self.is_one(b) {
                    return self.c_zero(w);
                }
            }
            BinOp::SMulHi if self.is_zero(b) => return Ok(b),
            BinOp::UDiv => {
                if self.is_zero(b) {
                    return self.mk_const(&BitVec::ones(Width::new(w)?));
                }
                if self.is_one(b) {
                    return Ok(a);
                }
            }
            BinOp::URem => {
                if self.is_zero(b) {
                    return Ok(a);
                }
                if self.is_one(b) {
                    return self.c_zero(w);
                }
            }
            BinOp::SDiv => {
                if self.is_one(b) {
                    return Ok(a);
                }
                if self.is_ones(b) {
                    return self.c_un(UnOp::Neg, a);
                }
            }
            BinOp::SRem => {
                if self.is_zero(b) {
                    return Ok(a);
                }
                if self.is_one(b) || self.is_ones(b) {
                    return self.c_zero(w);
                }
            }
            BinOp::Shl | BinOp::LShr => {
                if self.is_zero(b) || self.is_zero(a) {
                    return Ok(a);
                }
                if self.is_const_where(b, |c| count_at_least(c, w)) {
                    return self.c_zero(w);
                }
            }
            BinOp::AShr => {
                if self.is_zero(b) || self.is_zero(a) || self.is_ones(a) {
                    return Ok(a);
                }
                if self.is_const_where(b, |c| count_at_least(c, w)) {
                    let top = self.c_uint(w, u64::from(w) - 1)?;
                    return self.c_bin(BinOp::AShr, a, top);
                }
            }
            BinOp::RotL | BinOp::RotR => {
                if self.is_zero(a) || self.is_ones(a) {
                    return Ok(a);
                }
                if let Some(c) = self.const_val(b) {
                    let r = count_mod(&c, w);
                    if r == 0 {
                        return Ok(a);
                    }
                    let left = if op == BinOp::RotL {
                        r
                    } else {
                        u64::from(w) - r
                    };
                    if op == BinOp::RotR || c.to_u64() != Some(left) {
                        let k = self.c_uint(w, left)?;
                        return self.c_bin(BinOp::RotL, a, k);
                    }
                }
            }
            BinOp::Pdep | BinOp::Pext => {
                if self.is_zero(a) || self.is_zero(b) {
                    return self.c_zero(w);
                }
                if self.is_ones(b) {
                    return Ok(a);
                }
            }
            _ => {}
        }
        self.mk(Node::new(OpCode::from_bin(op), w, a, b, 0))
    }

    pub(crate) fn c_cmp(&mut self, op: CmpOp, a: u32, b: u32) -> Result<u32, Error> {
        let (wa, wb) = (self.wid(a), self.wid(b));
        if wa != wb {
            return Err(WidthError::Mismatch {
                left: wa,
                right: wb,
            }
            .into());
        }
        if let (Some(x), Some(y)) = (self.const_val(a), self.const_val(b)) {
            return self.c_bool(BitVec::cmp_unchecked(op, &x, &y));
        }
        let (a, b) = if op.is_commutative() && self.order(a, b).is_gt() {
            (b, a)
        } else {
            (a, b)
        };
        if a == b {
            return self.c_bool(matches!(op, CmpOp::Eq | CmpOp::Ule | CmpOp::Sle));
        }
        let smin = |v: &BitVec| *v == BitVec::smin(v.width());
        let smax = |v: &BitVec| *v == BitVec::smax(v.width());
        let decided = match op {
            CmpOp::Ult if self.is_zero(b) || self.is_ones(a) => Some(false),
            CmpOp::Ule if self.is_zero(a) || self.is_ones(b) => Some(true),
            CmpOp::Slt if self.is_const_where(b, smin) || self.is_const_where(a, smax) => {
                Some(false)
            }
            CmpOp::Sle if self.is_const_where(a, smin) || self.is_const_where(b, smax) => {
                Some(true)
            }
            _ => None,
        };
        if let Some(d) = decided {
            return self.c_bool(d);
        }
        if wa == 1 && matches!(op, CmpOp::Eq | CmpOp::Ne) {
            // 1-bit equality with a constant is the operand or its complement.
            if let Some(c) = self.const_val(b) {
                let keep = (op == CmpOp::Eq) != c.is_zero();
                return if keep { Ok(a) } else { self.c_un(UnOp::Not, a) };
            }
        }
        self.mk(Node::new(OpCode::from_cmp(op), 1, a, b, 0))
    }

    pub(crate) fn c_zext(&mut self, a: u32, to: u16) -> Result<u32, Error> {
        let w = self.wid(a);
        let tw = Width::new(to)?;
        if to < w {
            return Err(WidthError::NotWider { from: w, to }.into());
        }
        if to == w {
            return Ok(a);
        }
        if let Some(v) = self.const_val(a) {
            return self.mk_const(&v.zext(tw)?);
        }
        let n = self.node(a);
        if n.op == OpCode::Zext {
            return self.c_zext(n.a, to);
        }
        self.mk(Node::new(OpCode::Zext, to, a, 0, 0))
    }

    pub(crate) fn c_sext(&mut self, a: u32, to: u16) -> Result<u32, Error> {
        let w = self.wid(a);
        let tw = Width::new(to)?;
        if to < w {
            return Err(WidthError::NotWider { from: w, to }.into());
        }
        if to == w {
            return Ok(a);
        }
        if let Some(v) = self.const_val(a) {
            return self.mk_const(&v.sext(tw)?);
        }
        let n = self.node(a);
        match n.op {
            OpCode::Sext => return self.c_sext(n.a, to),
            // The top bit of a strict zero extension is 0.
            OpCode::Zext => return self.c_zext(n.a, to),
            _ => {}
        }
        self.mk(Node::new(OpCode::Sext, to, a, 0, 0))
    }

    pub(crate) fn c_extract(&mut self, a: u32, lo: u16, len: u16) -> Result<u32, Error> {
        let w = self.wid(a);
        let lw = Width::new(len)?;
        if u32::from(lo) + u32::from(len) > u32::from(w) {
            return Err(WidthError::ExtractRange { width: w, lo, len }.into());
        }
        if lo == 0 && len == w {
            return Ok(a);
        }
        if let Some(v) = self.const_val(a) {
            return self.mk_const(&v.extract(lo, lw)?);
        }
        let n = self.node(a);
        let inner_w = |cx: &Self| cx.wid(n.a);
        match n.op {
            OpCode::Extract => return self.c_extract(n.a, n.b as u16 + lo, len),
            OpCode::Zext => {
                let iw = inner_w(self);
                if lo + len <= iw {
                    return self.c_extract(n.a, lo, len);
                }
                if lo >= iw {
                    return self.c_zero(len);
                }
            }
            OpCode::Sext => {
                let iw = inner_w(self);
                if lo + len <= iw {
                    return self.c_extract(n.a, lo, len);
                }
                if len == 1 && lo >= iw - 1 {
                    return self.c_extract(n.a, iw - 1, 1);
                }
            }
            OpCode::Concat => {
                let low_w = self.wid(n.b);
                if lo + len <= low_w {
                    return self.c_extract(n.b, lo, len);
                }
                if lo >= low_w {
                    return self.c_extract(n.a, lo - low_w, len);
                }
            }
            _ => {}
        }
        self.mk(Node::new(OpCode::Extract, len, a, u32::from(lo), 0))
    }

    pub(crate) fn c_concat(&mut self, hi: u32, lo: u32) -> Result<u32, Error> {
        let (hw, lw) = (self.wid(hi), self.wid(lo));
        let total = u32::from(hw) + u32::from(lw);
        if total > u32::from(Width::MAX_BITS) {
            return Err(WidthError::ConcatTooWide { hi: hw, lo: lw }.into());
        }
        let total = total as u16;
        if let (Some(h), Some(l)) = (self.const_val(hi), self.const_val(lo)) {
            return self.mk_const(&BitVec::concat(&h, &l)?);
        }
        if self.is_zero(hi) {
            return self.c_zext(lo, total);
        }
        let (nh, nl) = (self.node(hi), self.node(lo));
        if nh.op == OpCode::Concat
            && let (Some(left), Some(right)) = (self.const_val(nh.b), self.const_val(lo))
        {
            let tail = self.mk_const(&BitVec::concat(&left, &right)?)?;
            return self.c_concat(nh.a, tail);
        }
        if nh.op == OpCode::Extract
            && nl.op == OpCode::Extract
            && nh.a == nl.a
            && nh.b == nl.b + u32::from(lw)
        {
            return self.c_extract(nl.a, nl.b as u16, total);
        }
        self.mk(Node::new(OpCode::Concat, total, hi, lo, 0))
    }

    pub(crate) fn c_select(&mut self, c: u32, t: u32, f: u32) -> Result<u32, Error> {
        let wc = self.wid(c);
        if wc != 1 {
            return Err(WidthError::ConditionWidth { bits: wc }.into());
        }
        let (wt, wf) = (self.wid(t), self.wid(f));
        if wt != wf {
            return Err(WidthError::Mismatch {
                left: wt,
                right: wf,
            }
            .into());
        }
        if let Some(v) = self.const_val(c) {
            return Ok(if v.is_zero() { f } else { t });
        }
        if t == f {
            return Ok(t);
        }
        let nc = self.node(c);
        if nc.op == OpCode::Not {
            return self.c_select(nc.a, f, t);
        }
        if wt == 1 {
            if self.is_one(t) && self.is_zero(f) {
                return Ok(c);
            }
            if self.is_zero(t) && self.is_one(f) {
                return self.c_un(UnOp::Not, c);
            }
        }
        self.mk(Node::new(OpCode::Select, wt, c, t, f))
    }

    /// The registry operation `op` and its signature at the widths of `args`.
    fn ext_sig(
        &self,
        op: crate::ext::ExtId,
        args: &[u32],
    ) -> Result<(std::sync::Arc<crate::ext::Registry>, crate::ext::ExtSig), Error> {
        let reg = self
            .registry
            .clone()
            .ok_or_else(|| Error::Unsupported("the context has no extension registry".into()))?;
        let o = reg
            .op(op)
            .ok_or_else(|| Error::Unsupported("no such extension operation".into()))?;
        if args.is_empty() || args.len() > crate::ext::MAX_ARGS {
            return Err(Error::Unsupported(format!(
                "`{}` called with {} arguments (1 to {})",
                o.name(),
                args.len(),
                crate::ext::MAX_ARGS
            )));
        }
        let widths: Vec<Width> = args.iter().map(|&a| self.width_of(a)).collect();
        let sig = o.signature(&widths).map_err(|why| {
            Error::Unsupported(format!(
                "`{}` at widths {:?}: {why}",
                o.name(),
                widths.iter().map(|w| w.bits()).collect::<Vec<_>>()
            ))
        })?;
        if sig.is_empty() || sig.len() > crate::ext::MAX_OUTPUTS {
            return Err(Error::Contract(format!(
                "`{}` declares {} outputs",
                o.name(),
                sig.len()
            )));
        }
        Ok((reg, sig))
    }

    /// Output `k` of the extension call `op(args)`: folded to a constant when every argument
    /// is one (and the operation keeps its contract on them).
    pub(crate) fn c_ext(
        &mut self,
        op: crate::ext::ExtId,
        k: usize,
        args: &[u32],
    ) -> Result<u32, Error> {
        let (reg, sig) = self.ext_sig(op, args)?;
        let w = sig
            .width(k)
            .ok_or_else(|| Error::Unsupported(format!("no output {k}")))?;
        let o = reg
            .op(op)
            .ok_or_else(|| Error::Contract("no such operation".into()))?;
        let arity = args.len();
        let mut kids = [0u32; 3];
        kids[..arity].copy_from_slice(args);
        // Commutative operations take their first two arguments in canonical order (only
        // arguments of one width can trade places).
        if o.traits().commutative
            && arity >= 2
            && self.wid(kids[0]) == self.wid(kids[1])
            && self.order(kids[0], kids[1]).is_gt()
        {
            kids.swap(0, 1);
        }
        let consts: Option<Vec<BitVec>> =
            kids[..arity].iter().map(|&a| self.const_val(a)).collect();
        if let Some(vals) = consts
            && let Ok(out) = crate::ext::run_eval(o, &vals)
            && out.get(k).is_some_and(|v| v.width() == w)
        {
            return self.mk_const(&out[k]);
        }
        // A round trip: the call undoes an output of another call over it.
        for rt in reg.round_trips(op.raw()) {
            if usize::from(rt.g_output) != k || rt.args.len() != arity {
                continue;
            }
            let Some(pos) = rt
                .args
                .iter()
                .position(|a| *a == crate::ext::InverseArg::Output)
            else {
                continue;
            };
            let inner = self.node(kids[pos]);
            let Some((f_arity, f_out)) = inner.op.as_ext() else {
                continue;
            };
            if inner.aux != rt.f || f_out != usize::from(rt.f_output) {
                continue;
            }
            let fargs = [inner.a, inner.b, inner.c];
            let fits = rt.args.iter().zip(&kids[..arity]).all(|(a, &x)| match *a {
                crate::ext::InverseArg::Output => x == kids[pos],
                crate::ext::InverseArg::Arg(i) => {
                    usize::from(i) < f_arity && fargs[usize::from(i)] == x
                }
            });
            let back = fargs[usize::from(rt.f_arg)];
            if fits && usize::from(rt.f_arg) < f_arity && self.wid(back) == w.bits() {
                return Ok(back);
            }
        }
        let code = OpCode::ext(arity, k)
            .ok_or_else(|| Error::Unsupported(format!("output {k} of {arity} arguments")))?;
        let mut n = Node::new(code, w.bits(), kids[0], kids[1], kids[2]);
        n.aux = op.raw();
        self.mk(n)
    }

    /// [`Context::c_ext`] for the operation at registry position `index` (from a node).
    fn c_ext_at(&mut self, index: u8, k: usize, args: &[u32]) -> Result<u32, Error> {
        let op = self
            .registry
            .as_deref()
            .and_then(|r| r.id_at(index))
            .ok_or_else(|| Error::Contract("an extension node without its operation".into()))?;
        self.c_ext(op, k, args)
    }

    /// Rebuilds node `i` with new children, through the canonicalizing constructors.
    pub(crate) fn rebuild(&mut self, i: u32, kids: [u32; 3]) -> Result<u32, Error> {
        let n = self.node(i);
        let [a, b, c] = kids;
        match n.op {
            OpCode::Const | OpCode::Sym => Ok(i),
            OpCode::Zext => self.c_zext(a, n.width),
            OpCode::Sext => self.c_sext(a, n.width),
            OpCode::Extract => self.c_extract(a, n.b as u16, n.width),
            OpCode::Concat => self.c_concat(a, b),
            OpCode::Select => self.c_select(a, b, c),
            op if op.as_ext().is_some() => {
                let (arity, k) = op.as_ext().unwrap_or((1, 0));
                self.c_ext_at(n.aux, k, &[a, b, c][..arity])
            }
            op => {
                if let Some(u) = op.as_un() {
                    self.c_un(u, a)
                } else if let Some(bo) = op.as_bin() {
                    self.c_bin(bo, a, b)
                } else if let Some(co) = op.as_cmp() {
                    self.c_cmp(co, a, b)
                } else if let Some(d) = self.fp_desc(i) {
                    self.c_fp(d, &[a, b, c][..d.kind().arity()])
                } else {
                    unreachable!("every opcode is covered")
                }
            }
        }
    }

    // ----- public builder -------------------------------------------------------------------

    /// Every output of the extension call `op(args)` (1 to 3 arguments), in order. Needs a
    /// context built with a registry holding `op`
    /// ([`with_registry`](Context::with_registry)); outputs of calls on constants are
    /// constants.
    pub fn ext(&mut self, op: crate::ext::ExtId, args: &[Expr]) -> Result<Vec<Expr>, Error> {
        let ids = self.ids(args)?;
        let (_, sig) = self.ext_sig(op, &ids)?;
        (0..sig.len())
            .map(|k| self.c_ext(op, k, &ids).map(|i| self.handle(i)))
            .collect()
    }

    /// Output `k` of the extension call `op(args)`.
    pub fn ext_output(
        &mut self,
        op: crate::ext::ExtId,
        k: usize,
        args: &[Expr],
    ) -> Result<Expr, Error> {
        let ids = self.ids(args)?;
        let i = self.c_ext(op, k, &ids)?;
        Ok(self.handle(i))
    }

    /// A constant.
    pub fn constant(&mut self, v: &BitVec) -> Result<Expr, Error> {
        let i = self.mk_const(v)?;
        Ok(self.handle(i))
    }

    /// The constant `v`, which must fit in `width` bits.
    pub fn constant_u64(&mut self, width: Width, v: u64) -> Result<Expr, Error> {
        self.constant(&BitVec::from_u64(width, v)?)
    }

    /// The constant `v`, which must fit in `width` bits.
    pub fn constant_u128(&mut self, width: Width, v: u128) -> Result<Expr, Error> {
        self.constant(&BitVec::from_u128(width, v)?)
    }

    /// The constant `v`, which must be representable as a signed `width`-bit value.
    pub fn constant_i128(&mut self, width: Width, v: i128) -> Result<Expr, Error> {
        self.constant(&BitVec::from_i128(width, v)?)
    }

    /// Zero.
    pub fn zero(&mut self, width: Width) -> Result<Expr, Error> {
        self.constant(&BitVec::zero(width))
    }

    /// One.
    pub fn one(&mut self, width: Width) -> Result<Expr, Error> {
        self.constant(&BitVec::one(width))
    }

    /// All ones.
    pub fn ones(&mut self, width: Width) -> Result<Expr, Error> {
        self.constant(&BitVec::ones(width))
    }

    /// A 1-bit constant.
    pub fn bool(&mut self, b: bool) -> Result<Expr, Error> {
        self.constant(&BitVec::from_bool(b))
    }

    /// A unary operator.
    pub fn un(&mut self, op: UnOp, a: Expr) -> Result<Expr, Error> {
        let a = self.id(a)?;
        let i = self.c_un(op, a)?;
        Ok(self.handle(i))
    }

    /// A binary operator; the operands must have the same width.
    pub fn bin(&mut self, op: BinOp, a: Expr, b: Expr) -> Result<Expr, Error> {
        let (a, b) = (self.id(a)?, self.id(b)?);
        let i = self.c_bin(op, a, b)?;
        Ok(self.handle(i))
    }

    /// A comparison (1-bit result); the operands must have the same width.
    pub fn cmp(&mut self, op: impl Into<CmpOpExt>, a: Expr, b: Expr) -> Result<Expr, Error> {
        let (a, b) = (self.id(a)?, self.id(b)?);
        let (op, swap) = op.into().canonical();
        let (a, b) = if swap { (b, a) } else { (a, b) };
        let i = self.c_cmp(op, a, b)?;
        Ok(self.handle(i))
    }

    /// Zero extension to `to` (at least the operand's width; equal width is the identity).
    pub fn zext(&mut self, a: Expr, to: Width) -> Result<Expr, Error> {
        let a = self.id(a)?;
        let i = self.c_zext(a, to.bits())?;
        Ok(self.handle(i))
    }

    /// Sign extension to `to` (at least the operand's width; equal width is the identity).
    pub fn sext(&mut self, a: Expr, to: Width) -> Result<Expr, Error> {
        let a = self.id(a)?;
        let i = self.c_sext(a, to.bits())?;
        Ok(self.handle(i))
    }

    /// The low `to` bits.
    pub fn trunc(&mut self, a: Expr, to: Width) -> Result<Expr, Error> {
        self.extract(a, 0, to)
    }

    /// Bits `[lo, lo + len)`.
    pub fn extract(&mut self, a: Expr, lo: u16, len: Width) -> Result<Expr, Error> {
        let a = self.id(a)?;
        let i = self.c_extract(a, lo, len.bits())?;
        Ok(self.handle(i))
    }

    /// `hi` in the high bits, `lo` in the low bits.
    pub fn concat(&mut self, hi: Expr, lo: Expr) -> Result<Expr, Error> {
        let (h, l) = (self.id(hi)?, self.id(lo)?);
        let i = self.c_concat(h, l)?;
        Ok(self.handle(i))
    }

    /// `cond ? then : els`; the condition must be 1 bit wide.
    pub fn select(&mut self, cond: Expr, then: Expr, els: Expr) -> Result<Expr, Error> {
        let (c, t, f) = (self.id(cond)?, self.id(then)?, self.id(els)?);
        let i = self.c_select(c, t, f)?;
        Ok(self.handle(i))
    }
}

macro_rules! unary_shorthands {
    ($($(#[$doc:meta])* $name:ident => $op:ident;)*) => {
        impl Context {
            $($(#[$doc])* pub fn $name(&mut self, a: Expr) -> Result<Expr, Error> {
                self.un(UnOp::$op, a)
            })*
        }
    };
}

macro_rules! binary_shorthands {
    ($($(#[$doc:meta])* $name:ident => $op:ident;)*) => {
        impl Context {
            $($(#[$doc])* pub fn $name(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
                self.bin(BinOp::$op, a, b)
            })*
        }
    };
}

macro_rules! compare_shorthands {
    ($($(#[$doc:meta])* $name:ident => $op:ident;)*) => {
        impl Context {
            $($(#[$doc])* pub fn $name(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
                self.cmp(CmpOpExt::$op, a, b)
            })*
        }
    };
}

unary_shorthands! {
    /// Bitwise complement.
    not => Not;
    /// Two's-complement negation.
    neg => Neg;
    /// Number of set bits.
    popcnt => Popcnt;
    /// Leading zeros (`clz(0) = W`).
    clz => Clz;
    /// Trailing zeros (`ctz(0) = W`).
    ctz => Ctz;
    /// Byte reversal (`W % 8 == 0`).
    bswap => Bswap;
    /// Bit reversal.
    bitrev => BitRev;
}

binary_shorthands! {
    /// Addition.
    add => Add;
    /// Subtraction.
    sub => Sub;
    /// Multiplication.
    mul => Mul;
    /// High half of the unsigned double-width product.
    umulhi => UMulHi;
    /// High half of the signed double-width product.
    smulhi => SMulHi;
    /// Unsigned division (`udiv(x, 0) = ones`).
    udiv => UDiv;
    /// Unsigned remainder (`urem(x, 0) = x`).
    urem => URem;
    /// Signed division (`bvsdiv`).
    sdiv => SDiv;
    /// Signed remainder (`bvsrem`).
    srem => SRem;
    /// Bitwise and.
    and => And;
    /// Bitwise or.
    or => Or;
    /// Bitwise exclusive or.
    xor => Xor;
    /// Left shift (a count `>= W` gives 0).
    shl => Shl;
    /// Logical right shift (a count `>= W` gives 0).
    lshr => LShr;
    /// Arithmetic right shift (a count `>= W` gives the sign fill).
    ashr => AShr;
    /// Rotate left by `count mod W`.
    rotl => RotL;
    /// Rotate right by `count mod W`.
    rotr => RotR;
    /// Parallel bit deposit.
    pdep => Pdep;
    /// Parallel bit extract.
    pext => Pext;
}

compare_shorthands! {
    /// `a == b`.
    eq => Eq;
    /// `a != b`.
    ne => Ne;
    /// Unsigned `a < b`.
    ult => Ult;
    /// Unsigned `a <= b`.
    ule => Ule;
    /// Unsigned `a > b`.
    ugt => Ugt;
    /// Unsigned `a >= b`.
    uge => Uge;
    /// Signed `a < b`.
    slt => Slt;
    /// Signed `a <= b`.
    sle => Sle;
    /// Signed `a > b`.
    sgt => Sgt;
    /// Signed `a >= b`.
    sge => Sge;
}

/// Derived constructors: they build existing node kinds.
impl Context {
    /// Unsigned minimum.
    pub fn umin(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        let c = self.ult(a, b)?;
        self.select(c, a, b)
    }

    /// Unsigned maximum.
    pub fn umax(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        let c = self.ult(a, b)?;
        self.select(c, b, a)
    }

    /// Signed minimum.
    pub fn smin(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        let c = self.slt(a, b)?;
        self.select(c, a, b)
    }

    /// Signed maximum.
    pub fn smax(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        let c = self.slt(a, b)?;
        self.select(c, b, a)
    }

    /// `a & ~b`.
    pub fn andn(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        let nb = self.not(b)?;
        self.and(a, nb)
    }

    /// `a | ~b`.
    pub fn orn(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        let nb = self.not(b)?;
        self.or(a, nb)
    }

    /// `~(a ^ b)`.
    pub fn xnor(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        let x = self.xor(a, b)?;
        self.not(x)
    }

    /// Bit `i` as a 1-bit value.
    pub fn bit(&mut self, a: Expr, i: u16) -> Result<Expr, Error> {
        self.extract(a, i, Width::W1)
    }

    /// Absolute value (`abs(smin) = smin`).
    pub fn abs(&mut self, a: Expr) -> Result<Expr, Error> {
        let w = self.width(a)?;
        let z = self.zero(w)?;
        let negative = self.slt(a, z)?;
        let n = self.neg(a)?;
        self.select(negative, n, a)
    }

    /// The carry out of `a + b` (1 bit).
    pub fn add_carry(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        let s = self.add(a, b)?;
        self.ult(s, a)
    }

    /// The borrow out of `a - b` (1 bit).
    pub fn sub_borrow(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        self.ult(a, b)
    }

    /// Signed overflow of `a + b` (1 bit).
    pub fn sadd_overflow(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        let s = self.add(a, b)?;
        let x = self.xor(s, a)?;
        let y = self.xor(s, b)?;
        let t = self.and(x, y)?;
        let z = self.zero(self.width(a)?)?;
        self.slt(t, z)
    }

    /// Signed overflow of `a - b` (1 bit).
    pub fn ssub_overflow(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        let d = self.sub(a, b)?;
        let x = self.xor(a, b)?;
        let y = self.xor(a, d)?;
        let t = self.and(x, y)?;
        let z = self.zero(self.width(a)?)?;
        self.slt(t, z)
    }

    /// `a + b` clamped to the unsigned range: all ones when the sum carries out.
    pub fn add_sat_u(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        let s = self.add(a, b)?;
        let c = self.add_carry(a, b)?;
        let ones = self.ones(self.width(a)?)?;
        self.select(c, ones, s)
    }

    /// `a - b` clamped to the unsigned range: 0 when `b` exceeds `a`.
    pub fn sub_sat_u(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        let d = self.sub(a, b)?;
        let borrow = self.ult(a, b)?;
        let zero = self.zero(self.width(a)?)?;
        self.select(borrow, zero, d)
    }

    /// `a + b` clamped to the signed range: the signed minimum or maximum on overflow.
    pub fn add_sat_s(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        let s = self.add(a, b)?;
        let o = self.sadd_overflow(a, b)?;
        // Addition overflows only when both operands have the sign of `a`.
        let limit = self.signed_limit(a)?;
        self.select(o, limit, s)
    }

    /// `a - b` clamped to the signed range: the signed minimum or maximum on overflow.
    pub fn sub_sat_s(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        let d = self.sub(a, b)?;
        let o = self.ssub_overflow(a, b)?;
        // Subtraction overflows only in the direction of `a`'s sign.
        let limit = self.signed_limit(a)?;
        self.select(o, limit, d)
    }

    /// The signed minimum if `a` is negative, else the signed maximum.
    fn signed_limit(&mut self, a: Expr) -> Result<Expr, Error> {
        let w = self.width(a)?;
        let zero = self.zero(w)?;
        let neg = self.slt(a, zero)?;
        let min = self.constant(&BitVec::smin(w))?;
        let max = self.constant(&BitVec::smax(w))?;
        self.select(neg, min, max)
    }

    /// The full `2W`-bit unsigned product (`2W <= 512`).
    pub fn mul_wide_u(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        let hi = self.umulhi(a, b)?;
        let lo = self.mul(a, b)?;
        self.concat(hi, lo)
    }

    /// The full `2W`-bit signed product (`2W <= 512`).
    pub fn mul_wide_s(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        let hi = self.smulhi(a, b)?;
        let lo = self.mul(a, b)?;
        self.concat(hi, lo)
    }
}

/// Whether the unsigned value of `c` is at least `w`.
fn count_at_least(c: &BitVec, w: u16) -> bool {
    c.to_u64().is_none_or(|v| v >= u64::from(w))
}

/// `c mod w` for a shift or rotate count.
pub(crate) fn count_mod(c: &BitVec, w: u16) -> u64 {
    let mut rem: u128 = 0;
    for &l in c.limbs().iter().rev() {
        rem = ((rem << 64) | u128::from(l)) % u128::from(w);
    }
    rem as u64
}

/// Trap guards for hosts that model faulting division or out-of-range shift counts (bitwright's
/// operators are total). A guard is an ordinary 1-bit expression; on a path that does not fault,
/// assume it false ([`Assumptions::assume_false`](crate::Assumptions::assume_false)).
pub mod traps {
    use super::*;

    /// The divide-by-zero guard of an unsigned division: `b == 0`.
    pub fn udiv(cx: &mut Context, _a: Expr, b: Expr) -> Result<Expr, Error> {
        let z = cx.zero(cx.width(b)?)?;
        cx.eq(b, z)
    }

    /// The trap guard of an unsigned remainder: `b == 0`.
    pub fn urem(cx: &mut Context, a: Expr, b: Expr) -> Result<Expr, Error> {
        udiv(cx, a, b)
    }

    /// The trap guard of a signed division that faults on overflow:
    /// `b == 0 | (a == smin & b == -1)`.
    pub fn sdiv(cx: &mut Context, a: Expr, b: Expr) -> Result<Expr, Error> {
        let w = cx.width(b)?;
        let zero = cx.zero(w)?;
        let by_zero = cx.eq(b, zero)?;
        let smin = cx.constant(&BitVec::smin(w))?;
        let minus_one = cx.ones(w)?;
        let a_min = cx.eq(a, smin)?;
        let b_m1 = cx.eq(b, minus_one)?;
        let overflow = cx.and(a_min, b_m1)?;
        cx.or(by_zero, overflow)
    }

    /// The trap guard of a signed remainder on hosts that fault like signed division.
    pub fn srem(cx: &mut Context, a: Expr, b: Expr) -> Result<Expr, Error> {
        sdiv(cx, a, b)
    }

    /// The guard of a shift by an out-of-range count, for hosts that treat it as a fault or as
    /// undefined (bitwright gives it a value): `count >=u W`.
    pub fn shift(cx: &mut Context, count: Expr) -> Result<Expr, Error> {
        let w = cx.width(count)?;
        let limit = cx.constant(&BitVec::wrapping_from_u64(w, u64::from(w.bits())))?;
        cx.uge(count, limit)
    }

    /// The guard of a rotation by an out-of-range count, for hosts that treat it as a fault or
    /// as undefined (bitwright rotates by `count mod W`): `count >=u W`.
    pub fn rotate(cx: &mut Context, count: Expr) -> Result<Expr, Error> {
        shift(cx, count)
    }
}

//! A subset of LLVM IR: functions over integers and floating point with acyclic control
//! flow (`br`, `switch`, `phi`, `ret`, `unreachable`), the instructions of the transformation
//! syntax, and the intrinsics bitwright knows. The attributes that change what a value may be
//! are read on parameters, return values and call sites (`noundef`, `range`, `nofpclass`), and
//! each program is checked with its own; ABI attributes (`zeroext`, `signext`, …) are skipped;
//! any other attribute, or metadata, that a target declares and that may matter makes it
//! unsupported, never ignored. Function attributes are read for the floating-point
//! environment (`strictfp`, denormal modes). Declarations, globals and other metadata are
//! ignored. Uses must be dominated by their definitions, as LLVM's verifier requires.

use std::collections::HashMap;

use super::ir::{Block, Body, Inst, Node, NodeId, Op, ParamAttrs, Term, Transform, Ty};
use super::lex::{Cursor, SyntaxError, Tok, lex, strip_comment};
use super::parse::{Ctx, attributes, type_name};

/// A function definition's text.
#[derive(Clone, Debug)]
pub struct FnText {
    /// Its name (without `@`).
    pub name: String,
    /// The line of `define`.
    pub line: usize,
    /// The header, from `define` to `{`.
    header: String,
    /// The body lines, with their numbers.
    body: Vec<(usize, String)>,
    /// Its function attributes, attribute groups (`#0`) resolved.
    attrs: String,
}

/// The function definitions of a module.
pub fn functions(text: &str) -> Result<Vec<FnText>, SyntaxError> {
    let mut out = Vec::new();
    let mut cur: Option<FnText> = None;
    // A statement that continues on the next lines (a `switch`'s cases), and its first line.
    let mut open: Option<(usize, String)> = None;
    // Attribute groups: `attributes #0 = { … }`.
    let mut groups: HashMap<String, String> = HashMap::new();
    for (k, raw) in text.lines().enumerate() {
        let n = k + 1;
        let line = strip_comment(raw).trim();
        if let Some(f) = cur.as_mut() {
            if let Some((start, mut acc)) = open.take() {
                acc.push(' ');
                acc.push_str(line);
                if brackets(&acc) > 0 {
                    open = Some((start, acc));
                } else {
                    f.body.push((start, acc));
                }
            } else if line == "}" {
                out.push(cur.take().expect("in a function"));
            } else if brackets(line) > 0 {
                open = Some((n, line.to_string()));
            } else if !line.is_empty() {
                f.body.push((n, line.to_string()));
            }
            continue;
        }
        if let Some(rest) = line.strip_prefix("attributes #")
            && let Some((id, body)) = rest.split_once('=')
        {
            let body = body.trim();
            let inner = body
                .strip_prefix('{')
                .and_then(|b| b.strip_suffix('}'))
                .unwrap_or(body);
            groups.insert(id.trim().to_string(), inner.trim().to_string());
            continue;
        }
        if line.starts_with("define ") || line == "define" {
            let Some(open) = line.rfind('{') else {
                return Err(SyntaxError {
                    line: n,
                    message: "expected `{` at the end of the `define` line".into(),
                });
            };
            let header = line[..open].to_string();
            let Some(at) = header.find('@') else {
                return Err(SyntaxError {
                    line: n,
                    message: "a function without a name".into(),
                });
            };
            let rest = &header[at + 1..];
            let name: String = if let Some(q) = rest.strip_prefix('"') {
                q.chars().take_while(|&c| c != '"').collect()
            } else {
                rest.chars()
                    .take_while(|&c| {
                        c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '$' | '-')
                    })
                    .collect()
            };
            cur = Some(FnText {
                name,
                line: n,
                header,
                body: Vec::new(),
                attrs: String::new(),
            });
        }
    }
    if let Some(f) = cur {
        return Err(SyntaxError {
            line: f.line,
            message: format!("@{} has no closing `}}`", f.name),
        });
    }
    // Function attributes: the header after the parameter list, groups resolved.
    for f in &mut out {
        let tail = header_tail(&f.header);
        let mut attrs = String::new();
        for word in tail.split_whitespace() {
            match word.strip_prefix('#').and_then(|id| groups.get(id)) {
                Some(g) => attrs.push_str(g),
                None => attrs.push_str(word),
            }
            attrs.push(' ');
        }
        f.attrs = attrs;
    }
    Ok(out)
}

/// The header after its parameter list (function attributes, `local_unnamed_addr`, …).
fn header_tail(header: &str) -> &str {
    let Some(at) = header.find('@') else {
        return "";
    };
    let Some(open) = header[at..].find('(').map(|k| at + k) else {
        return "";
    };
    let mut depth = 0i32;
    let mut quoted = false;
    for (i, ch) in header[open..].char_indices() {
        match ch {
            '"' => quoted = !quoted,
            '(' if !quoted => depth += 1,
            ')' if !quoted => {
                depth -= 1;
                if depth == 0 {
                    return &header[open + i + 1..];
                }
            }
            _ => {}
        }
    }
    ""
}

/// The floating-point environment function attributes declare, when it is not the default
/// one bitwright models (round to nearest, subnormals kept, no traps), or when they relax its
/// semantics (`"no-nans-fp-math"`, …), which counts only for a target (`target`).
fn float_env(attrs: &str, target: bool) -> Option<String> {
    let value = |key: &str| -> Option<&str> {
        let pat = format!("\"{key}\"=\"");
        let start = attrs.find(&pat)? + pat.len();
        attrs[start..].split('"').next()
    };
    if attrs.split_whitespace().any(|w| w == "strictfp") {
        return Some("`strictfp` (a floating-point environment other than the default)".into());
    }
    for key in ["denormal-fp-math", "denormal-fp-math-f32"] {
        if let Some(v) = value(key)
            && !matches!(v, "ieee" | "ieee,ieee")
        {
            return Some(format!(
                "\"{key}\"=\"{v}\" (subnormals flushed: bitwright models IEEE 754 subnormals)"
            ));
        }
    }
    if target {
        for key in [
            "no-nans-fp-math",
            "no-infs-fp-math",
            "no-signed-zeros-fp-math",
            "unsafe-fp-math",
            "approx-func-fp-math",
        ] {
            if value(key) == Some("true") {
                return Some(format!(
                    "the target's \"{key}\"=\"true\" (relaxed floating point, not modeled)"
                ));
            }
        }
    }
    None
}

/// Open `[` brackets on a line, outside quotes (a quoted name may hold one: `%"a[b"`).
fn brackets(line: &str) -> i32 {
    let mut quoted = false;
    line.chars().fold(0, |d, c| match c {
        '"' => {
            quoted = !quoted;
            d
        }
        '[' if !quoted => d + 1,
        ']' if !quoted => d - 1,
        _ => d,
    })
}

/// The block a line labels, if it is a label: by LLVM's grammar, a name of `[-a-zA-Z$._0-9]`
/// (`entry`, `.lr.ph`, `if-then`, `7`) or a quoted name (`"a b"`), then its colon, alone on
/// the line.
fn block_label(line: &str) -> Option<&str> {
    let name = line.strip_suffix(':')?;
    match name.strip_prefix('"') {
        Some(quoted) => quoted.strip_suffix('"').filter(|q| !q.contains('"')),
        None => (!name.is_empty()
            && name
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'$' | b'.' | b'_')))
        .then_some(name),
    }
}

/// Whether a line calls a `llvm.dbg.` intrinsic (`call void @llvm.dbg.value(metadata …)`).
fn debug_call(toks: &[Tok]) -> bool {
    let call = match toks {
        [Tok::Ident(t), rest @ ..] if matches!(t.as_str(), "tail" | "musttail" | "notail") => rest,
        _ => toks,
    };
    matches!(call, [Tok::Ident(c), Tok::Ident(v), Tok::Global(f), ..]
        if c == "call" && v == "void" && f.starts_with("llvm.dbg."))
}

/// Classes of `nofpclass`, as bits.
pub(crate) mod fpclass {
    pub const SNAN: u16 = 1;
    pub const QNAN: u16 = 1 << 1;
    pub const NINF: u16 = 1 << 2;
    pub const NNORM: u16 = 1 << 3;
    pub const NSUB: u16 = 1 << 4;
    pub const NZERO: u16 = 1 << 5;
    pub const PZERO: u16 = 1 << 6;
    pub const PSUB: u16 = 1 << 7;
    pub const PNORM: u16 = 1 << 8;
    pub const PINF: u16 = 1 << 9;

    pub fn parse(s: &str) -> Option<u16> {
        Some(match s {
            "nan" => SNAN | QNAN,
            "snan" => SNAN,
            "qnan" => QNAN,
            "inf" => NINF | PINF,
            "ninf" => NINF,
            "pinf" => PINF,
            "norm" => NNORM | PNORM,
            "nnorm" => NNORM,
            "pnorm" => PNORM,
            "sub" => NSUB | PSUB,
            "nsub" => NSUB,
            "psub" => PSUB,
            "zero" => NZERO | PZERO,
            "nzero" => NZERO,
            "pzero" => PZERO,
            "all" => 0x3ff,
            _ => return None,
        })
    }
}

/// A function's parameters: their names, types and attributes. The return type and whether
/// the return value is `noundef` come first.
struct Header {
    ret: Option<Ty>,
    ret_attrs: ParamAttrs,
    /// Return attributes that may matter and that bitwright does not model.
    ret_other: Vec<String>,
    params: Vec<Param>,
    /// Whether a parameter or the return value is a pointer.
    pointers: bool,
}

struct Param {
    name: String,
    ty: Ty,
    attrs: ParamAttrs,
    /// Attributes that may matter and that bitwright does not model.
    other: Vec<String>,
}

fn header(f: &FnText) -> Result<Header, SyntaxError> {
    let toks = lex(&f.header, f.line)?;
    let mut c = Cursor::new(&toks, f.line);
    c.eat_word("define");
    // Linkage, visibility and the like, then return attributes and the return type.
    while let Some(w) = c.peek_word() {
        if type_name(w).is_some()
            || w == "void"
            || matches!(w, "noundef" | "range" | "nofpclass" | "zeroext" | "signext")
        {
            break;
        }
        c.pos += 1;
    }
    let (ret_attrs, ret_other) = attributes(&mut c, false)?;
    let mut pointers = false;
    let ret = if c.eat_word("void") {
        None
    } else {
        match c.word() {
            Some(w) if type_name(w).is_some() => {
                pointers |= w == "ptr";
                type_name(w)
            }
            _ => return c.err("expected the return type (an integer or floating-point type)"),
        }
    };
    match c.next() {
        Some(Tok::Global(_)) => {}
        _ => return c.err("expected the function's name"),
    }
    c.expect("(")?;
    let mut params = Vec::new();
    let mut unnamed = 0u32;
    if !c.eat(")") {
        loop {
            let ty = match c.word() {
                Some(w) if type_name(w).is_some() => {
                    pointers |= w == "ptr";
                    type_name(w).expect("checked")
                }
                _ => return c.err("expected a parameter type (integers and floating point only)"),
            };
            let (attrs, other) = attributes(&mut c, false)?;
            let name = match c.peek() {
                Some(Tok::Local(n)) => {
                    let n = n.clone();
                    c.pos += 1;
                    n
                }
                _ => {
                    let n = unnamed.to_string();
                    unnamed += 1;
                    n
                }
            };
            params.push(Param {
                name,
                ty,
                attrs,
                other,
            });
            if c.eat(")") {
                break;
            }
            c.expect(",")?;
        }
    }
    Ok(Header {
        ret,
        ret_attrs,
        ret_other,
        params,
        pointers,
    })
}

/// Adds function `f` to `t` as the source (`src` none: its parameters become the inputs) or
/// as the target (`src`: the source's header, whose parameters are the inputs, by position).
fn body(t: &mut Transform, f: &FnText, src: Option<&Header>) -> Result<Body, SyntaxError> {
    let h = header(f)?;
    t.pointers |= h.pointers;
    if t.float_env.is_none() {
        t.float_env = float_env(&f.attrs, src.is_some());
    }
    let mut names: HashMap<String, NodeId> = HashMap::new();
    match src {
        None => {
            for p in &h.params {
                let n = t.push(
                    Node::Input {
                        name: p.name.clone(),
                        noundef: p.attrs.noundef,
                        range: p.attrs.range.clone(),
                    },
                    Some(p.ty),
                );
                t.inputs.push(n);
                if p.attrs.nofpclass != 0 {
                    t.nofpclass.push((n, p.attrs.nofpclass));
                }
                names.insert(p.name.clone(), n);
            }
        }
        Some(sh) => {
            if sh.params.len() != h.params.len() {
                return Err(SyntaxError {
                    line: f.line,
                    message: format!(
                        "@{} has {} parameters, the source {}",
                        f.name,
                        h.params.len(),
                        sh.params.len()
                    ),
                });
            }
            for (k, (p, sp)) in h.params.iter().zip(&sh.params).enumerate() {
                let n = t.inputs[k];
                if t.types[n as usize] != Some(p.ty) {
                    return Err(SyntaxError {
                        line: f.line,
                        message: format!(
                            "parameter %{} of @{} has another type than the source's",
                            p.name, f.name
                        ),
                    });
                }
                // What the target adds that may matter and is not modeled: refused.
                for o in p.other.iter().filter(|o| !sp.other.contains(o)) {
                    t.unsupported.push(format!(
                        "the target's parameter %{} has `{o}`, which bitwright does not model",
                        p.name
                    ));
                }
                names.insert(p.name.clone(), n);
            }
            for o in h.ret_other.iter().filter(|o| !sh.ret_other.contains(o)) {
                t.unsupported.push(format!(
                    "the target's return value has `{o}`, which bitwright does not model"
                ));
            }
        }
    }
    // Pass 1: blocks and the registers instructions define.
    let mut blocks: Vec<Block> = Vec::new();
    let mut block_of: HashMap<String, usize> = HashMap::new();
    let mut lines: Vec<(usize, Vec<Tok>, usize)> = Vec::new();
    // Each block's first line (its label, or its first instruction).
    let mut block_line: Vec<usize> = Vec::new();
    let mut unnamed = h
        .params
        .iter()
        .filter(|p| p.name.parse::<u32>().is_ok())
        .count() as u32;
    for (n, text) in &f.body {
        // A label is read by its own grammar: the tokens of an instruction would split
        // `if-then` and refuse `.lr.ph`.
        if let Some(l) = block_label(text) {
            let l = l.to_string();
            if block_of.insert(l.clone(), blocks.len()).is_some() {
                return Err(SyntaxError {
                    line: *n,
                    message: format!("block %{l} is defined twice"),
                });
            }
            blocks.push(Block {
                name: l,
                insts: Vec::new(),
                term: Term::Unreachable,
            });
            block_line.push(*n);
            continue;
        }
        // Debug records say nothing about values: `#dbg_value(…)` (LLVM 19 on) is not read,
        // nor is a call of a `llvm.dbg.` intrinsic (how LLVM wrote them before).
        if text.starts_with("#dbg_") {
            continue;
        }
        let toks = lex(text, *n)?;
        if debug_call(&toks) {
            continue;
        }
        if blocks.is_empty() {
            let l = unnamed.to_string();
            unnamed += 1;
            block_of.insert(l.clone(), 0);
            blocks.push(Block {
                name: l,
                insts: Vec::new(),
                term: Term::Unreachable,
            });
            block_line.push(*n);
        }
        if let [Tok::Local(r), Tok::P("="), ..] = toks.as_slice() {
            if names.contains_key(r) {
                return Err(SyntaxError {
                    line: *n,
                    message: format!("%{r} is defined twice"),
                });
            }
            let id = t.push(Node::Inst(Inst::new(r, Op::Freeze)), None);
            names.insert(r.clone(), id);
        }
        lines.push((*n, toks, blocks.len() - 1));
    }
    if blocks.is_empty() {
        return Err(SyntaxError {
            line: f.line,
            message: format!("@{} has no body", f.name),
        });
    }
    // Pass 2: instructions and terminators, block by block.
    let mut cx = Ctx {
        t,
        names,
        syms: HashMap::new(),
        alive: false,
        blocks: block_of.clone(),
        expression_depth: 0,
    };
    let mut b = 0usize;
    let mut terminated = vec![false; blocks.len()];
    // Where each instruction is, and its line; each terminator's line.
    let mut at: HashMap<NodeId, (usize, usize)> = HashMap::new();
    let mut line_of: HashMap<NodeId, usize> = HashMap::new();
    let mut term_line = vec![f.line; blocks.len()];
    for (n, toks, nb) in &lines {
        let nb = *nb;
        if nb != b {
            if !terminated[b] {
                return Err(SyntaxError {
                    line: *n,
                    message: format!("block %{} has no terminator", blocks[b].name),
                });
            }
            b = nb;
        }
        if terminated[b] {
            return Err(SyntaxError {
                line: *n,
                message: "an instruction after a terminator".into(),
            });
        }
        let mut c = Cursor::new(toks, *n);
        let mut terminator = true;
        match c.peek_word() {
            Some("ret") => {
                c.pos += 1;
                blocks[b].term = if c.eat_word("void") {
                    Term::Ret(None)
                } else {
                    let v = cx.operand(&mut c)?;
                    if let Some(rt) = h.ret {
                        cx.annotate(&c, v, rt)?;
                    }
                    Term::Ret(Some(v))
                };
                c.end()?;
            }
            Some("br") => {
                c.pos += 1;
                if c.eat_word("label") {
                    let Some(Tok::Local(l)) = c.next() else {
                        return c.err("expected a label");
                    };
                    blocks[b].term = Term::Jmp(label(&c, &block_of, l)?);
                } else {
                    let cond = cx.operand(&mut c)?;
                    cx.annotate(&c, cond, Ty::Int(1))?;
                    c.expect(",")?;
                    let tb = expect_label(&mut c, &block_of)?;
                    c.expect(",")?;
                    let fb = expect_label(&mut c, &block_of)?;
                    blocks[b].term = Term::Br(cond, tb, fb);
                }
                c.end()?;
            }
            Some("switch") => {
                c.pos += 1;
                let v = cx.operand(&mut c)?;
                c.expect(",")?;
                let dflt = expect_label(&mut c, &block_of)?;
                c.expect("[")?;
                let mut cases = Vec::new();
                while !c.eat("]") {
                    let lit = cx.operand(&mut c)?;
                    c.expect(",")?;
                    let to = expect_label(&mut c, &block_of)?;
                    cases.push((lit, to));
                }
                blocks[b].term = Term::Switch(v, dflt, cases);
                c.end()?;
            }
            Some("unreachable") => {
                c.pos += 1;
                blocks[b].term = Term::Unreachable;
                c.end()?;
            }
            _ => {
                terminator = false;
                let name = match (c.peek(), c.peek_at(1)) {
                    (Some(Tok::Local(r)), Some(Tok::P("="))) => {
                        let r = r.clone();
                        c.pos += 2;
                        r
                    }
                    _ => String::new(),
                };
                let (inst, ty) = cx.inst(&mut c, &name)?;
                let id = if name.is_empty() {
                    cx.t.push(Node::Inst(inst), None)
                } else {
                    let id = cx.names[&name];
                    cx.t.nodes[id as usize] = Node::Inst(inst);
                    id
                };
                if let Some(ty) = ty {
                    cx.annotate(&c, id, ty)?;
                }
                at.insert(id, (b, blocks[b].insts.len()));
                line_of.insert(id, *n);
                blocks[b].insts.push(id);
            }
        }
        if terminator {
            terminated[b] = true;
            term_line[b] = *n;
        }
    }
    // Every block ends in a terminator (an empty one too: it is not `unreachable`).
    if let Some(k) = terminated.iter().position(|&done| !done) {
        return Err(SyntaxError {
            line: block_line[k],
            message: format!("block %{} has no terminator", blocks[k].name),
        });
    }
    let t = cx.t;
    dominance(t, &blocks, &at, &line_of, &term_line)?;
    Ok(Body {
        blocks,
        root: None,
        matched: Vec::new(),
        params: h.params.iter().map(|p| p.attrs.clone()).collect(),
        ret_noundef: h.ret_attrs.noundef,
        ret_range: h.ret_attrs.range,
        ret_nofpclass: h.ret_attrs.nofpclass,
        returns_value: h.ret.is_some(),
    })
}

/// The successors of block `b`.
fn successors(blocks: &[Block], b: usize) -> Vec<usize> {
    match &blocks[b].term {
        Term::Jmp(t) => vec![*t],
        Term::Br(_, t, f) => vec![*t, *f],
        Term::Switch(_, d, cases) => {
            let mut v: Vec<usize> = cases.iter().map(|&(_, t)| t).collect();
            v.push(*d);
            v
        }
        _ => Vec::new(),
    }
}

/// Checks that every use in a reachable block is dominated by its definition, as LLVM's
/// verifier does (so no value depends on itself, and each is computed before it is read).
fn dominance(
    t: &Transform,
    blocks: &[Block],
    at: &HashMap<NodeId, (usize, usize)>,
    line_of: &HashMap<NodeId, usize>,
    term_line: &[usize],
) -> Result<(), SyntaxError> {
    let n = blocks.len();
    // Reverse post-order of the reachable blocks.
    let mut post = Vec::with_capacity(n);
    let mut seen = vec![false; n];
    let mut stack: Vec<(usize, usize)> = vec![(0, 0)];
    seen[0] = true;
    while let Some(&mut (b, ref mut k)) = stack.last_mut() {
        let s = successors(blocks, b);
        if *k < s.len() {
            let next = s[*k];
            *k += 1;
            if !seen[next] {
                seen[next] = true;
                stack.push((next, 0));
            }
        } else {
            post.push(b);
            stack.pop();
        }
    }
    let rpo: Vec<usize> = post.iter().rev().copied().collect();
    let mut order = vec![usize::MAX; n];
    for (i, &b) in rpo.iter().enumerate() {
        order[b] = i;
    }
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    // Every edge, from reachable blocks or not, for the phis.
    let mut edges: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (b, &reached) in seen.iter().enumerate() {
        for s in successors(blocks, b) {
            edges[s].push(b);
            if reached {
                preds[s].push(b);
            }
        }
    }
    // A phi has one entry per edge into its block (one value for the edges of one block).
    for (b, block) in blocks.iter().enumerate() {
        for &id in &block.insts {
            let Node::Inst(inst) = t.node(id) else {
                continue;
            };
            if inst.op != Op::Phi {
                continue;
            }
            let line = line_of.get(&id).copied().unwrap_or(0);
            let mut from = inst.incoming.clone();
            from.sort_unstable();
            let mut want = edges[b].clone();
            want.sort_unstable();
            if from != want {
                return Err(SyntaxError {
                    line,
                    message: format!(
                        "{} needs one entry for each edge into block %{}",
                        t.label(id),
                        block.name
                    ),
                });
            }
            // One value: one register, or equal literals (each written literal is a node).
            let same = |x: NodeId, y: NodeId| {
                x == y || matches!((t.node(x), t.node(y)), (Node::Lit(a), Node::Lit(b)) if a == b)
            };
            for (k, (&x, &p)) in inst.args.iter().zip(&inst.incoming).enumerate() {
                let differs = inst.args[..k]
                    .iter()
                    .zip(&inst.incoming)
                    .any(|(&y, &q)| q == p && !same(x, y));
                if differs {
                    return Err(SyntaxError {
                        line,
                        message: format!(
                            "{} gives two values for the edges from block %{}",
                            t.label(id),
                            blocks[p].name
                        ),
                    });
                }
            }
        }
    }
    // Immediate dominators (Cooper, Harvey and Kennedy).
    let mut idom = vec![usize::MAX; n];
    idom[0] = 0;
    let mut changed = true;
    while changed {
        changed = false;
        for &b in rpo.iter().skip(1) {
            let mut new = usize::MAX;
            for &p in &preds[b] {
                if idom[p] == usize::MAX {
                    continue;
                }
                new = if new == usize::MAX {
                    p
                } else {
                    let (mut x, mut y) = (p, new);
                    while x != y {
                        while order[x] > order[y] {
                            x = idom[x];
                        }
                        while order[y] > order[x] {
                            y = idom[y];
                        }
                    }
                    x
                };
            }
            if new != idom[b] {
                idom[b] = new;
                changed = true;
            }
        }
    }
    let dominates = |a: usize, mut b: usize| -> bool {
        loop {
            if a == b {
                return true;
            }
            if b == 0 || idom[b] == usize::MAX {
                return false;
            }
            b = idom[b];
        }
    };
    // `x` read in block `b` before position `pos` (`usize::MAX`: the terminator).
    let check = |x: NodeId, b: usize, pos: usize, line: usize| -> Result<(), SyntaxError> {
        let Some(&(db, di)) = at.get(&x) else {
            return Ok(());
        };
        let fine = if db == b {
            di < pos
        } else {
            seen[db] && dominates(db, b)
        };
        if fine {
            return Ok(());
        }
        let what = if db == b && di == pos {
            format!("{} is read in its own definition", t.label(x))
        } else {
            format!("{} does not dominate this use", t.label(x))
        };
        Err(SyntaxError {
            line,
            message: what,
        })
    };
    for &b in &rpo {
        for (i, &id) in blocks[b].insts.iter().enumerate() {
            let Node::Inst(inst) = t.node(id) else {
                continue;
            };
            let line = line_of.get(&id).copied().unwrap_or(0);
            if inst.op == Op::Phi {
                // An incoming value is read at the end of its block.
                for (&x, &from) in inst.args.iter().zip(&inst.incoming) {
                    if seen[from] {
                        check(x, from, usize::MAX, line)?;
                    }
                }
            } else {
                for &x in &inst.args {
                    check(x, b, i, line)?;
                }
            }
        }
        let line = term_line[b];
        match &blocks[b].term {
            Term::Ret(Some(v)) | Term::Br(v, ..) | Term::Switch(v, ..) => {
                check(*v, b, usize::MAX, line)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn label(c: &Cursor<'_>, blocks: &HashMap<String, usize>, l: &str) -> Result<usize, SyntaxError> {
    match blocks.get(l) {
        Some(&b) => Ok(b),
        None => c.err(format!("unknown block %{l}")),
    }
}

fn expect_label(c: &mut Cursor<'_>, blocks: &HashMap<String, usize>) -> Result<usize, SyntaxError> {
    if !c.eat_word("label") {
        return c.err("expected `label`");
    }
    match c.next() {
        Some(Tok::Local(l)) => {
            let l = l.clone();
            label(c, blocks, &l)
        }
        _ => c.err("expected a block label"),
    }
}

/// One function as the source of a transformation without a target (for lifting).
pub(crate) fn single(f: &FnText) -> Result<Transform, SyntaxError> {
    let mut t = Transform::new(f.name.clone());
    t.src = body(&mut t, f, None)?;
    t.tgt.returns_value = t.src.returns_value;
    Ok(t)
}

/// The transformation that `tgt` refines `src`: two functions of one signature, their
/// parameters the shared inputs by position.
pub fn function_pair(src: &FnText, tgt: &FnText) -> Result<Transform, SyntaxError> {
    let mut t = Transform::new(if src.name == tgt.name {
        src.name.clone()
    } else {
        format!("{} => {}", src.name, tgt.name)
    });
    let sh = header(src)?;
    let sb = body(&mut t, src, None)?;
    let tb = body(&mut t, tgt, Some(&sh))?;
    if sb.returns_value != tb.returns_value {
        return Err(SyntaxError {
            line: tgt.line,
            message: format!("@{} and @{} return different types", src.name, tgt.name),
        });
    }
    t.src = sb;
    t.tgt = tb;
    Ok(t)
}

/// The function pairs to validate: `@src` and `@tgt` of one module; or, with a second module,
/// each function of the first with the function of the same name in the second.
pub fn pairs(first: &str, second: Option<&str>) -> Result<Vec<Transform>, SyntaxError> {
    pairs_each(first, second)?
        .into_iter()
        .map(|(_, t)| t)
        .collect()
}

/// A function pair's name and its transformation, or why it cannot be read.
pub type Pair = (String, Result<Transform, SyntaxError>);

/// [`pairs`], each pair read on its own: a pair outside the subset comes with its error,
/// named, and the others are still read. The error is the module's (a function without its
/// closing brace, no `@src` and `@tgt`, no function in both files).
pub fn pairs_each(first: &str, second: Option<&str>) -> Result<Vec<Pair>, SyntaxError> {
    let a = functions(first)?;
    match second {
        None => {
            let src = a.iter().find(|f| f.name == "src");
            let tgt = a.iter().find(|f| f.name == "tgt");
            match (src, tgt) {
                (Some(s), Some(t)) => Ok(vec![("src => tgt".into(), function_pair(s, t))]),
                _ => Err(SyntaxError {
                    line: 1,
                    message: "expected functions @src and @tgt (or a second file)".into(),
                }),
            }
        }
        Some(second) => {
            let b = functions(second)?;
            let mut out = Vec::new();
            for f in &a {
                if let Some(g) = b.iter().find(|g| g.name == f.name) {
                    out.push((f.name.clone(), function_pair(f, g)));
                }
            }
            if out.is_empty() {
                return Err(SyntaxError {
                    line: 1,
                    message: "no function is defined in both files".into(),
                });
            }
            Ok(out)
        }
    }
}

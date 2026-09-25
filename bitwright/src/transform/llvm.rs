//! A subset of LLVM IR: functions over integers and floating point with acyclic control
//! flow (`br`, `switch`, `phi`, `ret`, `unreachable`), the instructions of the transformation
//! syntax, and the intrinsics bitwright knows. Parameter attributes that change what a value
//! may be are read (`noundef`, `range`, `nofpclass`); others are skipped. Declarations,
//! globals, metadata and attribute groups are ignored.

use std::collections::HashMap;

use super::ir::{Block, Body, Inst, Node, NodeId, Op, Term, Transform, Ty};
use super::lex::{Cursor, SyntaxError, Tok, lex, strip_comment};
use super::parse::{Ctx, type_name};

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
}

/// The function definitions of a module.
pub fn functions(text: &str) -> Result<Vec<FnText>, SyntaxError> {
    let mut out = Vec::new();
    let mut cur: Option<FnText> = None;
    // A statement that continues on the next lines (a `switch`'s cases), and its first line.
    let mut open: Option<(usize, String)> = None;
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
            });
        }
    }
    if let Some(f) = cur {
        return Err(SyntaxError {
            line: f.line,
            message: format!("@{} has no closing `}}`", f.name),
        });
    }
    Ok(out)
}

/// Open `[` brackets on a line.
fn brackets(line: &str) -> i32 {
    line.chars().fold(0, |d, c| match c {
        '[' => d + 1,
        ']' => d - 1,
        _ => d,
    })
}

/// What a parameter declares besides its type.
#[derive(Default)]
struct Attrs {
    noundef: bool,
    range: Option<(String, String)>,
    nofpclass: u16,
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

/// Parameter or return attributes at the cursor (skipping the ones without meaning here).
fn attrs(c: &mut Cursor<'_>) -> Result<Attrs, SyntaxError> {
    let mut a = Attrs::default();
    loop {
        match c.peek() {
            Some(Tok::Ident(w)) => {
                let w = w.clone();
                // A type ends the attributes of a return value.
                if type_name(&w).is_some() || w == "void" {
                    break;
                }
                c.pos += 1;
                match w.as_str() {
                    "noundef" => a.noundef = true,
                    "range" => {
                        c.expect("(")?;
                        c.word();
                        let lo = signed_num(c)?;
                        c.expect(",")?;
                        let hi = signed_num(c)?;
                        c.expect(")")?;
                        a.range = Some((lo, hi));
                    }
                    "nofpclass" => {
                        c.expect("(")?;
                        while let Some(w) = c.word() {
                            match fpclass::parse(w) {
                                Some(b) => a.nofpclass |= b,
                                None => return c.err(format!("unknown class `{w}` in nofpclass")),
                            }
                        }
                        c.expect(")")?;
                    }
                    _ => {
                        // `align 4`, `dereferenceable(8)`, `byval(i32)`, …: skip arguments.
                        if c.eat("(") {
                            let mut depth = 1;
                            while depth > 0 {
                                match c.next() {
                                    Some(Tok::P("(")) => depth += 1,
                                    Some(Tok::P(")")) => depth -= 1,
                                    None => return c.err("unbalanced parentheses"),
                                    _ => {}
                                }
                            }
                        } else if matches!(c.peek(), Some(Tok::Num(_))) {
                            c.pos += 1;
                        }
                    }
                }
            }
            Some(Tok::P("#")) => {
                c.pos += 1;
                c.next();
            }
            _ => break,
        }
    }
    Ok(a)
}

fn signed_num(c: &mut Cursor<'_>) -> Result<String, SyntaxError> {
    let neg = c.eat("-");
    match c.next() {
        Some(Tok::Num(s)) => Ok(if neg { format!("-{s}") } else { s.clone() }),
        Some(Tok::Ident(w)) if w == "true" => Ok("1".into()),
        Some(Tok::Ident(w)) if w == "false" => Ok("0".into()),
        _ => c.err("expected a number"),
    }
}

/// A function's parameters: their names, types and attributes. The return type and whether
/// the return value is `noundef` come first.
struct Header {
    ret: Option<Ty>,
    ret_attrs: Attrs,
    params: Vec<(String, Ty, Attrs)>,
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
    let ret_attrs = attrs(&mut c)?;
    let ret = if c.eat_word("void") {
        None
    } else {
        match c.word().and_then(type_name) {
            Some(t) => Some(t),
            None => return c.err("expected the return type (an integer or floating-point type)"),
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
            let Some(ty) = c.word().and_then(type_name) else {
                return c.err("expected a parameter type (integers and floating point only)");
            };
            let a = attrs(&mut c)?;
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
            params.push((name, ty, a));
            if c.eat(")") {
                break;
            }
            c.expect(",")?;
        }
    }
    Ok(Header {
        ret,
        ret_attrs,
        params,
    })
}

/// Adds function `f` to `t` as the source (`inputs` empty: its parameters become the inputs)
/// or the target (its parameters are the inputs, by position).
fn body(t: &mut Transform, f: &FnText, inputs: Option<&[NodeId]>) -> Result<Body, SyntaxError> {
    let h = header(f)?;
    let mut names: HashMap<String, NodeId> = HashMap::new();
    match inputs {
        None => {
            for (name, ty, a) in &h.params {
                let n = t.push(
                    Node::Input {
                        name: name.clone(),
                        noundef: a.noundef,
                        range: a.range.clone(),
                    },
                    Some(*ty),
                );
                t.inputs.push(n);
                if a.nofpclass != 0 {
                    t.nofpclass.push((n, a.nofpclass));
                }
                names.insert(name.clone(), n);
            }
        }
        Some(ins) => {
            if ins.len() != h.params.len() {
                return Err(SyntaxError {
                    line: f.line,
                    message: format!(
                        "@{} has {} parameters, the source {}",
                        f.name,
                        h.params.len(),
                        ins.len()
                    ),
                });
            }
            for ((name, ty, _), &n) in h.params.iter().zip(ins) {
                if t.types[n as usize] != Some(*ty) {
                    return Err(SyntaxError {
                        line: f.line,
                        message: format!(
                            "parameter %{name} of @{} has another type than the source's",
                            f.name
                        ),
                    });
                }
                names.insert(name.clone(), n);
            }
        }
    }
    // Pass 1: blocks and the registers instructions define.
    let mut blocks: Vec<Block> = Vec::new();
    let mut block_of: HashMap<String, usize> = HashMap::new();
    let mut lines: Vec<(usize, Vec<Tok>, usize)> = Vec::new();
    let mut unnamed = h
        .params
        .iter()
        .filter(|(n, ..)| n.parse::<u32>().is_ok())
        .count() as u32;
    for (n, text) in &f.body {
        let toks = lex(text, *n)?;
        let label = match toks.as_slice() {
            [Tok::Ident(l), Tok::P(":")] | [Tok::Num(l), Tok::P(":")] => Some(l.clone()),
            [Tok::Str(l), Tok::P(":")] => Some(l.clone()),
            _ => None,
        };
        if let Some(l) = label {
            block_of.insert(l.clone(), blocks.len());
            blocks.push(Block {
                name: l,
                insts: Vec::new(),
                term: Term::Unreachable,
            });
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
        }
        if let [Tok::Local(r), Tok::P("="), ..] = toks.as_slice() {
            if names.contains_key(r) {
                return Err(SyntaxError {
                    line: *n,
                    message: format!("%{r} is defined twice"),
                });
            }
            let id = t.push(
                Node::Inst(Inst {
                    name: r.clone(),
                    op: Op::Freeze,
                    flags: 0,
                    args: Vec::new(),
                    incoming: Vec::new(),
                }),
                None,
            );
            names.insert(r.clone(), id);
        }
        lines.push((*n, toks, blocks.len() - 1));
    }
    // Pass 2: instructions and terminators, block by block.
    let mut cx = Ctx {
        t,
        names,
        syms: HashMap::new(),
        alive: false,
        blocks: block_of.clone(),
    };
    let mut b = 0usize;
    let mut terminated = false;
    for (n, toks, nb) in &lines {
        let nb = *nb;
        if nb != b {
            if !terminated {
                return Err(SyntaxError {
                    line: *n,
                    message: format!("block %{} has no terminator", blocks[b].name),
                });
            }
            b = nb;
            terminated = false;
        }
        if terminated {
            return Err(SyntaxError {
                line: *n,
                message: "an instruction after a terminator".into(),
            });
        }
        let mut c = Cursor::new(toks, *n);
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
                terminated = true;
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
                terminated = true;
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
                terminated = true;
            }
            Some("unreachable") => {
                blocks[b].term = Term::Unreachable;
                terminated = true;
            }
            _ => {
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
                blocks[b].insts.push(id);
            }
        }
    }
    if !terminated && !blocks.is_empty() {
        return Err(SyntaxError {
            line: f.line,
            message: format!("block %{} has no terminator", blocks[b].name),
        });
    }
    if blocks.is_empty() {
        return Err(SyntaxError {
            line: f.line,
            message: format!("@{} has no body", f.name),
        });
    }
    Ok(Body {
        blocks,
        root: None,
        ret_noundef: h.ret_attrs.noundef,
        ret_range: h.ret_attrs.range,
        ret_nofpclass: h.ret_attrs.nofpclass,
        returns_value: h.ret.is_some(),
    })
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
    let sb = body(&mut t, src, None)?;
    let inputs = t.inputs.clone();
    let tb = body(&mut t, tgt, Some(&inputs))?;
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
    let a = functions(first)?;
    match second {
        None => {
            let src = a.iter().find(|f| f.name == "src");
            let tgt = a.iter().find(|f| f.name == "tgt");
            match (src, tgt) {
                (Some(s), Some(t)) => Ok(vec![function_pair(s, t)?]),
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
                    out.push(function_pair(f, g)?);
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

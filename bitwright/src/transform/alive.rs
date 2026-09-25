//! The transformation syntax, after the one the Alive paper introduced (Lopes et al., PLDI
//! 2015): an optional name and precondition, source instructions, `=>`, target instructions.
//!
//! ```text
//! Name: mul by a power of two
//! Pre: isPowerOf2(C)
//! %r = mul %x, C
//!   =>
//! %r = shl %x, log2(C)
//! ```
//!
//! Registers the source reads without defining them are inputs; words in operands are
//! symbolic constants; types are optional (instruction syntax as in LLVM IR, `add i8 %x, %y`,
//! `zext i8 %x to i16`), inferred, and every assignment of the widths left open is checked.

use std::collections::HashMap;

use super::ir::{Block, Body, Node, Term, Transform};
use super::lex::{Cursor, SyntaxError, Tok, lex, strip_comment};
use super::parse::Ctx;

#[derive(PartialEq, Eq)]
enum Part {
    Head,
    Source,
    Target,
}

struct Pending {
    t: Transform,
    part: Part,
    src_names: HashMap<String, super::ir::NodeId>,
    names: HashMap<String, super::ir::NodeId>,
    syms: HashMap<String, super::ir::NodeId>,
    root_name: Option<String>,
    start: usize,
}

impl Pending {
    fn new(name: String, start: usize) -> Self {
        let mut t = Transform::new(name);
        t.src.blocks.push(Block {
            name: "entry".into(),
            insts: Vec::new(),
            term: Term::None,
        });
        t.tgt.blocks.push(Block {
            name: "entry".into(),
            insts: Vec::new(),
            term: Term::None,
        });
        t.src.returns_value = true;
        t.tgt.returns_value = true;
        Pending {
            t,
            part: Part::Head,
            src_names: HashMap::new(),
            names: HashMap::new(),
            syms: HashMap::new(),
            root_name: None,
            start,
        }
    }

    fn ctx(&mut self) -> Ctx<'_> {
        Ctx {
            t: &mut self.t,
            names: core::mem::take(&mut self.names),
            syms: core::mem::take(&mut self.syms),
            alive: true,
            blocks: HashMap::new(),
        }
    }

    fn finish(mut self) -> Result<Transform, SyntaxError> {
        let err = |m: String| SyntaxError {
            line: self.start,
            message: m,
        };
        if self.part != Part::Target {
            return Err(err(format!("`{}` has no `=>`", self.t.name)));
        }
        let Some(root) = self.root_name.clone() else {
            return Err(err(format!("`{}` has no source instruction", self.t.name)));
        };
        let src_root = self.src_names[&root];
        let tgt_root = match self.names.get(&root) {
            Some(&n) if n != src_root => n,
            _ => {
                return Err(err(format!(
                    "the target of `{}` does not define %{root}",
                    self.t.name
                )));
            }
        };
        self.t.src.root = Some(src_root);
        self.t.tgt.root = Some(tgt_root);
        Ok(self.t)
    }
}

/// Parses every transformation of a file in the transformation syntax.
pub fn parse_transforms(text: &str) -> Result<Vec<Transform>, SyntaxError> {
    let mut out = Vec::new();
    let mut cur: Option<Pending> = None;
    for (k, raw) in text.lines().enumerate() {
        let n = k + 1;
        let line = strip_comment(raw).trim();
        if line.is_empty() {
            // A blank line after a target ends the transformation.
            if cur
                .as_ref()
                .is_some_and(|p| p.part == Part::Target && !p.t.tgt.blocks[0].insts.is_empty())
            {
                out.push(cur.take().expect("checked").finish()?);
            }
            continue;
        }
        if let Some(name) = line.strip_prefix("Name:") {
            if let Some(p) = cur.take() {
                out.push(p.finish()?);
            }
            cur = Some(Pending::new(name.trim().to_string(), n));
            continue;
        }
        let p =
            cur.get_or_insert_with(|| Pending::new(format!("transformation {}", out.len() + 1), n));
        if let Some(pre) = line.strip_prefix("Pre:") {
            if p.part != Part::Head {
                return Err(SyntaxError {
                    line: n,
                    message: "`Pre:` comes before the source".into(),
                });
            }
            let toks = lex(pre, n)?;
            let mut c = Cursor::new(&toks, n);
            let mut cx = p.ctx();
            let e = cx.cexpr(&mut c, 0)?;
            if !c.at_end() {
                return c.err("unexpected text after the precondition");
            }
            let (names, syms) = (cx.names, cx.syms);
            p.names = names;
            p.syms = syms;
            if !matches!(p.t.node(e), Node::Pred(..)) {
                return Err(SyntaxError {
                    line: n,
                    message: "the precondition is not a condition".into(),
                });
            }
            p.t.pre = Some(e);
            continue;
        }
        if line == "=>" {
            if p.part != Part::Source {
                return Err(SyntaxError {
                    line: n,
                    message: "`=>` without source instructions".into(),
                });
            }
            p.part = Part::Target;
            p.src_names = p.names.clone();
            continue;
        }
        let toks = lex(line, n)?;
        if p.part == Part::Head {
            p.part = Part::Source;
        }
        let mut c = Cursor::new(&toks, n);
        let name = match (c.peek(), c.peek_at(1)) {
            (Some(Tok::Local(r)), Some(Tok::P("="))) => {
                let r = r.clone();
                c.pos += 2;
                r
            }
            _ => String::new(),
        };
        let mut cx = p.ctx();
        let (inst, ty) = cx.inst(&mut c, &name)?;
        if !c.at_end() {
            return c.err("unexpected text after the instruction");
        }
        let id = cx.t.push(Node::Inst(inst), ty);
        let (mut names, syms) = (cx.names, cx.syms);
        if !name.is_empty() {
            if p.part == Part::Source
                && names
                    .get(&name)
                    .is_some_and(|&old| matches!(p.t.node(old), Node::Inst(_)))
            {
                return Err(SyntaxError {
                    line: n,
                    message: format!("%{name} is defined twice in the source"),
                });
            }
            names.insert(name.clone(), id);
            if p.part == Part::Source {
                p.root_name = Some(name);
            }
        }
        p.names = names;
        p.syms = syms;
        let body: &mut Body = if p.part == Part::Source {
            &mut p.t.src
        } else {
            &mut p.t.tgt
        };
        body.blocks[0].insts.push(id);
    }
    if let Some(p) = cur.take() {
        out.push(p.finish()?);
    }
    Ok(out)
}

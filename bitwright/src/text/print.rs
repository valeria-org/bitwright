//! A bounded, DAG-aware printer for the expression syntax.
//!
//! Shared non-leaf subterms are bound with `let %k = …;`, and so are subterms whose inline
//! nesting would exceed [`PrintOptions::max_depth`], so the output never walks a DAG as a tree
//! and always parses back (within the parser's nesting limit) to the same expression. Output
//! is bounded by node and character budgets; a truncated print ends with `…`.

use core::fmt::{self, Write as _};

use crate::BitVec;
use crate::expr::{Context, Expr, OpCode};
use crate::hash::IdMap;

/// Options for [`Context::display_with`].
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct PrintOptions {
    /// Stop after emitting this many nodes.
    pub max_nodes: usize,
    /// Stop after about this many characters.
    pub max_chars: usize,
    /// Bind shared subterms with `let` (otherwise they are repeated, within the budgets).
    pub lets: bool,
    /// Annotate every symbol's first occurrence with its width (`x:64`), so the text parses
    /// into a context that does not know the symbols.
    pub symbol_widths: bool,
    /// The deepest inline nesting before a subterm is bound with `let`.
    pub max_depth: u32,
}

impl Default for PrintOptions {
    fn default() -> Self {
        PrintOptions {
            max_nodes: 10_000,
            max_chars: 1 << 20,
            lets: true,
            symbol_widths: false,
            max_depth: 48,
        }
    }
}

impl PrintOptions {
    /// Sets [`max_nodes`](Self::max_nodes).
    pub fn with_max_nodes(mut self, n: usize) -> Self {
        self.max_nodes = n;
        self
    }

    /// Sets [`max_chars`](Self::max_chars).
    pub fn with_max_chars(mut self, n: usize) -> Self {
        self.max_chars = n;
        self
    }

    /// Sets [`lets`](Self::lets).
    pub fn with_lets(mut self, yes: bool) -> Self {
        self.lets = yes;
        self
    }

    /// Sets [`symbol_widths`](Self::symbol_widths).
    pub fn with_symbol_widths(mut self, yes: bool) -> Self {
        self.symbol_widths = yes;
        self
    }
}

/// A printable expression; see [`Context::display`].
#[derive(Debug)]
pub struct Display<'a> {
    cx: &'a Context,
    root: Result<u32, crate::Error>,
    opts: PrintOptions,
}

impl Context {
    /// The expression in the text syntax, with the default [`PrintOptions`].
    pub fn display(&self, e: Expr) -> Display<'_> {
        self.display_with(e, PrintOptions::default())
    }

    /// The expression in the text syntax.
    pub fn display_with(&self, e: Expr, opts: PrintOptions) -> Display<'_> {
        Display {
            cx: self,
            root: self.id(e),
            opts,
        }
    }
}

// Precedence levels; higher binds tighter.
const P_CMP: u8 = 1;
const P_OR: u8 = 2;
const P_XOR: u8 = 3;
const P_AND: u8 = 4;
const P_SHIFT: u8 = 5;
const P_SUM: u8 = 6;
const P_PROD: u8 = 7;
const P_UNARY: u8 = 8;
const P_ATOM: u8 = 9;

struct Printer<'a> {
    cx: &'a Context,
    opts: &'a PrintOptions,
    out: String,
    names: IdMap<u32, u32>,
    seen_symbols: IdMap<u32, ()>,
    emitted: usize,
    truncated: bool,
}

/// One step of the iterative inline emitter.
enum Step {
    Node(u32, u8, LitCtx),
    Text(&'static str),
    Owned(String),
}

/// Whether a literal at this position needs a width annotation.
#[derive(Copy, Clone, PartialEq, Eq)]
enum LitCtx {
    Inferred,
    Annotate,
}

impl Printer<'_> {
    fn budget_left(&mut self) -> bool {
        if self.emitted >= self.opts.max_nodes || self.out.len() >= self.opts.max_chars {
            self.truncated = true;
            return false;
        }
        true
    }

    fn constant(&mut self, v: &BitVec, ctx: LitCtx) {
        let w = v.width().bits();
        let s = if w == 1 {
            format!("{}", u8::from(!v.is_zero()))
        } else if let Some(neg) = v.to_i128().filter(|&s| (-65_536..0).contains(&s)) {
            format!("-{}", -neg)
        } else if let Some(u) = v.to_u64().filter(|&u| u < 65_536) {
            format!("{u}")
        } else {
            let t = v.to_string();
            t[..t.rfind(':').unwrap_or(t.len())].to_string()
        };
        self.out.push_str(&s);
        if ctx == LitCtx::Annotate {
            let _ = write!(self.out, ":{w}");
        }
    }

    /// Emits node `i` inline (bound subterms become their `%k` names). Iterative.
    fn inline(&mut self, root: u32, root_ctx: LitCtx) {
        let mut stack = vec![Step::Node(root, 0, root_ctx)];
        let mut first = true;
        while let Some(step) = stack.pop() {
            let (i, min_prec, ctx) = match step {
                Step::Text(s) => {
                    self.out.push_str(s);
                    continue;
                }
                Step::Owned(s) => {
                    self.out.push_str(&s);
                    continue;
                }
                Step::Node(i, p, c) => (i, p, c),
            };
            if !first && let Some(&k) = self.names.get(&i) {
                let _ = write!(self.out, "%{k}");
                continue;
            }
            first = false;
            if !self.budget_left() {
                self.out.push('…');
                continue;
            }
            self.emitted += 1;
            let cx = self.cx;
            let n = cx.node(i);
            // (text before, children with (min precedence, literal ctx) and separators, text after, own precedence)
            let mut parts: Vec<Step> = Vec::new();
            let prec: u8;
            let lit = |j: u32| cx.node(j).op == OpCode::Const;
            match n.op {
                OpCode::Const => {
                    let v = cx.const_val(i).unwrap_or(BitVec::zero(crate::Width::W1));
                    let negative_form = v.width().bits() > 1
                        && v.to_i128().is_some_and(|s| (-65_536..0).contains(&s));
                    let p = if negative_form { P_UNARY } else { P_ATOM };
                    if p < min_prec {
                        self.out.push('(');
                        self.constant(&v, ctx);
                        self.out.push(')');
                    } else {
                        self.constant(&v, ctx);
                    }
                    continue;
                }
                OpCode::Sym => {
                    let entry = &cx.symbols.entries[n.a as usize];
                    let _ = write!(self.out, "{}", entry.key);
                    if self.opts.symbol_widths && self.seen_symbols.insert(i, ()).is_none() {
                        let _ = write!(self.out, ":{}", entry.width);
                    }
                    continue;
                }
                OpCode::Not | OpCode::Neg => {
                    prec = P_UNARY;
                    parts.push(Step::Text(if n.op == OpCode::Not { "~" } else { "-" }));
                    parts.push(Step::Node(n.a, P_UNARY, LitCtx::Inferred));
                }
                OpCode::Add
                    if lit(n.b)
                        && cx
                            .const_val(n.b)
                            .and_then(|v| v.to_i128())
                            .is_some_and(|s| (-65_536..0).contains(&s))
                        && n.width > 1 =>
                {
                    // x + (-c) prints as x - c.
                    prec = P_SUM;
                    let c = cx.const_val(n.b).and_then(|v| v.to_i128()).unwrap_or(0);
                    parts.push(Step::Node(n.a, P_SUM, LitCtx::Inferred));
                    parts.push(Step::Owned(format!(" - {}", -c)));
                }
                op if infix(op).is_some() => {
                    let (sym, p) = infix(op).unwrap_or(("?", P_ATOM));
                    prec = p;
                    let (l, r) = if op.as_cmp().is_some() {
                        (p + 1, p + 1)
                    } else {
                        (p, p + 1)
                    };
                    parts.push(Step::Node(n.a, l, LitCtx::Inferred));
                    parts.push(Step::Text(sym));
                    parts.push(Step::Node(n.b, r, LitCtx::Inferred));
                }
                OpCode::Zext | OpCode::Sext => {
                    prec = P_ATOM;
                    let f = if n.op == OpCode::Zext { "zext" } else { "sext" };
                    parts.push(Step::Owned(format!("{f}<{}>(", n.width)));
                    parts.push(Step::Node(n.a, 0, LitCtx::Annotate));
                    parts.push(Step::Text(")"));
                }
                OpCode::Extract => {
                    prec = P_ATOM;
                    if n.b == 0 {
                        parts.push(Step::Owned(format!("trunc<{}>(", n.width)));
                    } else {
                        parts.push(Step::Owned(format!("extract<{}, {}>(", n.b, n.width)));
                    }
                    parts.push(Step::Node(n.a, 0, LitCtx::Annotate));
                    parts.push(Step::Text(")"));
                }
                OpCode::Concat => {
                    prec = P_ATOM;
                    parts.push(Step::Text("concat("));
                    parts.push(Step::Node(n.a, 0, LitCtx::Annotate));
                    parts.push(Step::Text(", "));
                    parts.push(Step::Node(n.b, 0, LitCtx::Annotate));
                    parts.push(Step::Text(")"));
                }
                OpCode::Select => {
                    prec = P_ATOM;
                    let both_lit = lit(n.b) && lit(n.c);
                    let arm = if both_lit {
                        LitCtx::Annotate
                    } else {
                        LitCtx::Inferred
                    };
                    parts.push(Step::Text("select("));
                    parts.push(Step::Node(n.a, 0, LitCtx::Inferred));
                    parts.push(Step::Text(", "));
                    parts.push(Step::Node(n.b, 0, arm));
                    parts.push(Step::Text(", "));
                    parts.push(Step::Node(n.c, 0, LitCtx::Inferred));
                    parts.push(Step::Text(")"));
                }
                op if op.as_ext().is_some() => {
                    // `@name(args)`, or `@name[k](args)` for output k > 0; literal arguments
                    // carry their widths (nothing else says them).
                    prec = P_ATOM;
                    let (_, k) = op.as_ext().unwrap_or((1, 0));
                    let name = cx
                        .registry
                        .as_deref()
                        .and_then(|r| r.op_at(n.aux))
                        .map_or("?", |o| o.name());
                    parts.push(Step::Owned(if k == 0 {
                        format!("@{name}(")
                    } else {
                        format!("@{name}[{k}](")
                    }));
                    let kids: Vec<u32> = n.children().collect();
                    for (j, c) in kids.iter().enumerate() {
                        if j > 0 {
                            parts.push(Step::Text(", "));
                        }
                        parts.push(Step::Node(*c, 0, LitCtx::Annotate));
                    }
                    parts.push(Step::Text(")"));
                }
                op => {
                    // Function-call forms.
                    prec = P_ATOM;
                    let name = if let Some(u) = op.as_un() {
                        u.name()
                    } else if let Some(b) = op.as_bin() {
                        b.name()
                    } else {
                        "?"
                    };
                    parts.push(Step::Owned(format!("{name}(")));
                    let kids: Vec<u32> = n.children().collect();
                    for (k, c) in kids.iter().enumerate() {
                        if k > 0 {
                            parts.push(Step::Text(", "));
                        }
                        parts.push(Step::Node(*c, 0, LitCtx::Inferred));
                    }
                    parts.push(Step::Text(")"));
                }
            }
            let paren = prec < min_prec;
            if paren {
                stack.push(Step::Text(")"));
            }
            for p in parts.into_iter().rev() {
                stack.push(p);
            }
            if paren {
                stack.push(Step::Text("("));
            }
        }
    }
}

fn infix(op: OpCode) -> Option<(&'static str, u8)> {
    Some(match op {
        OpCode::Add => (" + ", P_SUM),
        OpCode::Sub => (" - ", P_SUM),
        OpCode::Mul => (" * ", P_PROD),
        OpCode::And => (" & ", P_AND),
        OpCode::Or => (" | ", P_OR),
        OpCode::Xor => (" ^ ", P_XOR),
        OpCode::Shl => (" << ", P_SHIFT),
        OpCode::LShr => (" >>u ", P_SHIFT),
        OpCode::AShr => (" >>s ", P_SHIFT),
        OpCode::Eq => (" == ", P_CMP),
        OpCode::Ne => (" != ", P_CMP),
        OpCode::Ult => (" <u ", P_CMP),
        OpCode::Ule => (" <=u ", P_CMP),
        OpCode::Slt => (" <s ", P_CMP),
        OpCode::Sle => (" <=s ", P_CMP),
        _ => return None,
    })
}

impl fmt::Display for Display<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let root = match self.root {
            Ok(r) => r,
            Err(ref e) => return write!(f, "<{e}>"),
        };
        let cx = self.cx;
        // Parser nesting is limited; each inline level can cost two parser levels.
        let max_depth = self.opts.max_depth.clamp(1, 60);
        // Reachable nodes in post-order, and use counts within the printed DAG. The walk is
        // bounded: nothing beyond the node budget can be printed anyway.
        let expand_limit = self.opts.max_nodes.saturating_mul(2).max(16);
        let mut order = Vec::new();
        let mut uses: IdMap<u32, u32> = IdMap::default();
        {
            let mut stack: Vec<(u32, u8)> = vec![(root, 0)];
            uses.insert(root, 0);
            while let Some(top) = stack.last_mut() {
                let (i, k) = *top;
                let n = cx.node(i);
                if (k as usize) < n.op.arity() && uses.len() <= expand_limit {
                    top.1 += 1;
                    let c = [n.a, n.b, n.c][k as usize];
                    let u = uses.entry(c).or_insert(0);
                    *u += 1;
                    if *u == 1 {
                        stack.push((c, 0));
                    }
                } else {
                    stack.pop();
                    order.push(i);
                }
            }
        }
        // Decide `let` bindings: shared non-leaves, and depth breakers.
        let mut bound: Vec<u32> = Vec::new();
        let mut depth: IdMap<u32, u32> = IdMap::default();
        for &i in &order {
            let n = cx.node(i);
            if n.op.arity() == 0 {
                depth.insert(i, 0);
                continue;
            }
            let d = 1 + n
                .children()
                .map(|c| depth.get(&c).copied().unwrap_or(0))
                .max()
                .unwrap_or(0);
            let shared = self.opts.lets && uses[&i] >= 2;
            if i != root && (shared || d > max_depth) {
                bound.push(i);
                depth.insert(i, 0);
            } else {
                depth.insert(i, d);
            }
        }
        let mut p = Printer {
            cx,
            opts: &self.opts,
            out: String::new(),
            names: IdMap::default(),
            seen_symbols: IdMap::default(),
            emitted: 0,
            truncated: false,
        };
        for (k, &i) in bound.iter().enumerate() {
            if p.truncated {
                break;
            }
            let _ = write!(p.out, "let %{k} = ");
            p.inline(i, LitCtx::Inferred);
            p.out.push_str(";\n");
            p.names.insert(i, k as u32);
        }
        if p.truncated {
            p.out.push('…');
        } else {
            p.inline(root, LitCtx::Annotate);
        }
        f.write_str(&p.out)
    }
}

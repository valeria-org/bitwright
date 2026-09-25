//! LLVM IR functions (the subset [`transform`](crate::transform) reads, and `load`, `store`,
//! `getelementptr` over scalar types, `alloca`, `ptrtoint`, `inttoptr`): the returned value,
//! over the parameters, with memory one flat array of bytes (pointers are 64-bit addresses).

use super::{Block, memory};
use crate::memory::Endian;
use crate::transform::encode::{Choices, Enc, Leaves, SRC_CHOICE_KEY};
use crate::transform::ir::{Node, Ty};
use crate::{Context, Error, Width};

/// Reads function `name` of an LLVM IR module (the first one, without a name): its return
/// value as the output `ret`, its stores, over its parameters (symbols of their names).
pub fn llvm(cx: &mut Context, text: &str, name: Option<&str>) -> Result<Block, Error> {
    let syntax = |e: crate::transform::SyntaxError| Error::Unsupported(e.to_string());
    let fns = crate::transform::functions(text).map_err(syntax)?;
    let f = match name {
        Some(n) => fns.iter().find(|f| f.name == n),
        None => fns.first(),
    }
    .ok_or_else(|| Error::Unsupported("no such function in the module".into()))?;
    let t = crate::transform::llvm::single(f).map_err(syntax)?;
    let a = crate::transform::types::typing(&t)
        .and_then(|ty| ty.assignments(&t, &[64], 1))
        .map_err(Error::Unsupported)?;
    let Some(a) = a.first() else {
        return Err(Error::Unsupported("no types for the function".into()));
    };
    let mut inputs = Vec::new();
    let mut leaves = Leaves {
        inputs: Vec::new(),
        consts: Vec::new(),
    };
    for &n in &t.inputs {
        let Node::Input { name, .. } = t.node(n) else {
            continue;
        };
        let bits = match a.types[n as usize] {
            Ty::Int(b) => b,
            Ty::Float(f) => f.width().bits(),
        };
        let s = cx.symbol(name.as_str(), Width::new(bits)?)?;
        inputs.push((name.clone(), s));
        leaves.inputs.push((s, cx.bool(false)?));
    }
    let side = Enc::new(cx, &t, &a.types, &leaves, Choices::Symbols(SRC_CHOICE_KEY))?
        .with_memory(memory(Width::W64, Endian::Little))
        .body(&t.src, false)?;
    let outputs = match side.result {
        Some((v, _)) => vec![("ret".to_string(), v)],
        None => Vec::new(),
    };
    let (memory, version) = side.mem.expect("lifting has memory");
    Ok(Block {
        inputs,
        outputs,
        stores: side.stores,
        exits: Vec::new(),
        next: None,
        memory,
        version,
    })
}

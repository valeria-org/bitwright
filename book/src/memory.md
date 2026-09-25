# Memory

Lifted code reads and writes memory: spills to the stack, fields of a structure, a lookup
table in read-only data. `bitwright::memory` turns loads and stores into the operators
bitwright already has, at construction, so the simplifier, the facts, the prover and SMT-LIB
export see nothing new.

A `Memory` maps addresses of one width to cells of another (bytes, usually), little- or
big-endian for values wider than a cell. Stores make versions; a load reads a version:

- each cell is read through the stores before it, newest first. A store at an equal address
  gives the cell; one at a different address is skipped; one whose address may be either
  becomes a `select` on the equality. Addresses with one base and constant offsets (`sp - 8`,
  `sp - 4`) are decided by their offsets, others by the builder or the facts;
- what no store covers comes from the memory's base: known contents where the address is in a
  region of them (a constant, or a table selected by the offset when the address is not
  constant), and otherwise an unknown cell, the symbol `name.k`. A later read of unknown memory
  at an address that may equal an earlier one selects the earlier cell when they are equal, so
  equal addresses always read equal values however they are written;
- the cells of a load are put together again, and pieces of one stored value become that
  value: a spill reloaded is the spilled value.

```rust
use bitwright::memory::{Endian, Memory};
use bitwright::{BitVec, Context, ParseOptions, SymbolKey, Width};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W64);
// A lookup table at 0x4000 (read-only data), the rest unknown.
let table: Vec<u8> = (0..16u8).map(|i| i.wrapping_mul(13) ^ 0x5a).collect();
let mut mem = Memory::new("mem", Width::W64, Width::W8, Endian::Little).with_bytes(0x4000, &table)?;
let m0 = mem.initial();

// A spill and a reload: the reload is the value.
let (slot, x) = (cx.parse("sp - 8", &o)?, cx.parse("x", &o)?);
let m1 = mem.store(&mut cx, m0, slot, x)?;
let x_again = mem.load(&mut cx, m1, slot, 8)?;
assert_eq!(x_again, x);

// A table lookup at an index the facts show in range, before the spill (after it, the
// lookup would depend on whether the spill hit the table): a table, no unknown memory.
let at = cx.parse("0x4000 + (i & 15)", &o)?;
let entry = mem.load(&mut cx, m0, at, 1)?;
assert!(mem.reads().is_empty());
let env = [(SymbolKey::from("i"), BitVec::from_u64(Width::W64, 3)?)];
assert_eq!(cx.eval(&[entry], &env[..])?[0].to_u64(), Some(u64::from(table[3])));

// A store through a pointer that may alias the slot: the reload depends on it.
let (p, y) = (cx.parse("p", &o)?, cx.parse("y", &ParseOptions::width(Width::W8))?);
let m2 = mem.store(&mut cx, m1, p, y)?;
let low = mem.load(&mut cx, m2, slot, 1)?;
assert_eq!(cx.display(low).to_string(), "select(sp - 8 == p, y, trunc<8>(x))");
# Ok::<(), Box<dyn std::error::Error>>(())
```

The unknown cells are ordinary symbols, so a model of an expression that reads memory is a
model of the memory it read. `Memory::reads` lists each read's address and symbol, and
`Memory::bind` evaluates the addresses in turn to give the symbols their values from a memory
image, for evaluating an expression against a concrete memory.

SMT-LIB arrays import as memories (see [SMT-LIB](smtlib.md)).

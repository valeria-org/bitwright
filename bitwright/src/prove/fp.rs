//! Floating-point operations as circuits (see the module docs of `prove`).

use super::Blaster;
use super::blast::Bits;
use crate::error::Error;

/// The bits of floating-point node `i`.
pub(super) fn blast(b: &mut Blaster<'_>, i: u32) -> Result<Bits, Error> {
    let _ = (&b, i);
    Err(Error::Unsupported(
        "floating point is not blasted yet".into(),
    ))
}

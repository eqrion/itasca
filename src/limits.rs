//! Every numeric bound the validator enforces, in one place.
//!
//! Two kinds live here, and which one a rejection came from matters when
//! reading it. Most are the specification's own bounds, or Wasm 1.0
//! restrictions that later proposals lifted and this validator does not.
//! The implementation caps (`MAX_FUNCTION_BYTES` and friends) are different:
//! a cap only ever rejects, so it cannot make the validator unsound, but it
//! does make it incomplete, which is why the completeness theorem carries it
//! as a hypothesis.

use crate::error::Error;

/// Spec 4.2.8: a memory is at most 2^16 pages, which is 4 GiB.
pub const MAX_MEMORY_PAGES: u32 = 65536;

/// Spec 4.2.7: a table is indexed by a `u32`, so the `u32` range is its bound.
pub const MAX_TABLE_ELEMS: u32 = u32::MAX;

/// Wasm 1.0 has at most one table, counting imports and definitions together.
pub const MAX_TABLES: usize = 1;

/// Wasm 1.0 has at most one memory, counting imports and definitions together.
pub const MAX_MEMORIES: usize = 1;

/// Wasm 1.0 function types return at most one value; multi-value arrived later.
///
/// `opiter` enforces this rather than leaving it to the module validator,
/// because `call` is the one operator whose push count comes from the context
/// rather than from the opcode, and without a bound on it nothing bounds the
/// operand stack, which makes `Vec::push` a live panic site.
pub const MAX_RESULTS: usize = 1;

/// An implementation cap on function body size.
///
/// This is what bounds everything else in `validate_body`: `pos` cannot
/// exceed the body length, and each iteration advances `pos` by at least one
/// byte while growing the stacks by at most one entry, so no push or cursor
/// increment can overflow.
pub const MAX_FUNCTION_BYTES: usize = 7_654_321;

/// An implementation cap on module size. Every position the module decoder
/// computes is below this, which rules out an overflowing cursor.
pub const MAX_MODULE_BYTES: usize = 1_073_741_824;

/// An implementation cap on the number of locals a function may declare. A
/// local declaration is a count and a type, so without a cap two bytes of
/// input could ask for four billion locals.
pub const MAX_LOCALS: usize = 50_000;

/// A minimum and optional maximum size, for a table or a memory.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct Limits {
    pub min: u32,
    pub max: Option<u32>,
}

/// Spec 3.2.1: the minimum is within range, and so is the maximum if there is
/// one, and the maximum is not below the minimum.
pub fn validate_limits(limits: &Limits, range: u32) -> Result<(), Error> {
    if limits.min > range {
        return Err(Error::LimitsOutOfRange);
    }
    if let Some(max) = limits.max {
        if max > range {
            return Err(Error::LimitsOutOfRange);
        }
        if limits.min > max {
            return Err(Error::LimitsOutOfRange);
        }
    }
    Ok(())
}

//! Numeric bounds the validator enforces, in one place.
//!
//! Most are bounds from the spec itself, or Wasm 1.0 restrictions that later
//! proposals lifted and this validator still enforces. The `MAX_*_BYTES` and
//! `MAX_LOCALS` constants are different: implementation caps, chosen so the
//! position and stack-depth arithmetic elsewhere in the crate can't overflow.
//! A module that only exceeds one of these caps is otherwise valid but still
//! gets rejected.

use crate::error::Error;
use crate::types::Limits;

// A memory is at most 2^16 pages, i.e. 4 GiB (spec 4.2.8).
pub const MAX_MEMORY_PAGES: u32 = 65536;

// A table is indexed by a `u32`, so this is its bound (spec 4.2.7).
pub const MAX_TABLE_ELEMS: u32 = u32::MAX;

// Wasm 1.0 has at most one table, counting imports and definitions together.
pub const MAX_TABLES: usize = 1;

// Wasm 1.0 has at most one memory, counting imports and definitions together.
pub const MAX_MEMORIES: usize = 1;

// Wasm 1.0 function types return at most one value; multi-value arrived
// later. `code` enforces this bound itself because `call`'s push count comes
// from the callee's type rather than from the opcode, so nothing else bounds
// the operand stack.
pub const MAX_RESULTS: usize = 1;

// Implementation cap on function body size, chosen so position tracking in
// `validate_body` can't overflow.
pub const MAX_FUNCTION_BYTES: usize = 7_654_321;

// Implementation cap on module size, chosen so position tracking in the
// module decoder can't overflow.
pub const MAX_MODULE_BYTES: usize = 1_073_741_824;

// Most bytes an LEB128 `u32` can take before `read_u32_leb` gives up. Not a
// cap the validator enforces on input; it's what a consumer needs to know to
// size a framing read.
pub const MAX_LEB_BYTES: usize = 5;

// Most bytes the code section's header can take: an id byte, the section
// size, and the entry count.
pub const MAX_CODE_HEADER_BYTES: usize = 1 + 2 * MAX_LEB_BYTES;

// Implementation cap on the number of locals a function may declare. A local
// declaration is a count and a type, so without a cap two bytes of input
// could ask for four billion locals.
pub const MAX_LOCALS: usize = 50_000;

/// Checks that `limits.min` is at most `range`, that `limits.max` is too if
/// present, and that `limits.max` is not below `limits.min` (spec 3.2.1).
pub(crate) fn validate_limits(limits: &Limits, range: u32) -> Result<(), Error> {
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

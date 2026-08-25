//! Formally verified WebAssembly 1.0 module validator.
//!
//! ```
//! # let wasm_bytes = b"\x00asm\x01\x00\x00\x00";
//! let module = itasca::validate_module(wasm_bytes)?;
//! # Ok::<(), itasca::error::Error>(())
//! ```
//!
//! Decoding and validation are one streaming pass, split into three parts:
//! the environment, the code section, and the tail. `module` exposes all
//! three entry points for a caller that wants to drive them itself, which is
//! what a compiler consumer does.
//!
//! A compiler gets at function bodies through [`code::validate_body_with`]
//! and an [`OpVisitor`]: validation calls one hook per operator, with its
//! immediates already decoded and checked. Every hook defaults to doing
//! nothing, so a consumer only pays for the ones it implements.
//!
//! [`import_types`] and [`export_types`] read a validated module's
//! environment and report what it imports and what it exports, which is
//! what an embedder needs to link it.
//!
//! # Trust boundary
//!
//! [`validate_module`] and [`module::validate_module_with`] ask nothing of
//! the caller: they take a `&[u8]` and accept or reject it.
//!
//! The decomposed entry points -- [`module::validate_env`],
//! [`module::validate_code`], [`module::validate_code_entry`],
//! [`module::validate_tail`], and their `_with` forms -- expect two things
//! instead:
//!
//! - `data` is at most `limits::MAX_MODULE_BYTES` long. `validate_module`
//!   checks this once up front and then calls the parts, so a caller driving
//!   the parts directly is responsible for the check itself.
//! - `env`, and for the later parts the position reached so far, came from
//!   running the earlier parts on this same `data`. A hand-built [`module::Env`]
//!   or an out-of-order call is not something these functions are validated
//!   against.
//!
//! Hooks (see [`OpVisitor`] and [`module::CodeVisitor`]) are ordinary,
//! unverified code. A hook must always return, and the only way it affects
//! the outcome is by returning `Err`: that can turn an otherwise-valid module
//! into a rejection, but a hook can never turn a rejection into an acceptance.
//! [`module::CodeVisitor::on_code_entry`] is the one hook that can also skip
//! validating a code entry itself -- overriding it means taking over that
//! validation.

#![cfg_attr(not(feature = "std"), no_std)]
// Aeneas requires explicit Vec::new() + push() instead of vec![] macro
#![allow(clippy::vec_init_then_push)]

extern crate alloc;

pub mod code;
pub mod error;
pub mod module;
pub mod types;

/// Numeric bounds the validator enforces. Private: a consumer has no use
/// for the bounds themselves, only for the fact that validation enforces them.
mod limits;

/// Byte-level reads over `(data, pos)`. Internal: everything else in this
/// crate is built on top of these rather than around them.
mod reader;

pub use code::*;
pub use error::*;
pub use module::*;
pub use types::*;

//! Formally verified WebAssembly 1.0 module validator.
//!
//! ```
//! # let wasm_bytes = b"\x00asm\x01\x00\x00\x00";
//! let module = itasca::validate_module(wasm_bytes)?;
//! # Ok::<(), itasca::error::Error>(())
//! ```
//!
//! Decoding and validation are one streaming pass, split into three parts:
//! the environment, the code section, and the tail. `module` has the three
//! entry points if you want to drive them yourself, which is what a compiler
//! consumer does.
//!
//! A compiler gets at the function bodies through [`opiter::validate_body_with`]
//! and an [`OpVisitor`]: the loop stays here, where the proofs are, and calls
//! one hook per validated operator with its immediates already decoded and
//! checked. Every hook defaults to doing nothing, and monomorphisation erases
//! the ones a consumer does not write.
//!
//! [`import_types`] and [`export_types`] read the validated module's
//! environment and give back what it asks for and what it provides, which is
//! what an embedder needs in order to link it.
//!
//! # What is exported, and what it is trusted for
//!
//! Two kinds of thing: verified validation routines, and the decoded data they
//! hand back. Every routine's documentation names the theorems that hold of it
//! and the conditions they carry. The one exception is
//! [`opiter::validate_body_with`], which is the raw entry point below the code
//! section's framing: it stays public because the `validate_body_*` theorems
//! are about it, and its preconditions are written out there.
//!
//! [`validate_module`] and [`module::validate_module_with`] have no
//! preconditions at all: they take a `&[u8]` and either accept it or do not,
//! and `validate_module_no_panic` says no input makes either crash or hang.
//! The decomposed entry points -- [`module::decode_env`],
//! [`module::validate_code`], [`module::validate_code_entry`],
//! [`module::decode_tail`] and their `_with` forms -- take a position and an
//! environment, and there the theorems are conditional. Two conditions run
//! through all of them, and both are the caller's:
//!
//! - **`data` is at most [`limits::MAX_MODULE_BYTES`] long.** Every no-panic
//!   and completeness result about a part carries `dlen data <= module_bytes`.
//!   `validate_module` checks it once and then calls the parts, which is why
//!   it has no hypothesis; a caller that calls the parts itself owes the check.
//!   In practice the bound guards `usize` arithmetic in the Coq model rather
//!   than anything a 64-bit host can reach, but it is a hypothesis and not a
//!   remark.
//! - **`env` came out of [`module::decode_env`] on this same `data`, and each
//!   position came out of the part before it.** The soundness results are
//!   stated relative to the environment they were handed, so a hand-built
//!   [`env::Env`] gets a true theorem about a module nobody has. The no-panic
//!   results additionally need `env_small`, which is the postcondition
//!   `decode_env` establishes and nothing else does.
//!
//! Compose the three and `Module_Driven.validate_module_of_parts` says the run
//! is the run [`validate_module`] would have made, so every result about it --
//! `validate_module_repr`, `validate_module_typed`,
//! `validate_module_typechecked` -- holds of a decomposed consumer without
//! being restated.
//!
//! Hooks are unverified code and carry two obligations, named in Coq and
//! repeated on each trait here: `hooks_total` (a hook must return) and
//! `hooks_accept` (it must return `Ok` for validation to finish). Neither can
//! turn a rejection into an acceptance. [`module::CodeVisitor`] has a third,
//! `code_hooks_validate`, because overriding its `on_code_entry` means taking
//! on that entry's validation.

#![cfg_attr(not(feature = "std"), no_std)]
// Aeneas requires explicit Vec::new() + push() instead of vec![] macro
#![allow(clippy::vec_init_then_push)]

extern crate alloc;

pub mod env;
pub mod error;
pub mod limits;
pub mod module;
pub mod opiter;
pub mod types;
pub mod visit;

/// Byte-level reads over `(data, pos)`. Internal: nothing here is a
/// validation routine, and a decoder hand-rolled around these is exactly the
/// code no theorem covers.
mod reader;

pub use module::{export_types, import_types, validate_module, ValidatedModule};
pub use error::VisitError;
pub use visit::{NopVisitor, OpVisitor, VisitResult};
pub use types::ExternType;

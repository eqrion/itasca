//! Formally verified WebAssembly 1.0 module validator.
//!
//! ```
//! # let wasm_bytes = b"\x00asm\x01\x00\x00\x00";
//! let module = itasca::validate_module(wasm_bytes)?;
//! # Ok::<(), itasca::error::Error>(())
//! ```
//!
//! [`validate_module`] supplies a synchronous source and worker to
//! [`stream::validate_streaming`], the sole module driver. Streaming consumers
//! provide coherent environment, code, and tail regions and schedule the issued
//! batches. The driver accepts only after every issued batch has validated and
//! the regions together encode a valid Wasm 1.0 module.
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
//! [`validate_module`] takes arbitrary bytes with no caller preconditions.
//! Its Lean contracts prove ordinary return, acceptance soundness, and acceptance
//! of independently typed Wasm 1.0 binaries within the implementation limits,
//! including exact returned declarations, data, and external-type metadata.
//!
//! [`stream::validate_streaming`] has explicit source-coherence and batch-
//! provenance obligations; its totality contract instead requires returning
//! callbacks. Source availability and an accepting worker/scheduler policy give
//! completeness. See [`stream`] for storage and worker-lifetime obligations.
//!
//! [`module::validate_env`], [`module::validate_code_entry`], and
//! [`module::validate_tail`] share the same component implementations used by the
//! driver. Their separate contracts do not certify a whole module. Entry and
//! tail callers must use the environment decoded for that logical module and
//! satisfy the component's documented bounds and byte-position requirements.
//!
//! [`OpVisitor`] and [`module::ModuleVisitor`] hooks are ordinary embedding code.
//! Returning an error can reject an otherwise-valid input; successful hooks
//! cannot bypass entry/body validation. Returning hooks are needed for totality,
//! and accepting hooks for completeness. Workers advance issued batches through
//! [`stream::CodeBatch::validate_func`], which retains the validation result.

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

pub mod stream;

//! Formally verified WebAssembly 1.0 module validator.
//!
//! ```
//! # let wasm_bytes = b"\x00asm\x01\x00\x00\x00";
//! let module = veriwasm::validate_module(wasm_bytes)?;
//! # Ok::<(), veriwasm::error::Error>(())
//! ```
//!
//! Decoding and validation are one streaming pass, split into three parts:
//! the environment, the code section, and the tail. `module` has the three
//! entry points if you want to drive them yourself, which is what a compiler
//! consumer does.
//!
//! [`import_types`] and [`export_types`] read the validated module's
//! environment and give back what it asks for and what it provides, which is
//! what an embedder needs in order to link it.

#![cfg_attr(not(feature = "std"), no_std)]
// Aeneas requires explicit Vec::new() + push() instead of vec![] macro
#![allow(clippy::vec_init_then_push)]

extern crate alloc;

pub mod env;
pub mod error;
pub mod limits;
pub mod module;
pub mod opiter;
pub mod reader;
pub mod types;

pub use module::{export_types, import_types, validate_module, ValidatedModule};
pub use types::ExternType;

//! WebAssembly validation for the Wasm 1.0 and multi-value profiles.
//!
//! [`validate_module`] validates a complete byte slice and returns read-only
//! module metadata. It requires no caller preconditions. Both profiles have
//! Lean proofs of termination, acceptance soundness, and completeness within
//! the implementation limits, assuming successful allocation.
//!
//! ```
//! let bytes = b"\x00asm\x01\x00\x00\x00";
//! let module = itasca::validate_module(bytes, itasca::ValidationProfile::Wasm1)?;
//! let imports = itasca::import_types(module.env())?;
//! # Ok::<(), itasca::Error>(())
//! ```
//!
//! [`validate_streaming`] supports separate input regions, parallel workers,
//! and compiler callbacks. Its guarantees require coherent source bytes and
//! workers that preserve issued batch identities. Callbacks must return for
//! termination and accept for completeness. Only a successful driver result
//! certifies the complete module.
//!
//! [`OpVisitor`] observes decoded operators during batch validation.
//! [`ModuleVisitor`] observes custom sections. Callback errors can reject valid
//! input; callbacks cannot bypass validation. See [`validate_streaming`] for
//! source, worker, and storage obligations.

#![cfg_attr(not(feature = "std"), no_std)]
// Aeneas requires explicit Vec::new() + push() instead of vec![] macro
#![allow(clippy::vec_init_then_push)]

extern crate alloc;

mod code;
mod error;
mod module;
mod signature;
mod types;

/// Specification bounds and implementation resource limits.
mod limits;

/// Shared byte readers with explicit cursor arguments.
mod reader;

pub use code::{
    Context, Ctrl, EmptyOpVisitor, LabelKind, MemArg, OpIterState, OpVisitor, StackType,
    VisitResult,
};
pub use error::{Error, OpError, VisitError};
pub use module::{
    export_types, import_types, validate_module, Data, Element, Env, Export, ExportDesc, Global,
    Import, ImportDesc, Module, ModuleVisitor, Tail,
};
pub use signature::{BlockType, ResultType, TypePart};
pub use stream::{
    validate_streaming, CodeBatch, CodeEntry, Config, Region, Result, Source, StreamingVisitor,
};
pub use types::{
    ConstExpr, CustomSection, ElemType, ExternType, FuncType, GlobalType, Limits, MemType, Mut,
    TableType, ValueType,
};

mod stream;

/// The language profile used for module and function validation.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum ValidationProfile {
    /// WebAssembly 1.0, including its original segment and branch-table rules.
    Wasm1,
    /// Scalar WebAssembly with multi-value functions and indexed block signatures.
    /// Other Wasm 2.0 proposals remain disabled.
    MultiValue,
}

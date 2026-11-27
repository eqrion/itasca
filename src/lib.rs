//! WebAssembly Core 2.0 validation.
//!
//! [`validate_module`] validates a complete byte slice and returns read-only
//! module metadata. It accepts arbitrary input bytes. The Lean proofs for the
//! previous API are being ported to this metadata representation.
//!
//! ```
//! let bytes = b"\x00asm\x01\x00\x00\x00";
//! let module = itasca::validate_module(bytes)?;
//! let imports = module.import_types()?;
//! # Ok::<(), itasca::Error>(())
//! ```
//!
//! [`validate_streaming`] supports separate input regions, parallel workers,
//! and validation callbacks. Its guarantees require coherent source bytes and
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
// Keep extracted namespaces distinct from fields named `module` and `types`.
#[path = "module.rs"]
mod metadata;
mod signature;
#[path = "types.rs"]
mod wasm_types;

/// Specification bounds and implementation resource limits.
mod limits;

/// Shared byte readers with explicit cursor arguments.
mod reader;

pub use code::{
    Context, Ctrl, DefaultOpVisitor, LabelKind, MemArg, OpIterState, OpVisitor, Opcode, StackType,
    VisitResult,
};
pub use error::{Error, OpError, VisitError};
pub use metadata::{
    validate_module, CodeMetadata, Data, DataMode, DefaultModuleVisitor, Element, ElementInit,
    ElementMode, Export, ExportDesc, FuncDesc, Global, Import, ImportKind, MemoryDesc,
    ModuleMetadata, ModuleVisitor, TableDesc,
};
pub use signature::{BlockType, ResultType, TypePart};
pub use stream::{
    validate_streaming, Result, StreamingBatch, StreamingConfig, StreamingEntry, StreamingRegion,
    StreamingSource, StreamingVisitor,
};
pub use wasm_types::{
    ConstExpr, CustomSection, ElemType, ExternType, FuncType, GlobalType, Limits, MemType, Mut,
    TableType, ValueType,
};

mod stream;

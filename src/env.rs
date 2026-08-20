//! The module environment: everything a Wasm binary declares before its code
//! section.
//!
//! A module decodes in three parts, and this is the first: `Env` is built
//! from the sections up to the code section, the code section is validated
//! against it, and the tail is decoded after. The split matters because
//! validating a function body reads the environment and nothing else, which
//! is what lets a consumer validate or compile entries as they stream in.
//! Here that is a fact about the types: `validate_code_entry` takes an
//! `&Env`, and the data segments a module's tail declares are in
//! `module::Tail`, which it cannot see.

use alloc::vec::Vec;

use crate::types::{ConstExpr, FuncType, GlobalType, MemType, TableType};

/// A global this module defines, with its initialiser.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct Global {
    pub gtype: GlobalType,
    pub init: ConstExpr,
}

/// What an import asks for.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum ImportDesc {
    Func(u32),
    Table(TableType),
    Memory(MemType),
    Global(GlobalType),
}

/// An import entry. Names are raw bytes: they are checked for UTF-8 validity
/// (spec 5.2.4) as they are decoded, but `core::str::from_utf8` is outside the
/// Aeneas subset, so nothing here carries a `str`.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone)]
pub struct Import {
    pub module: Vec<u8>,
    pub name: Vec<u8>,
    pub desc: ImportDesc,
}

/// What an export names, as an index into the matching index space.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum ExportDesc {
    Func(u32),
    Table(u32),
    Memory(u32),
    Global(u32),
}

/// An export entry.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone)]
pub struct Export {
    pub name: Vec<u8>,
    pub desc: ExportDesc,
}

/// An element segment: a table, an offset into it, and the functions to write.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone)]
pub struct Element {
    pub table_idx: u32,
    pub offset: ConstExpr,
    pub init: Vec<u32>,
}

/// Everything the binary declares before the code section.
///
/// The accessor half of the interface: every field is what `decode_env` read
/// out of the binary, and reading them is what a compiler builds its metadata
/// from. They are writable too, which the type system cannot help with; an
/// `Env` a caller altered is one no theorem is about.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone)]
pub struct Env {
    /// Section 1. Also the type index space.
    pub types: Vec<FuncType>,
    /// Section 2.
    pub imports: Vec<Import>,
    /// Section 6, the globals this module defines.
    pub globals: Vec<Global>,
    /// Section 7.
    pub exports: Vec<Export>,
    /// Section 9.
    pub elements: Vec<Element>,
    /// Section 8.
    pub start: Option<u32>,
    /// Section 3: one type index per code-section entry, in order. Redundant
    /// with `func_types`, but a consumer wants the index and not just the
    /// type.
    pub func_type_indices: Vec<u32>,

    /// The index spaces of spec 3.1.1: imported entries first, then the ones
    /// this module defines. Body validation is a lookup in these rather than a
    /// walk over the import list.
    pub func_types: Vec<FuncType>,
    pub table_types: Vec<TableType>,
    pub mem_types: Vec<MemType>,
    pub global_types: Vec<GlobalType>,

    /// Where the imported entries end and the defined ones start. Only the
    /// two index spaces something consults the boundary of are tracked:
    /// initialisers may name an imported global and no other, and a consumer
    /// needs to know which functions it has to supply.
    pub num_imported_funcs: usize,
    pub num_imported_globals: usize,
}

impl Env {
    /// The empty environment `decode_env` starts from.
    ///
    /// Public because the crate's own tests build environments to drive
    /// `opiter::validate_body` against, and for no other reason. An `Env` that
    /// did not come out of `decode_env` satisfies none of the conditions the
    /// code-section entry points carry: soundness is stated relative to the
    /// environment handed over, and `env_small`, which their no-panic results
    /// need, is `decode_env`'s postcondition. See the crate documentation.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Env {
        Env {
            types: Vec::new(),
            imports: Vec::new(),
            globals: Vec::new(),
            exports: Vec::new(),
            elements: Vec::new(),
            start: None,
            func_type_indices: Vec::new(),
            func_types: Vec::new(),
            table_types: Vec::new(),
            mem_types: Vec::new(),
            global_types: Vec::new(),
            num_imported_funcs: 0,
            num_imported_globals: 0,
        }
    }
}

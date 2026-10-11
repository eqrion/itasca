//! Scalar, signature, external, and constant-expression metadata.

use alloc::vec::Vec;

/// A scalar WebAssembly value type supported by both profiles.
#[cfg_attr(not(charon), derive(Debug))]
#[derive(Clone, Copy)]
pub enum ValueType {
    I32,
    I64,
    F32,
    F64,
}

impl PartialEq for ValueType {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ValueType::I32, ValueType::I32) => true,
            (ValueType::I64, ValueType::I64) => true,
            (ValueType::F32, ValueType::F32) => true,
            (ValueType::F64, ValueType::F64) => true,
            _ => false,
        }
    }
}

impl Eq for ValueType {}

/// The mutability of a global.
#[cfg_attr(not(charon), derive(Debug))]
#[derive(Clone, Copy)]
pub enum Mut {
    Const,
    Var,
}

impl PartialEq for Mut {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Mut::Const, Mut::Const) => true,
            (Mut::Var, Mut::Var) => true,
            _ => false,
        }
    }
}

impl Eq for Mut {}

/// The parameter and result types of a function.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone)]
pub struct FuncType {
    pub params: Vec<ValueType>,
    pub results: Vec<ValueType>,
}

/// A minimum size and optional maximum size.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct Limits {
    pub min: u32,
    pub max: Option<u32>,
}

/// A memory's size limits in 64 KiB pages.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct MemType {
    pub limits: Limits,
}

/// The element type supported by both profiles.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum ElemType {
    FuncRef,
}

/// A table's element type and size limits.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct TableType {
    pub limits: Limits,
    pub elem: ElemType,
}

/// A global's value type and mutability.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct GlobalType {
    pub mutability: Mut,
    pub valtype: ValueType,
}

/// The resolved type required by an import or provided by an export.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub enum ExternType {
    Func(FuncType),
    Table(TableType),
    Memory(MemType),
    Global(GlobalType),
}

/// A decoded initializer or segment-offset expression.
///
/// Both profiles allow one constant instruction or a read of an immutable
/// imported global.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum ConstExpr {
    I32(i32),
    I64(i64),
    /// The exact `f32` immediate bits, including signed zero and NaN payloads.
    F32(u32),
    /// The exact `f64` immediate bits, including signed zero and NaN payloads.
    F64(u64),
    /// A read of an immutable imported global.
    GlobalGet(u32),
}

/// The name and payload bounds of a custom section.
///
/// Offsets refer to the source region selected by
/// `StreamingVisitor::custom_region`. The validator checks the name's
/// UTF-8 encoding and treats the payload as opaque bytes.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct CustomSection {
    /// The number of UTF-8 name bytes immediately preceding `payload_start`.
    pub name_len: usize,
    /// The offset of the first payload byte after the name.
    pub payload_start: usize,
    /// The exclusive end offset of the payload.
    pub payload_end: usize,
}

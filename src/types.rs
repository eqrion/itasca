//! The value and external types of the WebAssembly 1.0 type system.

use alloc::vec::Vec;

use crate::limits::Limits;

/// A wasm value type.
///
/// There's no variant for the bottom type of an unreachable stack value; that
/// lives in `opiter::StackType::Bot` instead, so it can't leak into a
/// function signature.
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

/// Whether a global is mutable.
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

/// A function signature: its parameter types and result types.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone)]
pub struct FuncType {
    pub params: Vec<ValueType>,
    pub results: Vec<ValueType>,
}

/// A memory type: the limits on its size, in pages.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct MemType {
    pub limits: Limits,
}

/// Element type, always `funcref` in Wasm 1.0.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum ElemType {
    FuncRef,
}

/// A table type: its element type and size limits.
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

/// An external type (spec 3.2.7): what an import asks for, or what an export
/// provides.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub enum ExternType {
    Func(FuncType),
    Table(TableType),
    Memory(MemType),
    Global(GlobalType),
}

/// A constant expression: a global's initialiser, or an element or data
/// segment's offset.
///
/// Wasm 1.0 (spec 3.4.10) allows exactly one instruction here, so this is a
/// decoded value rather than a byte range.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum ConstExpr {
    I32(i32),
    I64(i64),
    /// The immediate's bit pattern, as `reader::read_f32_bits` returns it:
    /// the verified core has no floating-point arithmetic.
    F32(u32),
    F64(u64),
    /// `global.get` of an imported immutable global, the only global in scope
    /// in an initialiser.
    GlobalGet(u32),
}

/// Where a custom section's name and contents are.
///
/// Ranges rather than bytes: a custom section is padding as far as the module
/// a binary denotes is concerned (`Spec_Module.v` reads it as such), so nothing
/// here needs its contents, and a consumer that wants them has the bytes
/// already. Positions index whatever was handed to the decoder that reported
/// it, the same frame as every other position in this interface.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct CustomSection {
    /// The name's length. It ends where the payload starts, so the name is
    /// `[payload_start - name_len, payload_start)`. A length rather than a
    /// start because that is what the decoder has without subtracting, and a
    /// subtraction here would be a panic site in verified code for something
    /// a consumer can do for itself. Checked for UTF-8 validity as it was
    /// read (spec 5.2.4), and not copied out.
    pub name_len: usize,
    /// The bytes after the name: `[payload_start, payload_end)`.
    pub payload_start: usize,
    pub payload_end: usize,
}

//! Slot-based execution of validated WebAssembly modules.
//!
//! The generic compiler, store, and interpreter are extracted to Lean, where
//! `lean/Exec` proves their correctness under explicit platform contracts. The
//! `native` module instantiates them with the standard allocator and IEEE
//! operations and is excluded from extraction.
//!
//! Handles identify objects in exactly one store. Float values preserve bits.

use crate::{FuncType, ValueType};
use alloc::vec::Vec;

mod bytecode;
mod compiler;
mod interp;
#[cfg(not(charon))]
mod native;
mod operators;
mod platform;
mod value;

mod store;
pub use compiler::{
    CompileError, CompileLimits, CompileResource, ControlMap, ExecutableModule, FunctionStats,
};
pub use interp::Execution;
#[cfg(not(charon))]
pub use native::{compile, compile_with_limits};
pub use platform::{FloatOps, HostError, InterruptAction, MemoryBuffer, Platform, VecMemory};

pub use store::{Store, StoreLimits};

macro_rules! address {
    ($name:ident) => {
        /// An opaque address belonging to exactly one store.
        #[derive(Clone, Copy)]
        #[cfg_attr(not(charon), derive(Debug, PartialEq, Eq, Hash))]
        pub struct $name {
            pub(super) store: usize,
            pub(super) index: usize,
        }
    };
}
address!(FuncAddr);
address!(TableAddr);
address!(MemoryAddr);
address!(GlobalAddr);
address!(ExternAddr);
address!(InstanceAddr);

/// A typed Wasm value. Integer and floating-point payloads preserve raw bits.
#[derive(Clone, Copy)]
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub enum Value {
    I32(u32),
    I64(u64),
    F32(u32),
    F64(u64),
    V128(u128),
    FuncRef(Option<FuncAddr>),
    ExternRef(Option<ExternAddr>),
}
impl Value {
    /// Returns this value's WebAssembly type.
    pub fn value_type(self) -> ValueType {
        match self {
            Self::I32(_) => ValueType::I32,
            Self::I64(_) => ValueType::I64,
            Self::F32(_) => ValueType::F32,
            Self::F64(_) => ValueType::F64,
            Self::V128(_) => ValueType::V128,
            Self::FuncRef(_) => ValueType::FuncRef,
            Self::ExternRef(_) => ValueType::ExternRef,
        }
    }
    pub(super) fn zero(t: ValueType) -> Self {
        match t {
            ValueType::I32 => Self::I32(0),
            ValueType::I64 => Self::I64(0),
            ValueType::F32 => Self::F32(0),
            ValueType::F64 => Self::F64(0),
            ValueType::V128 => Self::V128(0),
            ValueType::FuncRef => Self::FuncRef(None),
            ValueType::ExternRef => Self::ExternRef(None),
        }
    }
    pub(super) fn i32(self) -> Result<u32, ExecError> {
        match self {
            Self::I32(v) => Ok(v),
            _ => Err(ExecError::Internal),
        }
    }
}

/// A store object supplied as an import or obtained from an export.
#[derive(Clone, Copy)]
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub enum Extern {
    Func(FuncAddr),
    Table(TableAddr),
    Memory(MemoryAddr),
    Global(GlobalAddr),
}

/// A WebAssembly execution trap, separate from embedding resource limits.
#[derive(Clone, Copy)]
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub enum Trap {
    Unreachable,
    IntegerDivideByZero,
    IntegerOverflow,
    InvalidConversionToInteger,
    MemoryOutOfBounds,
    TableOutOfBounds,
    UninitializedElement,
    IndirectCallTypeMismatch,
    Host,
}
/// An import resolution or type matching failure.
#[derive(Clone, Copy)]
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub enum LinkError {
    MissingImport,
    IncompatibleImportType,
}
/// The embedding limit that stopped execution or allocation.
#[derive(Clone, Copy)]
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub enum ResourceLimit {
    CallStack,
    Values,
    Allocation,
    Objects,
}
/// An execution, linking, resource, or host-boundary failure.
#[derive(Clone, Copy)]
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub enum ExecError {
    Trap(Trap),
    Link(LinkError),
    Exhausted(ResourceLimit),
    BadArguments,
    WrongStore,
    Terminated,
    /// A violated runtime invariant. Code produced by the compiler never
    /// reaches these checks; they keep the extracted interpreter total.
    Internal,
}
impl From<Trap> for ExecError {
    fn from(t: Trap) -> Self {
        Self::Trap(t)
    }
}
#[cfg(not(charon))]
impl core::fmt::Display for ExecError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}
#[cfg(all(feature = "std", not(charon)))]
impl std::error::Error for ExecError {}

/// Reserves capacity for `n` more elements, reporting failure as allocation exhaustion.
pub(crate) fn reserve<A: platform::Alloc, T>(v: &mut Vec<T>, n: usize) -> Result<(), ExecError> {
    if A::reserve(v, n) {
        Ok(())
    } else {
        Err(ExecError::Exhausted(ResourceLimit::Allocation))
    }
}
/// Removes every element while retaining capacity.
pub(crate) fn clear<T>(values: &mut Vec<T>) {
    while !values.is_empty() {
        values.pop();
    }
}
/// Copies a signature into fallibly reserved storage.
pub(crate) fn copy_type<A: platform::Alloc>(t: &FuncType) -> Result<FuncType, ExecError> {
    let mut params = Vec::new();
    let mut results = Vec::new();
    reserve::<A, _>(&mut params, t.params.len())?;
    reserve::<A, _>(&mut results, t.results.len())?;
    let mut i = 0;
    while i < t.params.len() {
        params.push(t.params[i]);
        i += 1;
    }
    i = 0;
    while i < t.results.len() {
        results.push(t.results[i]);
        i += 1;
    }
    Ok(FuncType { params, results })
}
/// Returns `start..start + len` if it lies within `0..size`, and `trap` otherwise.
pub(crate) fn range(
    start: u64,
    len: u64,
    size: usize,
    trap: Trap,
) -> Result<core::ops::Range<usize>, ExecError> {
    if start > size as u64 || len > size as u64 - start {
        return Err(ExecError::Trap(trap));
    }
    Ok(start as usize..(start + len) as usize)
}

//! A fuel-metered rewriting interpreter for validated WebAssembly modules.
//!
//! Execution is currently tested, not formally verified. This module is excluded
//! from Charon extraction; the validator and its audited dependencies are unchanged.
//! Handles belong to one store, whose objects remain alive until it is dropped.
//! Floating-point values contain IEEE bits, and external references identify
//! embedding-owned objects which must remain valid for the store's lifetime.

use crate::{FuncType, ValueType};
use alloc::vec::Vec;

mod compiler;
mod execution;
mod numeric;
mod store;
pub use compiler::{
    compile, compile_with_limits, CompileError, CompileLimits, CompileResource, ControlMap,
    ExecutableModule, FunctionStats,
};
pub use execution::Execution;
pub use store::{Instantiation, Store, StoreLimits};

macro_rules! address {
    ($name:ident) => {
        /// An opaque address belonging to exactly one store.
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
    pub(super) fn i32(self) -> Result<u32, RuntimeError> {
        match self {
            Self::I32(v) => Ok(v),
            _ => Err(RuntimeError::TypeMismatch),
        }
    }
}

/// A store object supplied as an import or obtained from an export.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Extern {
    Func(FuncAddr),
    Table(TableAddr),
    Memory(MemoryAddr),
    Global(GlobalAddr),
}

/// A WebAssembly execution trap, separate from embedding resource limits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Trap {
    Unreachable,
    IntegerDivideByZero,
    IntegerOverflow,
    InvalidConversionToInteger,
    MemoryOutOfBounds,
    TableOutOfBounds,
    UninitializedElement,
    IndirectCallTypeMismatch,
}
/// An import resolution or type matching failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LinkError {
    MissingImport,
    IncompatibleImportType,
}
/// The embedding limit that stopped execution or allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourceLimit {
    CallStack,
    Values,
    Allocation,
    Objects,
    CostOverflow,
}
/// An execution, linking, resource, or host-boundary failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuntimeError {
    Trap(Trap),
    Link(LinkError),
    Resource(ResourceLimit),
    TypeMismatch,
    WrongStore,
    HostFailure,
    InvalidState,
}
impl From<Trap> for RuntimeError {
    fn from(t: Trap) -> Self {
        Self::Trap(t)
    }
}
impl core::fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}
#[cfg(feature = "std")]
impl std::error::Error for RuntimeError {}

/// A typed host invocation. Completing it requires the originating execution.
#[derive(Debug)]
pub struct HostRequest {
    pub host_id: u64,
    pub arguments: Vec<Value>,
    pub results: Vec<ValueType>,
}

/// A synchronous embedding handler for explicitly yielded host requests.
///
/// A handler may create nested executions using the supplied store. Fuel does
/// not bound callback time; cancellation and host resources belong to the
/// embedding. Returned values are type- and ownership-checked by the execution.
pub trait Host {
    fn call(&mut self, store: &mut Store, request: HostRequest)
        -> Result<Vec<Value>, RuntimeError>;
}
/// The result of running until completion, a host boundary, or fuel suspension.
#[derive(Debug)]
pub enum Outcome {
    Returned(Vec<Value>),
    Suspended,
    NeedsHostCall(HostRequest),
    Failed(RuntimeError),
}

pub(super) fn copy_type(t: &FuncType) -> Result<FuncType, RuntimeError> {
    let mut params = Vec::new();
    let mut results = Vec::new();
    reserve(&mut params, t.params.len())?;
    reserve(&mut results, t.results.len())?;
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
pub(super) fn reserve<T>(v: &mut Vec<T>, n: usize) -> Result<(), RuntimeError> {
    v.try_reserve(n)
        .map_err(|_| RuntimeError::Resource(ResourceLimit::Allocation))
}
pub(super) fn range(
    start: u64,
    len: u64,
    size: usize,
    trap: Trap,
) -> Result<core::ops::Range<usize>, RuntimeError> {
    let end = start.checked_add(len).ok_or(RuntimeError::Trap(trap))?;
    if end > size as u64 {
        return Err(trap.into());
    }
    Ok(start as usize..end as usize)
}

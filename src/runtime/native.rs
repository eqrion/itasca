//! Reviewed native instantiations of the generic runtime.
use super::platform::Alloc;
use super::*;
use crate::{GlobalType, MemType, TableType};
use core::sync::atomic::{AtomicUsize, Ordering};

mod float;
pub(super) use float::NativeFloat;

pub(crate) struct StdAlloc;
impl Alloc for StdAlloc {
    fn reserve<T>(values: &mut Vec<T>, additional: usize) -> bool {
        values.try_reserve(additional).is_ok()
    }
}
static NEXT_STORE: AtomicUsize = AtomicUsize::new(1);
fn next_identity() -> usize {
    let mut id = NEXT_STORE.load(Ordering::Relaxed);
    loop {
        let next = id.checked_add(1).expect("store identity space exhausted");
        match NEXT_STORE.compare_exchange_weak(id, next, Ordering::Relaxed, Ordering::Relaxed) {
            Ok(_) => return id,
            Err(now) => id = now,
        }
    }
}
impl MemoryBuffer for VecMemory {
    fn new_zeroed(len: usize) -> Option<Self> {
        Self::new_zeroed_with::<StdAlloc>(len)
    }
    fn bytes(&self) -> &[u8] {
        self.as_bytes()
    }
    fn bytes_mut(&mut self) -> &mut [u8] {
        self.as_bytes_mut()
    }
    fn grow(&mut self, new_len: usize) -> bool {
        self.grow_with::<StdAlloc>(new_len)
    }
}
impl<M: MemoryBuffer> Default for Store<M> {
    fn default() -> Self {
        Self::new()
    }
}
impl<M: MemoryBuffer> Store<M> {
    /// Creates an empty store with default resource limits.
    pub fn new() -> Self {
        Self::with_limits(StoreLimits::default())
    }
    /// Creates an empty store with explicit resource limits.
    pub fn with_limits(limits: StoreLimits) -> Self {
        Self::with_identity(next_identity(), limits)
    }
    /// Defines a synchronous host function with its declared type.
    pub fn define_host(&mut self, ty: FuncType, id: u64) -> Result<FuncAddr, ExecError> {
        self.define_host_with::<StdAlloc>(ty, id)
    }
    /// Defines an embedding-owned reference identity.
    pub fn define_extern(&mut self, id: u64) -> Result<ExternAddr, ExecError> {
        self.define_extern_with::<StdAlloc>(id)
    }
    /// Defines memory backed by exactly its declared initial number of pages.
    pub fn define_memory(&mut self, ty: MemType, buf: M) -> Result<MemoryAddr, ExecError> {
        self.define_memory_with::<StdAlloc>(ty, buf)
    }
    /// Defines a table filled with null references.
    pub fn define_table(&mut self, ty: TableType) -> Result<TableAddr, ExecError> {
        self.define_table_with::<StdAlloc>(ty)
    }
    /// Defines a global with a typed, store-owned initial value.
    pub fn define_global(&mut self, ty: GlobalType, value: Value) -> Result<GlobalAddr, ExecError> {
        self.define_global_with::<StdAlloc>(ty, value)
    }
    /// Links, initializes segments, and synchronously executes the start function.
    ///
    /// Link errors and Wasm 1.0 segment bounds errors leave the store unchanged.
    /// Wasm 2.0 traps preserve completed segment writes and allocated objects.
    pub fn instantiate<P: Platform<M>>(
        &mut self,
        module: ExecutableModule,
        imports: &[Extern],
        platform: &mut P,
    ) -> Result<InstanceAddr, ExecError> {
        self.instantiate_with::<P, NativeFloat, StdAlloc>(module, imports, platform)
    }
    /// Grows a memory, returning its previous page count or `u32::MAX` on failure.
    pub fn grow_memory(&mut self, addr: MemoryAddr, delta: u32) -> Result<u32, ExecError> {
        self.grow_memory_with(addr, delta)
    }
    /// Grows a table, returning its previous length or `u32::MAX` on failure.
    pub fn grow_table(
        &mut self,
        addr: TableAddr,
        delta: u32,
        value: Value,
    ) -> Result<u32, ExecError> {
        self.grow_table_with::<StdAlloc>(addr, delta, value)
    }
}
impl Execution {
    /// Invokes a function synchronously, replacing `results` on success.
    ///
    /// Host result slots are initialized to the zero value of their declared
    /// type. Hooks may reenter Wasm through a separate execution. After argument
    /// validation, invocation clears earlier frames and retains capacity for reuse.
    pub fn invoke<M: MemoryBuffer, P: Platform<M>>(
        &mut self,
        store: &mut Store<M>,
        platform: &mut P,
        func: FuncAddr,
        args: &[Value],
        results: &mut Vec<Value>,
    ) -> Result<(), ExecError> {
        interp::invoke_with::<M, P, NativeFloat, StdAlloc>(
            self, store, platform, func, args, results,
        )
    }
}

/// Validates and rewrites a complete module under the selected profile.
///
/// The returned code owns all initialization bytes and has no dependency on the
/// input slice. The default `CompileLimits` apply. Resource failures are reported
/// as `Error::Visitor(VisitError::OutOfMemory)`; use `compile_with_limits` to
/// distinguish the exhausted compiler budget from validation failures.
pub fn compile(
    bytes: &[u8],
    profile: crate::ValidationProfile,
) -> Result<ExecutableModule, crate::Error> {
    compiler::compile_default_with::<StdAlloc>(bytes, profile)
}
/// Validates and rewrites a complete module with explicit compiler budgets.
///
/// Bytecode, source maps, locals, labels, and branch-table storage are bounded;
/// compiler allocations use fallible reservation. Metadata decoding retains the
/// validator's documented allocation premise. A resource failure never yields a
/// partial executable module.
pub fn compile_with_limits(
    bytes: &[u8],
    profile: crate::ValidationProfile,
    limits: CompileLimits,
) -> Result<ExecutableModule, CompileError> {
    compiler::compile_with::<StdAlloc>(bytes, profile, limits)
}

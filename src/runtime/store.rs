//! Store representation, issued handles, and object access.
mod instantiate;

use super::instantiate::{eval_const_exec, initialize_segments};
use super::platform::Alloc;
use super::*;
use crate::{
    DataMode, ElemType, ElementMode, ExportDesc, FuncType, GlobalType, ImportDesc, Limits, MemType,
    Mut, TableType, ValidationProfile,
};
use alloc::vec::Vec;

/// Limits on retained store objects and live interpreter storage.
#[derive(Clone, Copy)]
#[cfg_attr(not(charon), derive(Debug))]
pub struct StoreLimits {
    /// Total functions, signatures, tables, memories, globals, and external identities.
    pub max_objects: usize,
    /// Retained defining instances, including failed instantiations.
    pub max_instances: usize,
    /// Total instance-map entries, segment slots, and initial element values.
    pub max_instance_items: usize,
    /// Total parameter and result entries in distinct canonical signatures.
    pub max_signature_values: usize,
    /// Total linear memory bytes across the store.
    pub max_memory_bytes: usize,
    /// Total live table elements across the store.
    pub max_table_elements: usize,
    /// Call frames in one execution.
    pub max_frames: usize,
    /// Highest active frame extent in 64-bit slots in one execution.
    ///
    /// Each frame reserves its locals and statically computed peak operand
    /// storage at entry. A `v128` occupies two slots; other values occupy one.
    pub max_values: usize,
}
impl Default for StoreLimits {
    fn default() -> Self {
        Self {
            max_objects: 1_000_000,
            max_instances: 10_000,
            max_instance_items: 1_000_000,
            max_signature_values: 1_000_000,
            max_memory_bytes: 256 * 1024 * 1024,
            max_table_elements: 1_000_000,
            max_frames: 1024,
            max_values: 1_000_000,
        }
    }
}
pub(super) enum FunctionCode {
    Host(u64),
    Wasm { instance: usize, function: usize },
}
pub(super) struct Function {
    pub signature: usize,
    pub code: FunctionCode,
}
pub(super) struct Memory<M> {
    pub buf: M,
    pub maximum: Option<u32>,
}
pub(super) struct Table {
    pub elements: Vec<u64>,
    pub ty: ElemType,
    pub maximum: Option<u32>,
}
pub(super) struct GlobalInstance {
    pub lo: u64,
    pub hi: u64,
    pub ty: GlobalType,
}
pub(super) struct ElemInstance {
    pub ty: ElemType,
    pub refs: Vec<u64>,
}
pub(super) struct DataInstance {
    pub bytes: Vec<u8>,
}
pub(super) struct Instance {
    pub module: ExecutableModule,
    pub types: Vec<usize>,
    pub funcs: Vec<FuncAddr>,
    pub tables: Vec<TableAddr>,
    pub memories: Vec<MemoryAddr>,
    pub globals: Vec<GlobalAddr>,
    pub elements: Vec<usize>,
    pub data: Vec<usize>,
}
/// An append-only owner of runtime objects and their defining module instances.
///
/// Dropping a failed instantiation does not undo observable imported-object writes.
/// Objects retained by such an instance remain valid until this store is dropped.
pub struct Store<M = VecMemory> {
    pub(super) id: usize,
    pub(super) limits: StoreLimits,
    pub(super) funcs: Vec<Function>,
    pub(super) types: Vec<FuncType>,
    pub(super) tables: Vec<Table>,
    pub(super) memories: Vec<Memory<M>>,
    pub(super) globals: Vec<GlobalInstance>,
    pub(super) instances: Vec<Instance>,
    pub(super) elems: Vec<ElemInstance>,
    pub(super) datas: Vec<DataInstance>,
    externs: Vec<u64>,
    instance_items: usize,
    signature_values: usize,
    memory_bytes: usize,
    table_elements: usize,
}
impl<M: MemoryBuffer> Store<M> {
    pub(crate) fn with_identity(id: usize, limits: StoreLimits) -> Self {
        Self {
            id,
            limits,
            funcs: Vec::new(),
            types: Vec::new(),
            tables: Vec::new(),
            memories: Vec::new(),
            globals: Vec::new(),
            instances: Vec::new(),
            elems: Vec::new(),
            datas: Vec::new(),
            externs: Vec::new(),
            instance_items: 0,
            signature_values: 0,
            memory_bytes: 0,
            table_elements: 0,
        }
    }
    pub(super) fn check(&self, id: usize) -> Result<(), ExecError> {
        if id == self.id {
            Ok(())
        } else {
            Err(ExecError::WrongStore)
        }
    }
    fn room(&self) -> Result<(), ExecError> {
        let n = self.funcs.len()
            + self.tables.len()
            + self.memories.len()
            + self.globals.len()
            + self.externs.len()
            + self.types.len();
        if n >= self.limits.max_objects {
            Err(ExecError::Exhausted(ResourceLimit::Objects))
        } else {
            Ok(())
        }
    }
    pub(super) fn check_value(&self, v: Value) -> Result<(), ExecError> {
        match v {
            Value::FuncRef(Some(a)) => self.check(a.store),
            Value::ExternRef(Some(a)) => self.check(a.store),
            _ => Ok(()),
        }
    }
    /// Allocates a typed synchronous host-function identity.
    pub(crate) fn define_host_with<A: Alloc>(
        &mut self,
        ty: FuncType,
        host_id: u64,
    ) -> Result<FuncAddr, ExecError> {
        let signature = self.intern_type::<A>(&ty)?;
        self.room()?;
        reserve::<A, _>(&mut self.funcs, 1)?;
        let a = FuncAddr {
            store: self.id,
            index: self.funcs.len(),
        };
        self.funcs.push(Function {
            signature,
            code: FunctionCode::Host(host_id),
        });
        Ok(a)
    }
    /// Allocates an opaque embedding identity, retained for the store's lifetime.
    pub(crate) fn define_extern_with<A: Alloc>(
        &mut self,
        identity: u64,
    ) -> Result<ExternAddr, ExecError> {
        self.room()?;
        reserve::<A, _>(&mut self.externs, 1)?;
        let a = ExternAddr {
            store: self.id,
            index: self.externs.len(),
        };
        self.externs.push(identity);
        Ok(a)
    }
    /// Returns the embedding identity associated with an external reference.
    pub fn extern_identity(&self, a: ExternAddr) -> Result<u64, ExecError> {
        self.check(a.store)?;
        Ok(self.externs[a.index])
    }
    /// Defines a memory using an embedding-owned buffer of its initial size.
    pub(crate) fn define_memory_with<A: Alloc>(
        &mut self,
        ty: MemType,
        buf: M,
    ) -> Result<MemoryAddr, ExecError> {
        self.room()?;
        check_limits(ty.limits, 65536)?;
        let size = ty.limits.min as u64 * 65536;
        if buf.bytes().len() as u64 != size {
            return Err(ExecError::BadArguments);
        }
        if !within(
            self.memory_bytes,
            buf.bytes().len(),
            self.limits.max_memory_bytes,
        ) {
            return Err(ExecError::Exhausted(ResourceLimit::Allocation));
        }
        reserve::<A, _>(&mut self.memories, 1)?;
        let a = MemoryAddr {
            store: self.id,
            index: self.memories.len(),
        };
        self.memories.push(Memory {
            buf,
            maximum: ty.limits.max,
        });
        self.memory_bytes += size as usize;
        Ok(a)
    }
    /// Allocates a table initially filled with null references of its element type.
    pub(crate) fn define_table_with<A: Alloc>(
        &mut self,
        ty: TableType,
    ) -> Result<TableAddr, ExecError> {
        self.room()?;
        check_limits(ty.limits, u32::MAX)?;
        if !within(
            self.table_elements(),
            ty.limits.min as usize,
            self.limits.max_table_elements,
        ) {
            return Err(ExecError::Exhausted(ResourceLimit::Allocation));
        }
        let mut elements = Vec::new();
        reserve::<A, _>(&mut elements, ty.limits.min as usize)?;
        let mut i = 0;
        while i < ty.limits.min {
            elements.push(0);
            i += 1;
        }
        reserve::<A, _>(&mut self.tables, 1)?;
        let a = TableAddr {
            store: self.id,
            index: self.tables.len(),
        };
        self.tables.push(Table {
            elements,
            ty: ty.elem,
            maximum: ty.limits.max,
        });
        self.table_elements += ty.limits.min as usize;
        Ok(a)
    }
    /// Allocates a global with a matching, store-owned value.
    pub(crate) fn define_global_with<A: Alloc>(
        &mut self,
        ty: GlobalType,
        value: Value,
    ) -> Result<GlobalAddr, ExecError> {
        self.room()?;
        self.check_value(value)?;
        if ty.valtype != value.value_type() {
            return Err(ExecError::BadArguments);
        }
        reserve::<A, _>(&mut self.globals, 1)?;
        let a = GlobalAddr {
            store: self.id,
            index: self.globals.len(),
        };
        let (lo, hi) = value::encode(value);
        self.globals.push(GlobalInstance { lo, hi, ty });
        Ok(a)
    }
    /// Returns the structural signature of a function in this store.
    pub fn func_type(&self, a: FuncAddr) -> Result<&FuncType, ExecError> {
        self.check(a.store)?;
        Ok(&self.types[self.funcs[a.index].signature])
    }

    fn intern_type<A: Alloc>(&mut self, ty: &FuncType) -> Result<usize, ExecError> {
        let mut i = 0;
        while i < self.types.len() && !same_func_type(&self.types[i], ty) {
            i += 1;
        }
        if i < self.types.len() {
            return Ok(i);
        }
        let count = ty
            .params
            .len()
            .checked_add(ty.results.len())
            .ok_or(ExecError::Exhausted(ResourceLimit::Objects))?;
        if !within(
            self.signature_values,
            count,
            self.limits.max_signature_values,
        ) {
            return Err(ExecError::Exhausted(ResourceLimit::Objects));
        }
        self.room()?;
        reserve::<A, _>(&mut self.types, 1)?;
        self.types.push(copy_type::<A>(ty)?);
        self.signature_values += count;
        Ok(i)
    }
    /// Reads a global belonging to this store.
    pub fn global(&self, a: GlobalAddr) -> Result<Value, ExecError> {
        self.check(a.store)?;
        let g = &self.globals[a.index];
        Ok(value::decode(g.ty.valtype, g.lo, g.hi, self.id))
    }
    /// Writes a mutable global with a value of its declared type.
    pub fn set_global(&mut self, a: GlobalAddr, v: Value) -> Result<(), ExecError> {
        self.check(a.store)?;
        self.check_value(v)?;
        let g = &mut self.globals[a.index];
        if g.ty.mutability != Mut::Var || g.ty.valtype != v.value_type() {
            return Err(ExecError::BadArguments);
        }
        let (lo, hi) = value::encode(v);
        g.lo = lo;
        g.hi = hi;
        Ok(())
    }
    /// Borrows the current bytes of a memory in this store.
    pub fn memory(&self, a: MemoryAddr) -> Result<&[u8], ExecError> {
        self.check(a.store)?;
        Ok(self.memories[a.index].buf.bytes())
    }
    /// Borrows memory bytes for embedding mutation without changing its size.
    pub fn memory_mut(&mut self, a: MemoryAddr) -> Result<&mut [u8], ExecError> {
        if a.store != self.id {
            return Err(ExecError::WrongStore);
        }
        Ok(self.memories[a.index].buf.bytes_mut())
    }
    /// Returns the number of elements in a table.
    pub fn table_size(&self, a: TableAddr) -> Result<u32, ExecError> {
        self.check(a.store)?;
        Ok(self.tables[a.index].elements.len() as u32)
    }
    /// Reads a typed reference from a table.
    pub fn table_get(&self, a: TableAddr, index: u32) -> Result<Value, ExecError> {
        self.check(a.store)?;
        let t = &self.tables[a.index];
        if index as usize >= t.elements.len() {
            return Err(ExecError::Trap(Trap::TableOutOfBounds));
        }
        Ok(value::decode(
            t.ty.value_type(),
            t.elements[index as usize],
            0,
            self.id,
        ))
    }
    /// Writes a table element after checking ownership, type, and bounds.
    pub fn set_table(&mut self, a: TableAddr, index: u32, v: Value) -> Result<(), ExecError> {
        self.check(a.store)?;
        self.check_value(v)?;
        let t = &mut self.tables[a.index];
        if t.ty.value_type() != v.value_type() {
            return Err(ExecError::BadArguments);
        }
        if index as usize >= t.elements.len() {
            return Err(ExecError::Trap(Trap::TableOutOfBounds));
        }
        t.elements[index as usize] = value::encode(v).0;
        Ok(())
    }
    /// Resolves an export by its UTF-8 byte name.
    pub fn export(&self, a: InstanceAddr, name: &[u8]) -> Result<Option<Extern>, ExecError> {
        self.check(a.store)?;
        let inst = &self.instances[a.index];
        let env = inst.module.env();
        let mut i = 0;
        let mut found = None;
        while i < env.exports().len() && found.is_none() {
            let ex = &env.exports()[i];
            if same_bytes(&ex.name, name) {
                found = Some(match ex.desc {
                    ExportDesc::Func(n) => Extern::Func(inst.funcs[n as usize]),
                    ExportDesc::Table(n) => Extern::Table(inst.tables[n as usize]),
                    ExportDesc::Memory(n) => Extern::Memory(inst.memories[n as usize]),
                    ExportDesc::Global(n) => Extern::Global(inst.globals[n as usize]),
                });
            }
            i += 1;
        }
        Ok(found)
    }
    fn memory_bytes(&self) -> usize {
        self.memory_bytes
    }
    fn table_elements(&self) -> usize {
        self.table_elements
    }
    pub(crate) fn grow_memory_with(
        &mut self,
        addr: MemoryAddr,
        delta: u32,
    ) -> Result<u32, ExecError> {
        self.check(addr.store)?;
        Ok(self.grow_memory_index(addr.index, delta))
    }
    pub(crate) fn grow_table_with<A: Alloc>(
        &mut self,
        addr: TableAddr,
        delta: u32,
        v: Value,
    ) -> Result<u32, ExecError> {
        self.check(addr.store)?;
        self.check_value(v)?;
        if v.value_type() != self.tables[addr.index].ty.value_type() {
            return Err(ExecError::BadArguments);
        }
        Ok(self.grow_table_index::<A>(addr.index, delta, value::encode(v).0))
    }
    pub(crate) fn grow_memory_index(&mut self, index: usize, delta: u32) -> u32 {
        let old = self.memories[index].buf.bytes().len() / 65536;
        let pages = old as u64 + delta as u64;
        if pages > 65536 || pages > self.memories[index].maximum.unwrap_or(65536) as u64 {
            return u32::MAX;
        }
        let add = delta as u64 * 65536;
        if add > usize::MAX as u64
            || pages * 65536 > usize::MAX as u64
            || !within(
                self.memory_bytes(),
                add as usize,
                self.limits.max_memory_bytes,
            )
        {
            return u32::MAX;
        }
        let m = &mut self.memories[index];
        if !m.buf.grow(pages as usize * 65536) {
            return u32::MAX;
        }
        self.memory_bytes += add as usize;
        old as u32
    }
    pub(crate) fn grow_table_index<A: Alloc>(&mut self, index: usize, delta: u32, v: u64) -> u32 {
        let old = self.tables[index].elements.len();
        let n = old as u64 + delta as u64;
        if n > u32::MAX as u64
            || n > self.tables[index].maximum.unwrap_or(u32::MAX) as u64
            || !within(
                self.table_elements(),
                delta as usize,
                self.limits.max_table_elements,
            )
        {
            return u32::MAX;
        }
        let t = &mut self.tables[index];
        if !A::reserve(&mut t.elements, delta as usize) {
            return u32::MAX;
        }
        let mut i = old;
        while i < n as usize {
            t.elements.push(v);
            i += 1;
        }
        self.table_elements += delta as usize;
        old as u32
    }
}
fn same_bytes(left: &[u8], right: &[u8]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut index = 0;
    let mut same = true;
    while index < left.len() && same {
        same = left[index] == right[index];
        index += 1;
    }
    same
}
fn instantiation_failed(result: &Result<InstanceAddr, ExecError>) -> bool {
    match result {
        Ok(_) => false,
        Err(_) => true,
    }
}
fn wasm1(profile: ValidationProfile) -> bool {
    match profile {
        ValidationProfile::Wasm1 => true,
        ValidationProfile::Wasm2 => false,
    }
}
fn check_limits(l: Limits, max: u32) -> Result<(), ExecError> {
    if l.min > max || l.max.unwrap_or(max) > max || l.min > l.max.unwrap_or(max) {
        Err(ExecError::BadArguments)
    } else {
        Ok(())
    }
}
fn matches_limits(size: u64, maximum: Option<u32>, required: Limits) -> bool {
    size >= required.min as u64
        && match required.max {
            None => true,
            Some(r) => match maximum {
                Some(m) => m <= r,
                None => false,
            },
        }
}
fn copy_bytes<A: Alloc>(source: &[u8]) -> Result<Vec<u8>, ExecError> {
    let mut bytes = Vec::new();
    reserve::<A, _>(&mut bytes, source.len())?;
    let mut i = 0;
    while i < source.len() {
        bytes.push(source[i]);
        i += 1;
    }
    Ok(bytes)
}
fn add_items(items: &mut usize, additional: usize) -> Result<(), ExecError> {
    match items.checked_add(additional) {
        Some(n) => {
            *items = n;
            Ok(())
        }
        None => Err(ExecError::Exhausted(ResourceLimit::Objects)),
    }
}

fn within(current: usize, additional: usize, limit: usize) -> bool {
    match current.checked_add(additional) {
        Some(total) => total <= limit,
        None => false,
    }
}

fn same_func_type(a: &FuncType, b: &FuncType) -> bool {
    if a.params.len() != b.params.len() || a.results.len() != b.results.len() {
        return false;
    }
    let mut i = 0;
    let mut same = true;
    while i < a.params.len() && same {
        same = a.params[i] == b.params[i];
        i += 1;
    }
    i = 0;
    while i < a.results.len() && same {
        same = a.results[i] == b.results[i];
        i += 1;
    }
    same
}

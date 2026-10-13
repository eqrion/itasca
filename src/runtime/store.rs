use super::*;
use crate::{
    ConstExpr, DataMode, ElemType, ElementMode, ExportDesc, FuncType, GlobalType, ImportDesc,
    Limits, MemType, Mut, TableType, ValidationProfile,
};
use alloc::{rc::Rc, vec::Vec};
use core::sync::atomic::{AtomicUsize, Ordering};

static NEXT_STORE: AtomicUsize = AtomicUsize::new(1);

/// Limits on retained store objects and live interpreter storage.
#[derive(Clone, Copy, Debug)]
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
    /// Locals and operands in one execution.
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
pub(super) struct Memory {
    pub bytes: Vec<u8>,
    pub maximum: Option<u32>,
}
pub(super) struct Table {
    pub elements: Vec<Value>,
    pub ty: ElemType,
    pub maximum: Option<u32>,
}
pub(super) struct GlobalInstance {
    pub value: Value,
    pub ty: GlobalType,
}
pub(super) struct Instance {
    pub module: Rc<ExecutableModule>,
    pub types: Vec<usize>,
    pub funcs: Vec<FuncAddr>,
    pub tables: Vec<TableAddr>,
    pub memories: Vec<MemoryAddr>,
    pub globals: Vec<GlobalAddr>,
    pub elements: Vec<Vec<Value>>,
    pub data: Vec<bool>,
}
/// An append-only owner of runtime objects and their defining module instances.
///
/// Dropping a failed instantiation does not undo observable imported-object writes.
/// Objects retained by such an instance remain valid until this store is dropped.
pub struct Store {
    pub(super) id: usize,
    pub(super) limits: StoreLimits,
    pub(super) funcs: Vec<Function>,
    pub(super) types: Vec<FuncType>,
    pub(super) tables: Vec<Table>,
    pub(super) memories: Vec<Memory>,
    pub(super) globals: Vec<GlobalInstance>,
    pub(super) instances: Vec<Instance>,
    externs: Vec<u64>,
    instance_items: usize,
    signature_values: usize,
    memory_bytes: usize,
    table_elements: usize,
}
impl Default for Store {
    fn default() -> Self {
        Self::new()
    }
}
impl Store {
    /// Creates an empty store with the documented default resource limits.
    pub fn new() -> Self {
        Self::with_limits(StoreLimits::default())
    }
    /// Creates an empty store with explicit resource limits.
    pub fn with_limits(limits: StoreLimits) -> Self {
        let mut id = NEXT_STORE.load(Ordering::Relaxed);
        loop {
            let next = id.checked_add(1).expect("store identity space exhausted");
            match NEXT_STORE.compare_exchange_weak(id, next, Ordering::Relaxed, Ordering::Relaxed) {
                Ok(_) => break,
                Err(now) => id = now,
            }
        }
        Self {
            id,
            limits,
            funcs: Vec::new(),
            types: Vec::new(),
            tables: Vec::new(),
            memories: Vec::new(),
            globals: Vec::new(),
            instances: Vec::new(),
            externs: Vec::new(),
            instance_items: 0,
            signature_values: 0,
            memory_bytes: 0,
            table_elements: 0,
        }
    }
    pub(super) fn check(&self, id: usize) -> Result<(), RuntimeError> {
        if id == self.id {
            Ok(())
        } else {
            Err(RuntimeError::WrongStore)
        }
    }
    fn room(&self) -> Result<(), RuntimeError> {
        let n = self.funcs.len()
            + self.tables.len()
            + self.memories.len()
            + self.globals.len()
            + self.externs.len()
            + self.types.len();
        if n >= self.limits.max_objects {
            Err(RuntimeError::Resource(ResourceLimit::Objects))
        } else {
            Ok(())
        }
    }
    pub(super) fn check_value(&self, v: Value) -> Result<(), RuntimeError> {
        match v {
            Value::FuncRef(Some(a)) => self.check(a.store),
            Value::ExternRef(Some(a)) => self.check(a.store),
            _ => Ok(()),
        }
    }
    /// Allocates a typed host-function identity. Callbacks are driven by `Outcome`.
    pub fn define_host(&mut self, ty: FuncType, host_id: u64) -> Result<FuncAddr, RuntimeError> {
        let signature = self.intern_type(&ty)?;
        self.room()?;
        reserve(&mut self.funcs, 1)?;
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
    pub fn define_extern(&mut self, identity: u64) -> Result<ExternAddr, RuntimeError> {
        self.room()?;
        reserve(&mut self.externs, 1)?;
        let a = ExternAddr {
            store: self.id,
            index: self.externs.len(),
        };
        self.externs.push(identity);
        Ok(a)
    }
    /// Returns the embedding identity associated with an external reference.
    pub fn extern_identity(&self, a: ExternAddr) -> Result<u64, RuntimeError> {
        self.check(a.store)?;
        Ok(self.externs[a.index])
    }
    /// Allocates a zero-initialized memory, enforcing specification and store limits.
    pub fn define_memory(&mut self, ty: MemType) -> Result<MemoryAddr, RuntimeError> {
        self.room()?;
        check_limits(ty.limits, 65536)?;
        let size = (ty.limits.min as u64) * 65536;
        if size > self.limits.max_memory_bytes as u64
            || !within(
                self.memory_bytes(),
                size as usize,
                self.limits.max_memory_bytes,
            )
        {
            return Err(RuntimeError::Resource(ResourceLimit::Allocation));
        }
        let mut bytes = Vec::new();
        reserve(&mut bytes, size as usize)?;
        bytes.resize(size as usize, 0);
        reserve(&mut self.memories, 1)?;
        let a = MemoryAddr {
            store: self.id,
            index: self.memories.len(),
        };
        self.memories.push(Memory {
            bytes,
            maximum: ty.limits.max,
        });
        self.memory_bytes += size as usize;
        Ok(a)
    }
    /// Allocates a table initially filled with null references of its element type.
    pub fn define_table(&mut self, ty: TableType) -> Result<TableAddr, RuntimeError> {
        self.room()?;
        check_limits(ty.limits, u32::MAX)?;
        if !within(
            self.table_elements(),
            ty.limits.min as usize,
            self.limits.max_table_elements,
        ) {
            return Err(RuntimeError::Resource(ResourceLimit::Allocation));
        }
        let mut elements = Vec::new();
        reserve(&mut elements, ty.limits.min as usize)?;
        elements.resize(ty.limits.min as usize, Value::zero(ty.elem.value_type()));
        reserve(&mut self.tables, 1)?;
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
    pub fn define_global(
        &mut self,
        ty: GlobalType,
        value: Value,
    ) -> Result<GlobalAddr, RuntimeError> {
        self.room()?;
        self.check_value(value)?;
        if ty.valtype != value.value_type() {
            return Err(RuntimeError::TypeMismatch);
        }
        reserve(&mut self.globals, 1)?;
        let a = GlobalAddr {
            store: self.id,
            index: self.globals.len(),
        };
        self.globals.push(GlobalInstance { value, ty });
        Ok(a)
    }
    /// Returns the structural signature of a function in this store.
    pub fn func_type(&self, a: FuncAddr) -> Result<&FuncType, RuntimeError> {
        self.check(a.store)?;
        Ok(&self.types[self.funcs[a.index].signature])
    }

    fn intern_type(&mut self, ty: &FuncType) -> Result<usize, RuntimeError> {
        let mut i = 0;
        while i < self.types.len() {
            if &self.types[i] == ty {
                return Ok(i);
            }
            i += 1;
        }
        let count = ty
            .params
            .len()
            .checked_add(ty.results.len())
            .ok_or(RuntimeError::Resource(ResourceLimit::Objects))?;
        if !within(
            self.signature_values,
            count,
            self.limits.max_signature_values,
        ) {
            return Err(RuntimeError::Resource(ResourceLimit::Objects));
        }
        self.room()?;
        reserve(&mut self.types, 1)?;
        self.types.push(copy_type(ty)?);
        self.signature_values += count;
        Ok(i)
    }
    /// Reads a global belonging to this store.
    pub fn global(&self, a: GlobalAddr) -> Result<Value, RuntimeError> {
        self.check(a.store)?;
        Ok(self.globals[a.index].value)
    }
    /// Writes a mutable global with a value of its declared type.
    pub fn set_global(&mut self, a: GlobalAddr, v: Value) -> Result<(), RuntimeError> {
        self.check(a.store)?;
        self.check_value(v)?;
        let g = &mut self.globals[a.index];
        if g.ty.mutability != Mut::Var || g.ty.valtype != v.value_type() {
            return Err(RuntimeError::TypeMismatch);
        }
        g.value = v;
        Ok(())
    }
    /// Borrows the current bytes of a memory in this store.
    pub fn memory(&self, a: MemoryAddr) -> Result<&[u8], RuntimeError> {
        self.check(a.store)?;
        Ok(&self.memories[a.index].bytes)
    }
    /// Borrows memory bytes for embedding mutation without changing its size.
    pub fn memory_mut(&mut self, a: MemoryAddr) -> Result<&mut [u8], RuntimeError> {
        self.check(a.store)?;
        Ok(&mut self.memories[a.index].bytes)
    }
    /// Borrows the reference elements of a table.
    pub fn table(&self, a: TableAddr) -> Result<&[Value], RuntimeError> {
        self.check(a.store)?;
        Ok(&self.tables[a.index].elements)
    }
    /// Writes a table element after checking ownership, type, and bounds.
    pub fn set_table(&mut self, a: TableAddr, index: u32, v: Value) -> Result<(), RuntimeError> {
        self.check(a.store)?;
        self.check_value(v)?;
        let t = &mut self.tables[a.index];
        if t.ty.value_type() != v.value_type() {
            return Err(RuntimeError::TypeMismatch);
        }
        let x = t
            .elements
            .get_mut(index as usize)
            .ok_or(RuntimeError::Trap(Trap::TableOutOfBounds))?;
        *x = v;
        Ok(())
    }
    /// Resolves an export by its UTF-8 byte name.
    pub fn export(&self, a: InstanceAddr, name: &[u8]) -> Result<Option<Extern>, RuntimeError> {
        self.check(a.store)?;
        let inst = &self.instances[a.index];
        let env = inst.module.env();
        let mut i = 0;
        while i < env.exports().len() {
            let ex = &env.exports()[i];
            if ex.name == name {
                return Ok(Some(match ex.desc {
                    ExportDesc::Func(n) => Extern::Func(inst.funcs[n as usize]),
                    ExportDesc::Table(n) => Extern::Table(inst.tables[n as usize]),
                    ExportDesc::Memory(n) => Extern::Memory(inst.memories[n as usize]),
                    ExportDesc::Global(n) => Extern::Global(inst.globals[n as usize]),
                }));
            }
            i += 1;
        }
        Ok(None)
    }
    fn memory_bytes(&self) -> usize {
        self.memory_bytes
    }
    fn table_elements(&self) -> usize {
        self.table_elements
    }
    pub(super) fn grow_memory(&mut self, index: usize, delta: u32) -> u32 {
        let old = self.memories[index].bytes.len() / 65536;
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
        if m.bytes.try_reserve(add as usize).is_err() {
            return u32::MAX;
        }
        m.bytes.resize(pages as usize * 65536, 0);
        self.memory_bytes += add as usize;
        old as u32
    }
    pub(super) fn grow_table(&mut self, index: usize, delta: u32, v: Value) -> u32 {
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
        if t.elements.try_reserve(delta as usize).is_err() {
            return u32::MAX;
        }
        t.elements.resize(n as usize, v);
        self.table_elements += delta as usize;
        old as u32
    }
}
fn check_limits(l: Limits, max: u32) -> Result<(), RuntimeError> {
    if l.min > max || l.max.unwrap_or(max) > max || l.min > l.max.unwrap_or(max) {
        Err(RuntimeError::TypeMismatch)
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
impl Store {
    /// Links and initializes a module, returning resumable start-function work.
    ///
    /// Imports are supplied in declaration order and share the provider's objects.
    /// Wasm 1.0 checks every active segment before writes; Wasm 2.0 applies them
    /// sequentially. A trap preserves prior effects and all allocated addresses.
    pub fn instantiate(
        &mut self,
        module: Rc<ExecutableModule>,
        imports: &[Extern],
    ) -> Result<Instantiation, RuntimeError> {
        let functions = self.funcs.len();
        let tables = self.tables.len();
        let memories = self.memories.len();
        let globals = self.globals.len();
        let types = self.types.len();
        let signature_values = self.signature_values;
        let memory_bytes = self.memory_bytes;
        let table_elements = self.table_elements;
        let instances = self.instances.len();
        let result = self.instantiate_inner(module, imports);
        // Before publication, no allocated address can have escaped and no
        // imported object has been written. Discard provisional objects on
        // failure so every retained Wasm function has a defining instance.
        // After publication, traps preserve all objects and observable effects.
        if result.is_err() && self.instances.len() == instances {
            self.funcs.truncate(functions);
            self.tables.truncate(tables);
            self.memories.truncate(memories);
            self.globals.truncate(globals);
            self.types.truncate(types);
            self.signature_values = signature_values;
            self.memory_bytes = memory_bytes;
            self.table_elements = table_elements;
        }
        result
    }

    fn instantiate_inner(
        &mut self,
        module: Rc<ExecutableModule>,
        imports: &[Extern],
    ) -> Result<Instantiation, RuntimeError> {
        let env = module.env();
        if imports.len() != env.imports().len() {
            return Err(RuntimeError::Link(LinkError::MissingImport));
        }
        if self.instances.len() >= self.limits.max_instances {
            return Err(RuntimeError::Resource(ResourceLimit::Objects));
        }
        let mut items = 0usize;
        let counts = [
            env.types().len(),
            env.func_types().len(),
            env.table_types().len(),
            env.mem_types().len(),
            env.global_types().len(),
            env.elements().len(),
            module.tail().data.len(),
        ];
        let mut count_index = 0;
        while count_index < counts.len() {
            items = items
                .checked_add(counts[count_index])
                .ok_or(RuntimeError::Resource(ResourceLimit::Objects))?;
            count_index += 1;
        }
        let mut element = 0;
        while element < env.elements().len() {
            items = items
                .checked_add(env.elements()[element].init.len())
                .ok_or(RuntimeError::Resource(ResourceLimit::Objects))?;
            element += 1;
        }
        if !within(self.instance_items, items, self.limits.max_instance_items) {
            return Err(RuntimeError::Resource(ResourceLimit::Objects));
        }
        let mut inst = Instance {
            module: Rc::clone(&module),
            types: Vec::new(),
            funcs: Vec::new(),
            tables: Vec::new(),
            memories: Vec::new(),
            globals: Vec::new(),
            elements: Vec::new(),
            data: Vec::new(),
        };
        reserve(&mut inst.funcs, env.func_types().len())?;
        reserve(&mut inst.tables, env.table_types().len())?;
        reserve(&mut inst.memories, env.mem_types().len())?;
        reserve(&mut inst.globals, env.global_types().len())?;
        let incompatible = RuntimeError::Link(LinkError::IncompatibleImportType);
        let mut i = 0;
        while i < imports.len() {
            match (env.imports()[i].desc, imports[i]) {
                (ImportDesc::Func(t), Extern::Func(a)) => {
                    self.check(a.store)?;
                    if self.types[self.funcs[a.index].signature] != env.types()[t as usize] {
                        return Err(incompatible);
                    }
                    inst.funcs.push(a);
                }
                (ImportDesc::Table(t), Extern::Table(a)) => {
                    self.check(a.store)?;
                    let v = &self.tables[a.index];
                    if t.elem != v.ty
                        || !matches_limits(v.elements.len() as u64, v.maximum, t.limits)
                    {
                        return Err(incompatible);
                    }
                    inst.tables.push(a);
                }
                (ImportDesc::Memory(t), Extern::Memory(a)) => {
                    self.check(a.store)?;
                    let v = &self.memories[a.index];
                    if !matches_limits((v.bytes.len() / 65536) as u64, v.maximum, t.limits) {
                        return Err(incompatible);
                    }
                    inst.memories.push(a);
                }
                (ImportDesc::Global(t), Extern::Global(a)) => {
                    self.check(a.store)?;
                    if self.globals[a.index].ty != t {
                        return Err(incompatible);
                    }
                    inst.globals.push(a);
                }
                _ => return Err(incompatible),
            }
            i += 1;
        }
        let identity = InstanceAddr {
            store: self.id,
            index: self.instances.len(),
        };
        reserve(&mut inst.types, env.types().len())?;
        i = 0;
        while i < env.types().len() {
            inst.types.push(self.intern_type(&env.types()[i])?);
            i += 1;
        }
        i = 0;
        while i < env.func_type_indices().len() {
            self.room()?;
            reserve(&mut self.funcs, 1)?;
            let a = FuncAddr {
                store: self.id,
                index: self.funcs.len(),
            };
            self.funcs.push(Function {
                signature: inst.types[env.func_type_indices()[i] as usize],
                code: FunctionCode::Wasm {
                    instance: identity.index,
                    function: i,
                },
            });
            inst.funcs.push(a);
            i += 1;
        }
        i = inst.tables.len();
        while i < env.table_types().len() {
            inst.tables.push(self.define_table(env.table_types()[i])?);
            i += 1;
        }
        i = inst.memories.len();
        while i < env.mem_types().len() {
            inst.memories.push(self.define_memory(env.mem_types()[i])?);
            i += 1;
        }
        i = 0;
        while i < env.globals().len() {
            let g = env.globals()[i];
            let v = eval_const(self, &inst, g.init)?;
            inst.globals.push(self.define_global(g.gtype, v)?);
            i += 1;
        }
        reserve(&mut inst.elements, env.elements().len())?;
        i = 0;
        while i < env.elements().len() {
            let segment = &env.elements()[i];
            let mut values = Vec::new();
            reserve(&mut values, segment.init.len())?;
            let mut j = 0;
            while j < segment.init.len() {
                values.push(eval_const(self, &inst, segment.init[j])?);
                j += 1;
            }
            inst.elements.push(values);
            i += 1;
        }
        reserve(&mut inst.data, module.tail().data.len())?;
        inst.data.resize(module.tail().data.len(), true);
        // Publish the internal defining instance before any function can escape.
        // The public handle is withheld until start succeeds.
        reserve(&mut self.instances, 1)?;
        self.instances.push(inst);
        self.instance_items += items;
        if module.profile() == ValidationProfile::Wasm1 {
            i = 0;
            while i < env.elements().len() {
                self.element_range(identity.index, i)?;
                i += 1;
            }
            i = 0;
            while i < module.tail().data.len() {
                self.data_range(identity.index, i)?;
                i += 1;
            }
        }
        i = 0;
        while i < env.elements().len() {
            match env.elements()[i].mode {
                ElementMode::Active { table_idx, .. } => {
                    let r = self
                        .element_range(identity.index, i)?
                        .ok_or(RuntimeError::InvalidState)?;
                    let table = self.instances[identity.index].tables[table_idx as usize].index;
                    let mut j = 0;
                    while j < r.len() {
                        self.tables[table].elements[r.start + j] =
                            self.instances[identity.index].elements[i][j];
                        j += 1;
                    }
                    self.instances[identity.index].elements[i].clear();
                }
                ElementMode::Declarative => self.instances[identity.index].elements[i].clear(),
                ElementMode::Passive => (),
            }
            i += 1;
        }
        i = 0;
        while i < module.tail().data.len() {
            if let DataMode::Active { memory_idx, .. } = module.tail().data[i].mode {
                let r = self
                    .data_range(identity.index, i)?
                    .ok_or(RuntimeError::InvalidState)?;
                let memory = self.instances[identity.index].memories[memory_idx as usize].index;
                self.memories[memory].bytes[r].copy_from_slice(&module.tail().data[i].init);
                self.instances[identity.index].data[i] = false;
            }
            i += 1;
        }
        let execution = match env.start() {
            Some(f) => Some(Execution::new(
                self,
                self.instances[identity.index].funcs[f as usize],
                &[],
            )?),
            None => None,
        };
        Ok(Instantiation {
            identity,
            execution,
            done: false,
            failed: false,
        })
    }
    fn element_range(
        &self,
        instance: usize,
        index: usize,
    ) -> Result<Option<core::ops::Range<usize>>, RuntimeError> {
        let inst = &self.instances[instance];
        let e = &inst.module.env().elements()[index];
        match e.mode {
            ElementMode::Active { table_idx, offset } => {
                let start = eval_const(self, inst, offset)?.i32()?;
                Ok(Some(range(
                    start as u64,
                    e.init.len() as u64,
                    self.tables[inst.tables[table_idx as usize].index]
                        .elements
                        .len(),
                    Trap::TableOutOfBounds,
                )?))
            }
            _ => Ok(None),
        }
    }
    fn data_range(
        &self,
        instance: usize,
        index: usize,
    ) -> Result<Option<core::ops::Range<usize>>, RuntimeError> {
        let inst = &self.instances[instance];
        let d = &inst.module.tail().data[index];
        match d.mode {
            DataMode::Active { memory_idx, offset } => {
                let start = eval_const(self, inst, offset)?.i32()?;
                Ok(Some(range(
                    start as u64,
                    d.init.len() as u64,
                    self.memories[inst.memories[memory_idx as usize].index]
                        .bytes
                        .len(),
                    Trap::MemoryOutOfBounds,
                )?))
            }
            _ => Ok(None),
        }
    }
}
fn eval_const(store: &Store, inst: &Instance, expr: ConstExpr) -> Result<Value, RuntimeError> {
    Ok(match expr {
        ConstExpr::I32(x) => Value::I32(x as u32),
        ConstExpr::I64(x) => Value::I64(x as u64),
        ConstExpr::F32(x) => Value::F32(x),
        ConstExpr::F64(x) => Value::F64(x),
        ConstExpr::V128(lo, hi) => Value::V128(lo as u128 | ((hi as u128) << 64)),
        ConstExpr::RefNull(t) => Value::zero(t.value_type()),
        ConstExpr::RefFunc(f) => Value::FuncRef(Some(inst.funcs[f as usize])),
        ConstExpr::GlobalGet(g) => store.globals[inst.globals[g as usize].index].value,
    })
}
/// A pending module instantiation, including a start-function continuation.
///
/// `instance` becomes available after successful completion. Suspending or
/// resuming never repeats allocation, segment writes, or a host invocation.
pub struct Instantiation {
    identity: InstanceAddr,
    execution: Option<Execution>,
    done: bool,
    failed: bool,
}
impl Instantiation {
    /// Runs initialization synchronously through embedding host calls.
    pub fn run_with_host<H: Host>(&mut self, store: &mut Store, host: &mut H) -> Outcome {
        loop {
            match self.run(store) {
                Outcome::NeedsHostCall(request) => {
                    let values = host.call(store, request);
                    let result = match &values {
                        Ok(values) => Ok(values.as_slice()),
                        Err(error) => Err(*error),
                    };
                    if let Err(error) = self.resume_host(store, result) {
                        return Outcome::Failed(error);
                    }
                }
                outcome => return outcome,
            }
        }
    }
    /// Returns the instance handle after start has completed successfully.
    pub fn instance(&self) -> Option<InstanceAddr> {
        if self.done {
            Some(self.identity)
        } else {
            None
        }
    }
    /// Adds fuel to the start function's retained budget.
    pub fn add_fuel(&mut self, fuel: u64) -> Result<(), RuntimeError> {
        if self.done || self.failed {
            return Err(RuntimeError::InvalidState);
        }
        match &mut self.execution {
            Some(e) => e.add_fuel(fuel),
            None => Ok(()),
        }
    }
    /// Advances the start function or completes an instance without a start.
    pub fn run(&mut self, store: &mut Store) -> Outcome {
        if self.done || self.failed {
            return Outcome::Failed(RuntimeError::InvalidState);
        }
        if let Err(e) = store.check(self.identity.store) {
            return Outcome::Failed(e);
        }
        let result = match &mut self.execution {
            Some(e) => e.run(store),
            None => Outcome::Returned(Vec::new()),
        };
        match &result {
            Outcome::Returned(_) => self.done = true,
            Outcome::Failed(_) => self.failed = true,
            _ => (),
        };
        result
    }
    /// Supplies a checked result to the outstanding start-function host call.
    pub fn resume_host(
        &mut self,
        store: &Store,
        result: Result<&[Value], RuntimeError>,
    ) -> Result<(), RuntimeError> {
        match &mut self.execution {
            Some(e) => e.resume_host(store, result),
            None => Err(RuntimeError::InvalidState),
        }
    }
}

fn within(current: usize, additional: usize, limit: usize) -> bool {
    match current.checked_add(additional) {
        Some(total) => total <= limit,
        None => false,
    }
}

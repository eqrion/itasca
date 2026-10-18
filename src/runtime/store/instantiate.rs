//! Staged instantiation, publication, and rollback before commit.
use super::*;

impl<M: MemoryBuffer> Store<M> {
    pub(crate) fn instantiate_with<P: Platform<M>, F: FloatOps, A: Alloc>(
        &mut self,
        module: ExecutableModule,
        imports: &[Extern],
        platform: &mut P,
    ) -> Result<InstanceAddr, ExecError> {
        let functions = self.funcs.len();
        let tables = self.tables.len();
        let memories = self.memories.len();
        let globals = self.globals.len();
        let types = self.types.len();
        let signature_values = self.signature_values;
        let memory_bytes = self.memory_bytes;
        let table_elements = self.table_elements;
        let instances = self.instances.len();
        let elems = self.elems.len();
        let datas = self.datas.len();
        let mut committed = false;
        let result = self.instantiate_inner::<P, F, A>(module, imports, platform, &mut committed);
        // Provisional objects have not escaped. Before publication no imported
        // object has been written, including Wasm 1.0 bounds-check failures.
        if instantiation_failed(&result) && !committed {
            while self.elems.len() > elems {
                self.elems.pop();
            }
            while self.datas.len() > datas {
                self.datas.pop();
            }
            while self.instances.len() > instances {
                self.instances.pop();
            }
            while self.funcs.len() > functions {
                self.funcs.pop();
            }
            while self.tables.len() > tables {
                self.tables.pop();
            }
            while self.memories.len() > memories {
                self.memories.pop();
            }
            while self.globals.len() > globals {
                self.globals.pop();
            }
            while self.types.len() > types {
                self.types.pop();
            }
            self.signature_values = signature_values;
            self.memory_bytes = memory_bytes;
            self.table_elements = table_elements;
        }
        result
    }
    fn instantiate_inner<P: Platform<M>, F: FloatOps, A: Alloc>(
        &mut self,
        module: ExecutableModule,
        imports: &[Extern],
        platform: &mut P,
        committed: &mut bool,
    ) -> Result<InstanceAddr, ExecError> {
        if imports.len() != module.env().imports().len() {
            return Err(ExecError::Link(LinkError::MissingImport));
        }
        if self.instances.len() >= self.limits.max_instances {
            return Err(ExecError::Exhausted(ResourceLimit::Objects));
        }
        let mut items = 0usize;
        let mut status = Ok(());
        let counts = [
            module.env().types().len(),
            module.env().func_types().len(),
            module.env().table_types().len(),
            module.env().mem_types().len(),
            module.env().global_types().len(),
            module.env().elements().len(),
            module.tail().data.len(),
        ];
        let mut i = 0;
        while i < counts.len() && status.is_ok() {
            status = add_items(&mut items, counts[i]);
            i += 1;
        }
        i = 0;
        while i < module.env().elements().len() && status.is_ok() {
            let additional = module.env().elements()[i].init.len();
            status = add_items(&mut items, additional);
            i += 1;
        }
        status?;
        if !within(self.instance_items, items, self.limits.max_instance_items) {
            return Err(ExecError::Exhausted(ResourceLimit::Objects));
        }
        let mut inst = Instance {
            module,
            types: Vec::new(),
            funcs: Vec::new(),
            tables: Vec::new(),
            memories: Vec::new(),
            globals: Vec::new(),
            elements: Vec::new(),
            data: Vec::new(),
        };
        reserve::<A, _>(&mut inst.funcs, inst.module.env().func_types().len())?;
        reserve::<A, _>(&mut inst.tables, inst.module.env().table_types().len())?;
        reserve::<A, _>(&mut inst.memories, inst.module.env().mem_types().len())?;
        reserve::<A, _>(&mut inst.globals, inst.module.env().global_types().len())?;
        i = 0;
        while i < imports.len() && status.is_ok() {
            status = self.link_import(&mut inst, i, imports[i]);
            i += 1;
        }
        status?;
        let identity = InstanceAddr {
            store: self.id,
            index: self.instances.len(),
        };
        reserve::<A, _>(&mut inst.types, inst.module.env().types().len())?;
        i = 0;
        while i < inst.module.env().types().len() && status.is_ok() {
            status = self.add_instance_type::<A>(&mut inst, i);
            i += 1;
        }
        status?;
        i = 0;
        while i < inst.module.env().func_type_indices().len() && status.is_ok() {
            status = self.add_instance_function::<A>(&mut inst, identity.index, i);
            i += 1;
        }
        status?;
        i = inst.tables.len();
        while i < inst.module.env().table_types().len() && status.is_ok() {
            status = self.add_instance_table::<A>(&mut inst, i);
            i += 1;
        }
        status?;
        i = inst.memories.len();
        while i < inst.module.env().mem_types().len() && status.is_ok() {
            status = self.add_instance_memory::<A>(&mut inst, i);
            i += 1;
        }
        status?;
        i = 0;
        reserve::<A, _>(&mut self.instances, 1)?;
        self.instances.push(inst);
        while i < self.instances[identity.index].module.env().globals().len() && status.is_ok() {
            status = self.add_instance_global::<P, F, A>(platform, identity.index, i);
            i += 1;
        }
        status?;
        let element_count = self.instances[identity.index].module.env().elements().len();
        reserve::<A, _>(&mut self.instances[identity.index].elements, element_count)?;
        i = 0;
        while i < self.instances[identity.index].module.env().elements().len() && status.is_ok() {
            status = self.add_instance_element::<P, F, A>(platform, identity.index, i);
            i += 1;
        }
        status?;
        let data_count = self.instances[identity.index].module.tail().data.len();
        reserve::<A, _>(&mut self.instances[identity.index].data, data_count)?;
        i = 0;
        while i < self.instances[identity.index].module.tail().data.len() && status.is_ok() {
            status = self.add_instance_data::<A>(identity.index, i);
            i += 1;
        }
        status?;
        if wasm1(self.instances[identity.index].module.profile()) {
            i = 0;
            while i < self.instances[identity.index].module.env().elements().len() && status.is_ok()
            {
                status = match self.element_range_for::<P, F, A>(platform, identity.index, i) {
                    Ok(_) => Ok(()),
                    Err(e) => Err(e),
                };
                i += 1;
            }
            status?;
            i = 0;
            while i < self.instances[identity.index].module.tail().data.len() && status.is_ok() {
                status = match self.data_range_for::<P, F, A>(platform, identity.index, i) {
                    Ok(_) => Ok(()),
                    Err(e) => Err(e),
                };
                i += 1;
            }
            status?;
        }
        *committed = true;
        self.instance_items += items;
        initialize_segments::<M, P, F, A>(self, platform, identity.index)?;
        if let Some(f) = self.instances[identity.index].module.env().start() {
            let func = self.instances[identity.index].funcs[f as usize];
            let mut execution = Execution::new();
            let mut results = Vec::new();
            interp::invoke_with::<M, P, F, A>(
                &mut execution,
                self,
                platform,
                func,
                &[],
                &mut results,
            )?;
        }
        Ok(identity)
    }
    fn link_import(
        &mut self,
        inst: &mut Instance,
        i: usize,
        import: Extern,
    ) -> Result<(), ExecError> {
        let incompatible = ExecError::Link(LinkError::IncompatibleImportType);
        match (inst.module.env().imports()[i].desc, import) {
            (ImportDesc::Func(t), Extern::Func(a)) => {
                self.check(a.store)?;
                if !same_func_type(
                    &self.types[self.funcs[a.index].signature],
                    &inst.module.env().types()[t as usize],
                ) {
                    return Err(incompatible);
                }
                inst.funcs.push(a);
            }
            (ImportDesc::Table(t), Extern::Table(a)) => {
                self.check(a.store)?;
                let v = &self.tables[a.index];
                if t.elem.value_type() != v.ty.value_type()
                    || !matches_limits(v.elements.len() as u64, v.maximum, t.limits)
                {
                    return Err(incompatible);
                }
                inst.tables.push(a);
            }
            (ImportDesc::Memory(t), Extern::Memory(a)) => {
                self.check(a.store)?;
                let v = &self.memories[a.index];
                if !matches_limits((v.buf.bytes().len() / 65536) as u64, v.maximum, t.limits) {
                    return Err(incompatible);
                }
                inst.memories.push(a);
            }
            (ImportDesc::Global(t), Extern::Global(a)) => {
                self.check(a.store)?;
                if self.globals[a.index].ty.valtype != t.valtype
                    || self.globals[a.index].ty.mutability != t.mutability
                {
                    return Err(incompatible);
                }
                inst.globals.push(a);
            }
            _ => return Err(incompatible),
        }
        Ok(())
    }
    fn add_instance_type<A: Alloc>(
        &mut self,
        inst: &mut Instance,
        i: usize,
    ) -> Result<(), ExecError> {
        inst.types
            .push(self.intern_type::<A>(&inst.module.env().types()[i])?);
        Ok(())
    }
    fn add_instance_function<A: Alloc>(
        &mut self,
        inst: &mut Instance,
        instance: usize,
        i: usize,
    ) -> Result<(), ExecError> {
        self.room()?;
        reserve::<A, _>(&mut self.funcs, 1)?;
        let a = FuncAddr {
            store: self.id,
            index: self.funcs.len(),
        };
        self.funcs.push(Function {
            signature: inst.types[inst.module.env().func_type_indices()[i] as usize],
            code: FunctionCode::Wasm {
                instance: instance,
                function: i,
            },
        });
        inst.funcs.push(a);
        Ok(())
    }
    fn add_instance_table<A: Alloc>(
        &mut self,
        inst: &mut Instance,
        i: usize,
    ) -> Result<(), ExecError> {
        inst.tables
            .push(self.define_table_with::<A>(inst.module.env().table_types()[i])?);
        Ok(())
    }
    fn add_instance_memory<A: Alloc>(
        &mut self,
        inst: &mut Instance,
        i: usize,
    ) -> Result<(), ExecError> {
        let ty = inst.module.env().mem_types()[i];
        let n = ty.limits.min as u64 * 65536;
        if n > usize::MAX as u64
            || !within(self.memory_bytes, n as usize, self.limits.max_memory_bytes)
        {
            return Err(ExecError::Exhausted(ResourceLimit::Allocation));
        }
        let buf = match M::new_zeroed(n as usize) {
            Some(b) => b,
            None => return Err(ExecError::Exhausted(ResourceLimit::Allocation)),
        };
        inst.memories.push(self.define_memory_with::<A>(ty, buf)?);
        Ok(())
    }
    fn add_instance_global<P: Platform<M>, F: FloatOps, A: Alloc>(
        &mut self,
        platform: &mut P,
        instance: usize,
        i: usize,
    ) -> Result<(), ExecError> {
        let g = self.instances[instance].module.env().globals()[i];
        let initializer = self.instances[instance].module.global_initializers[i];
        let v =
            eval_const_exec::<M, P, F, A>(self, platform, instance, initializer, g.gtype.valtype)?;
        let addr = self.define_global_with::<A>(g.gtype, v)?;
        self.instances[instance].globals.push(addr);
        Ok(())
    }
    fn add_instance_element<P: Platform<M>, F: FloatOps, A: Alloc>(
        &mut self,
        platform: &mut P,
        instance: usize,
        i: usize,
    ) -> Result<(), ExecError> {
        let segment_len = self.instances[instance].module.env().elements()[i]
            .init
            .len();
        let mut values = Vec::new();
        reserve::<A, _>(&mut values, segment_len)?;
        let mut j = 0;
        let mut status = Ok(());
        while j < segment_len && status.is_ok() {
            let initializer = self.instances[instance].module.element_initializers[i][j];
            let ty = self.instances[instance].module.env().elements()[i]
                .elem
                .value_type();
            match eval_const_exec::<M, P, F, A>(self, platform, instance, initializer, ty) {
                Ok(v) => values.push(value::encode(v).0),
                Err(e) => status = Err(e),
            }
            j += 1;
        }
        status?;
        reserve::<A, _>(&mut self.elems, 1)?;
        let address = self.elems.len();
        self.elems.push(ElemInstance {
            ty: self.instances[instance].module.env().elements()[i].elem,
            refs: values,
        });
        self.instances[instance].elements.push(address);
        Ok(())
    }
    fn add_instance_data<A: Alloc>(&mut self, instance: usize, i: usize) -> Result<(), ExecError> {
        let source = &self.instances[instance].module.tail().data[i].init;
        let bytes = copy_bytes::<A>(source)?;
        reserve::<A, _>(&mut self.datas, 1)?;
        let address = self.datas.len();
        self.datas.push(DataInstance { bytes });
        self.instances[instance].data.push(address);
        Ok(())
    }
    fn element_range_for<P: Platform<M>, F: FloatOps, A: Alloc>(
        &mut self,
        platform: &mut P,
        instance: usize,
        index: usize,
    ) -> Result<Option<core::ops::Range<usize>>, ExecError> {
        let mode = self.instances[instance].module.env().elements()[index].mode;
        match mode {
            ElementMode::Active { table_idx, .. } => {
                let initializer = match self.instances[instance].module.element_offsets[index] {
                    Some(i) => i,
                    None => return Err(ExecError::BadArguments),
                };
                let start = eval_const_exec::<M, P, F, A>(
                    self,
                    platform,
                    instance,
                    initializer,
                    ValueType::I32,
                )?
                .i32()?;
                let len = self.instances[instance].module.env().elements()[index]
                    .init
                    .len();
                let table = self.instances[instance].tables[table_idx as usize].index;
                Ok(Some(range(
                    start as u64,
                    len as u64,
                    self.tables[table].elements.len(),
                    Trap::TableOutOfBounds,
                )?))
            }
            _ => Ok(None),
        }
    }
    fn data_range_for<P: Platform<M>, F: FloatOps, A: Alloc>(
        &mut self,
        platform: &mut P,
        instance: usize,
        index: usize,
    ) -> Result<Option<core::ops::Range<usize>>, ExecError> {
        let mode = self.instances[instance].module.tail().data[index].mode;
        match mode {
            DataMode::Active { memory_idx, .. } => {
                let initializer = match self.instances[instance].module.data_offsets[index] {
                    Some(i) => i,
                    None => return Err(ExecError::BadArguments),
                };
                let start = eval_const_exec::<M, P, F, A>(
                    self,
                    platform,
                    instance,
                    initializer,
                    ValueType::I32,
                )?
                .i32()?;
                let len = self.instances[instance].module.tail().data[index]
                    .init
                    .len();
                let memory = self.instances[instance].memories[memory_idx as usize].index;
                Ok(Some(range(
                    start as u64,
                    len as u64,
                    self.memories[memory].buf.bytes().len(),
                    Trap::MemoryOutOfBounds,
                )?))
            }
            _ => Ok(None),
        }
    }
}

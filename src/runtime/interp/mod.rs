//! Generic slot interpreter and synchronous call boundary.
use super::bytecode::Instr;
use super::platform::Alloc;
use super::store::FuncCode;
use super::*;

mod bulk;
pub(crate) mod float;
pub(crate) mod int;
mod memory;
pub(crate) mod simd;

struct Frame {
    instance: usize,
    function: usize,
    pc: u32,
    base: usize,
}
/// Reusable invocation storage. No frame or memory borrow survives a host call.
pub struct Execution {
    store: usize,
    slots: Vec<u64>,
    frames: Vec<Frame>,
    host_args: Vec<Value>,
    host_results: Vec<Value>,
}
impl Default for Execution {
    fn default() -> Self {
        Self::new()
    }
}
impl Execution {
    /// Creates empty execution storage, reusable across synchronous invocations.
    pub fn new() -> Self {
        Self {
            store: 0,
            slots: Vec::new(),
            frames: Vec::new(),
            host_args: Vec::new(),
            host_results: Vec::new(),
        }
    }
    /// Returns the complete-module byte offset of the current instruction.
    pub fn source_offset<M: MemoryBuffer>(
        &self,
        store: &Store<M>,
    ) -> Result<Option<usize>, ExecError> {
        if self.frames.len() == 0 {
            return Ok(None);
        }
        store.check(self.store)?;
        let f = &self.frames[self.frames.len() - 1];
        let code = &store.instances[f.instance].module.functions[f.function];
        let pc = if f.pc == 0 { 0 } else { f.pc - 1 };
        if (pc as usize) < code.source_offsets.len() {
            Ok(Some(code.source_offsets[pc as usize]))
        } else {
            Ok(None)
        }
    }
    fn ensure<A: Alloc>(&mut self, end: usize, limit: usize) -> Result<(), ExecError> {
        if end > limit {
            return Err(ExecError::Exhausted(ResourceLimit::Values));
        }
        if end > self.slots.len() {
            let n = end - self.slots.len();
            reserve::<A, _>(&mut self.slots, n)?;
            while self.slots.len() < end {
                self.slots.push(0);
            }
        }
        Ok(())
    }
}
fn interrupt<M: MemoryBuffer, P: Platform<M>>(platform: &mut P) -> Result<(), ExecError> {
    match platform.interrupt() {
        InterruptAction::Continue => Ok(()),
        InterruptAction::Terminate => Err(ExecError::Terminated),
    }
}
fn check_values<M: MemoryBuffer>(
    store: &Store<M>,
    values: &[Value],
    types: &[ValueType],
) -> Result<(), ExecError> {
    if values.len() != types.len() {
        return Err(ExecError::BadArguments);
    }
    let mut i = 0;
    let mut status = Ok(());
    while i < values.len() && status.is_ok() {
        status = store.check_value(values[i]);
        if status.is_ok() && values[i].value_type() != types[i] {
            status = Err(ExecError::BadArguments);
        }
        i += 1;
    }
    status
}
fn check_failed(result: Result<(), ExecError>) -> bool {
    match result {
        Ok(()) => false,
        Err(_) => true,
    }
}
fn encode_slot(slots: &mut [u64], position: usize, ty: ValueType, value: Value) {
    let (lo, hi) = value::encode(value);
    slots[position] = lo;
    if value::width(ty) == 2 {
        slots[position + 1] = hi;
    }
}
fn decode_slot(slots: &[u64], position: usize, ty: ValueType, store: usize) -> Value {
    let hi = if value::width(ty) == 2 {
        slots[position + 1]
    } else {
        0
    };
    value::decode(ty, slots[position], hi, store)
}
fn type_slots(types: &[ValueType]) -> Result<usize, ExecError> {
    value::type_slots(types).ok_or(ExecError::Exhausted(ResourceLimit::Values))
}
pub(crate) fn invoke_with<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    platform: &mut P,
    func: FuncAddr,
    args: &[Value],
    results: &mut Vec<Value>,
) -> Result<(), ExecError> {
    let ty = store.func_type(func)?;
    check_values(store, args, &ty.params)?;
    let needed = type_slots(&ty.params)?.max(type_slots(&ty.results)?);
    exec.ensure::<A>(needed, store.limits.max_values)?;
    clear(&mut exec.frames);
    exec.store = store.id;
    let mut i = 0;
    let mut slot = 0;
    while i < args.len() {
        encode_slot(&mut exec.slots, slot, ty.params[i], args[i]);
        slot += value::width(ty.params[i]) as usize;
        i += 1;
    }
    call::<M, P, F, A>(exec, store, platform, func, 0)?;
    let mut status = Ok(());
    while exec.frames.len() > 0 && status.is_ok() {
        status = step::<M, P, F, A>(exec, store, platform);
    }
    status?;
    let ty = store.func_type(func)?;
    reserve::<A, _>(results, ty.results.len().saturating_sub(results.len()))?;
    clear(results);
    i = 0;
    slot = 0;
    while i < ty.results.len() {
        let t = ty.results[i];
        let value = decode_slot(&exec.slots, slot, t, store.id);
        results.push(value);
        slot += value::width(t) as usize;
        i += 1;
    }
    Ok(())
}
fn call<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    platform: &mut P,
    func: FuncAddr,
    base: usize,
) -> Result<(), ExecError> {
    interrupt::<M, P>(platform)?;
    match store.funcs[func.index].code {
        FuncCode::Wasm { instance, function } => {
            if exec.frames.len() >= store.limits.max_frames {
                return Err(ExecError::Exhausted(ResourceLimit::CallStack));
            }
            let code = &store.instances[instance].module.functions[function];
            let end = match base.checked_add(code.slot_count as usize) {
                Some(n) => n,
                None => return Err(ExecError::Exhausted(ResourceLimit::Values)),
            };
            exec.ensure::<A>(end, store.limits.max_values)?;
            let mut i = base + code.param_slots as usize;
            while i < base + code.local_slots as usize {
                exec.slots[i] = 0;
                i += 1;
            }
            reserve::<A, _>(&mut exec.frames, 1)?;
            exec.frames.push(Frame {
                instance,
                function,
                pc: 0,
                base,
            });
        }
        FuncCode::Host(id) => {
            let ty = &store.types[store.funcs[func.index].signature];
            let size = type_slots(&ty.results)?.max(type_slots(&ty.params)?);
            let end = match base.checked_add(size) {
                Some(n) => n,
                None => return Err(ExecError::Exhausted(ResourceLimit::Values)),
            };
            exec.ensure::<A>(end, store.limits.max_values)?;
            let args_add = ty.params.len().saturating_sub(exec.host_args.len());
            reserve::<A, _>(&mut exec.host_args, args_add)?;
            let results_add = ty.results.len().saturating_sub(exec.host_results.len());
            reserve::<A, _>(&mut exec.host_results, results_add)?;
            clear(&mut exec.host_args);
            clear(&mut exec.host_results);
            let mut i = 0;
            let mut pos = base;
            while i < ty.params.len() {
                let t = ty.params[i];
                let value = decode_slot(&exec.slots, pos, t, store.id);
                exec.host_args.push(value);
                pos += value::width(t) as usize;
                i += 1;
            }
            i = 0;
            while i < ty.results.len() {
                exec.host_results.push(Value::zero(ty.results[i]));
                i += 1;
            }
            match platform.call_host(store, id, &exec.host_args, &mut exec.host_results) {
                Ok(()) => {}
                Err(HostError::Trap) => return Err(ExecError::Trap(Trap::Host)),
                Err(HostError::StackOverflow) => {
                    return Err(ExecError::Exhausted(ResourceLimit::CallStack))
                }
            }
            let ty = &store.types[store.funcs[func.index].signature];
            // A callback cannot turn a malformed result into API argument rejection.
            if check_failed(check_values(store, &exec.host_results, &ty.results)) {
                return Err(ExecError::Trap(Trap::Host));
            }
            i = 0;
            pos = base;
            while i < ty.results.len() {
                let value = exec.host_results[i];
                encode_slot(&mut exec.slots, pos, ty.results[i], value);
                pos += value::width(ty.results[i]) as usize;
                i += 1;
            }
        }
    }
    Ok(())
}
fn copy(slots: &mut [u64], dst: usize, src: usize, n: usize) {
    let mut i = 0;
    while i < n {
        slots[dst + i] = slots[src + i];
        i += 1;
    }
}
fn get(slots: &[u64], pos: usize) -> u64 {
    if pos < slots.len() {
        slots[pos]
    } else {
        0
    }
}
fn vector(slots: &[u64], pos: usize) -> u128 {
    get(slots, pos) as u128 | ((get(slots, pos + 1) as u128) << 64)
}
#[inline(always)]
fn step<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    platform: &mut P,
) -> Result<(), ExecError> {
    let frame_index = exec.frames.len() - 1;
    let frame = &exec.frames[frame_index];
    let inst = frame.instance;
    let function = frame.function;
    let base = frame.base;
    let pc = frame.pc;
    let instruction = store.instances[inst].module.functions[function].code[pc as usize];
    exec.frames[frame_index].pc = match pc.checked_add(1) {
        Some(next) => next,
        None => return Err(ExecError::Internal),
    };
    dispatch::<M, P, F, A>(
        exec,
        store,
        platform,
        frame_index,
        inst,
        function,
        base,
        instruction,
    )
}

#[inline(always)]
fn execute_scalar<F: FloatOps>(
    exec: &mut Execution,
    base: usize,
    op: u16,
    dst: u32,
    a: u32,
    b: u32,
) -> Result<(), ExecError> {
    let result = int::scalar::<F>(
        op,
        exec.slots[base + a as usize],
        exec.slots[base + b as usize],
    )?;
    exec.slots[base + dst as usize] = result;
    Ok(())
}
#[inline(always)]
fn execute_load<M: MemoryBuffer>(
    exec: &mut Execution,
    store: &Store<M>,
    inst: usize,
    base: usize,
    op: u16,
    dst: u32,
    addr: u32,
    offset: u32,
) -> Result<(), ExecError> {
    let m = store.instances[inst].memories[0].index;
    let result = memory::load(
        op,
        exec.slots[base + addr as usize] as u32,
        offset,
        store.memories[m].buf.bytes(),
    )?;
    exec.slots[base + dst as usize] = result;
    Ok(())
}
#[inline(always)]
fn execute_store<M: MemoryBuffer>(
    exec: &Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    op: u16,
    addr: u32,
    value: u32,
    offset: u32,
) -> Result<(), ExecError> {
    let m = store.instances[inst].memories[0].index;
    memory::store(
        op,
        exec.slots[base + addr as usize] as u32,
        offset,
        exec.slots[base + value as usize],
        store.memories[m].buf.bytes_mut(),
    )
}
#[inline(always)]
fn execute_simd<M: MemoryBuffer, F: FloatOps>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    function: usize,
    base: usize,
    op: u32,
    dst: u32,
    a: u32,
    entry: u32,
) -> Result<(), ExecError> {
    let imm = store.instances[inst].module.functions[function].simd[entry as usize];
    let shape = match super::bytecode::simd_shape(op) {
        Some(s) => s,
        None => return Err(ExecError::Internal),
    };
    let pos = base + a as usize;
    let x = if shape.0 == 2 {
        vector(&exec.slots, pos)
    } else {
        get(&exec.slots, pos) as u128
    };
    let y_pos = pos + shape.0 as usize;
    let y = if shape.1 == 2 {
        vector(&exec.slots, y_pos)
    } else {
        get(&exec.slots, y_pos) as u128
    };
    let z_pos = y_pos + shape.1 as usize;
    let z = if shape.2 == 2 {
        vector(&exec.slots, z_pos)
    } else {
        get(&exec.slots, z_pos) as u128
    };
    let result = if store.instances[inst].memories.len() > 0 {
        let m = store.instances[inst].memories[0].index;
        simd::simd::<F>(
            op,
            imm.offset,
            imm.lane,
            imm.bits,
            x,
            y,
            z,
            Some(store.memories[m].buf.bytes_mut()),
        )?
    } else {
        simd::simd::<F>(op, imm.offset, imm.lane, imm.bits, x, y, z, None)?
    };
    if shape.3 > 0 {
        exec.slots[base + dst as usize] = result as u64;
    }
    if shape.3 == 2 {
        exec.slots[base + dst as usize + 1] = (result >> 64) as u64;
    }
    Ok(())
}

#[inline(always)]
fn execute_copy(exec: &mut Execution, base: usize, dst: u32, src: u32) -> Result<(), ExecError> {
    exec.slots[base + dst as usize] = exec.slots[base + src as usize];
    Ok(())
}

#[inline(always)]
fn execute_copy2(exec: &mut Execution, base: usize, dst: u32, src: u32) -> Result<(), ExecError> {
    copy(&mut exec.slots, base + dst as usize, base + src as usize, 2);
    Ok(())
}

#[inline(always)]
fn execute_copy_n(
    exec: &mut Execution,
    base: usize,
    dst: u32,
    src: u32,
    n: u32,
) -> Result<(), ExecError> {
    copy(
        &mut exec.slots,
        base + dst as usize,
        base + src as usize,
        n as usize,
    );
    Ok(())
}

#[inline(always)]
fn execute_const32(
    exec: &mut Execution,
    base: usize,
    dst: u32,
    value: u32,
) -> Result<(), ExecError> {
    exec.slots[base + dst as usize] = value as u64;
    Ok(())
}

#[inline(always)]
fn execute_const64(
    exec: &mut Execution,
    base: usize,
    dst: u32,
    value: u64,
) -> Result<(), ExecError> {
    exec.slots[base + dst as usize] = value;
    Ok(())
}

#[inline(always)]
fn execute_const_v128<M: MemoryBuffer>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    function: usize,
    base: usize,
    dst: u32,
    pool: u32,
) -> Result<(), ExecError> {
    let v = store.instances[inst].module.functions[function].v128_pool[pool as usize];
    exec.slots[base + dst as usize] = v as u64;
    exec.slots[base + dst as usize + 1] = (v >> 64) as u64;
    Ok(())
}

#[inline(always)]
fn execute_jump(exec: &mut Execution, frame_index: usize, target: u32) -> Result<(), ExecError> {
    exec.frames[frame_index].pc = target;
    Ok(())
}

#[inline(always)]
fn execute_jump_if_zero(
    exec: &mut Execution,
    frame_index: usize,
    base: usize,
    cond: u32,
    target: u32,
) -> Result<(), ExecError> {
    if exec.slots[base + cond as usize] as u32 == 0 {
        exec.frames[frame_index].pc = target;
    }
    Ok(())
}

#[inline(always)]
fn execute_jump_if_non_zero(
    exec: &mut Execution,
    frame_index: usize,
    base: usize,
    cond: u32,
    target: u32,
) -> Result<(), ExecError> {
    if exec.slots[base + cond as usize] as u32 != 0 {
        exec.frames[frame_index].pc = target;
    }
    Ok(())
}

#[inline(always)]
fn execute_jump_table<M: MemoryBuffer>(
    exec: &mut Execution,
    store: &mut Store<M>,
    frame_index: usize,
    inst: usize,
    function: usize,
    base: usize,
    index: u32,
    start: u32,
    len: u32,
) -> Result<(), ExecError> {
    let index = exec.slots[base + index as usize] as u32;
    let selected = if index < len - 1 { index } else { len - 1 };
    let target =
        store.instances[inst].module.functions[function].jump_tables[(start + selected) as usize];
    exec.frames[frame_index].pc = target;
    Ok(())
}

#[inline(always)]
fn execute_loop_head<M: MemoryBuffer, P: Platform<M>>(platform: &mut P) -> Result<(), ExecError> {
    interrupt::<M, P>(platform)
}

#[inline(always)]
fn execute_call<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    platform: &mut P,
    inst: usize,
    base: usize,
    func: u32,
    callee: u32,
) -> Result<(), ExecError> {
    let addr = store.instances[inst].funcs[func as usize];
    call::<M, P, F, A>(exec, store, platform, addr, base + callee as usize)
}

#[inline(always)]
fn execute_call_indirect<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    platform: &mut P,
    inst: usize,
    function: usize,
    base: usize,
    entry: u32,
    index: u32,
    callee: u32,
) -> Result<(), ExecError> {
    let (table, ty) = store.instances[inst].module.functions[function].indirect[entry as usize];
    let t = store.instances[inst].tables[table as usize].index;
    let i = exec.slots[base + index as usize] as u32 as usize;
    if i >= store.tables[t].elements.len() {
        return Err(Trap::TableOutOfBounds.into());
    }
    let reference = store.tables[t].elements[i];
    if reference == 0 {
        return Err(Trap::UninitializedElement.into());
    }
    let f = reference as usize - 1;
    if store.funcs[f].signature != store.instances[inst].types[ty as usize] {
        return Err(Trap::IndirectCallTypeMismatch.into());
    }
    call::<M, P, F, A>(
        exec,
        store,
        platform,
        FuncAddr {
            store: store.id,
            index: f,
        },
        base + callee as usize,
    )
}

#[inline(always)]
fn execute_return(exec: &mut Execution, base: usize, src: u32, n: u32) -> Result<(), ExecError> {
    copy(&mut exec.slots, base, base + src as usize, n as usize);
    exec.frames.pop();
    Ok(())
}

#[inline(always)]
fn execute_unreachable() -> Result<(), ExecError> {
    Err(Trap::Unreachable.into())
}

#[inline(always)]
fn execute_select(
    exec: &mut Execution,
    base: usize,
    a: u32,
    b: u32,
    cond: u32,
) -> Result<(), ExecError> {
    if exec.slots[base + cond as usize] as u32 == 0 {
        exec.slots[base + a as usize] = exec.slots[base + b as usize];
    }
    Ok(())
}

#[inline(always)]
fn execute_select2(
    exec: &mut Execution,
    base: usize,
    a: u32,
    b: u32,
    cond: u32,
) -> Result<(), ExecError> {
    if exec.slots[base + cond as usize] as u32 == 0 {
        copy(&mut exec.slots, base + a as usize, base + b as usize, 2);
    }
    Ok(())
}

#[inline(always)]
fn execute_global_get<M: MemoryBuffer>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    dst: u32,
    global: u32,
) -> Result<(), ExecError> {
    let g = &store.globals[store.instances[inst].globals[global as usize].index];
    exec.slots[base + dst as usize] = g.lo;
    Ok(())
}

#[inline(always)]
fn execute_global_get2<M: MemoryBuffer>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    dst: u32,
    global: u32,
) -> Result<(), ExecError> {
    let g = &store.globals[store.instances[inst].globals[global as usize].index];
    exec.slots[base + dst as usize] = g.lo;
    exec.slots[base + dst as usize + 1] = g.hi;
    Ok(())
}

#[inline(always)]
fn execute_global_set<M: MemoryBuffer>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    src: u32,
    global: u32,
) -> Result<(), ExecError> {
    let g = &mut store.globals[store.instances[inst].globals[global as usize].index];
    g.lo = exec.slots[base + src as usize];
    Ok(())
}

#[inline(always)]
fn execute_global_set2<M: MemoryBuffer>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    src: u32,
    global: u32,
) -> Result<(), ExecError> {
    let g = &mut store.globals[store.instances[inst].globals[global as usize].index];
    g.lo = exec.slots[base + src as usize];
    g.hi = exec.slots[base + src as usize + 1];
    Ok(())
}

#[inline(always)]
fn execute_memory_size<M: MemoryBuffer>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    dst: u32,
) -> Result<(), ExecError> {
    let m = store.instances[inst].memories[0].index;
    exec.slots[base + dst as usize] = (store.memories[m].buf.bytes().len() / 65536) as u64;
    Ok(())
}

#[inline(always)]
fn execute_memory_grow<M: MemoryBuffer>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    dst: u32,
) -> Result<(), ExecError> {
    let m = store.instances[inst].memories[0].index;
    exec.slots[base + dst as usize] =
        store.grow_memory_index(m, exec.slots[base + dst as usize] as u32) as u64;
    Ok(())
}

#[inline(always)]
fn execute_ref_null(exec: &mut Execution, base: usize, dst: u32) -> Result<(), ExecError> {
    exec.slots[base + dst as usize] = 0;
    Ok(())
}

#[inline(always)]
fn execute_ref_is_null(
    exec: &mut Execution,
    base: usize,
    dst: u32,
    a: u32,
) -> Result<(), ExecError> {
    exec.slots[base + dst as usize] = if exec.slots[base + a as usize] == 0 {
        1
    } else {
        0
    };
    Ok(())
}

#[inline(always)]
fn execute_ref_func<M: MemoryBuffer>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    dst: u32,
    func: u32,
) -> Result<(), ExecError> {
    exec.slots[base + dst as usize] =
        match (store.instances[inst].funcs[func as usize].index as u64).checked_add(1) {
            Some(reference) => reference,
            None => return Err(ExecError::Internal),
        };
    Ok(())
}

#[inline(always)]
fn execute_table_get<M: MemoryBuffer>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    dst: u32,
    index: u32,
    table: u32,
) -> Result<(), ExecError> {
    let t = store.instances[inst].tables[table as usize].index;
    let i = exec.slots[base + index as usize] as u32 as usize;
    if i >= store.tables[t].elements.len() {
        return Err(Trap::TableOutOfBounds.into());
    }
    exec.slots[base + dst as usize] = store.tables[t].elements[i];
    Ok(())
}

#[inline(always)]
fn execute_table_set<M: MemoryBuffer>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    index: u32,
    value: u32,
    table: u32,
) -> Result<(), ExecError> {
    let t = store.instances[inst].tables[table as usize].index;
    let i = exec.slots[base + index as usize] as u32 as usize;
    if i >= store.tables[t].elements.len() {
        return Err(Trap::TableOutOfBounds.into());
    }
    store.tables[t].elements[i] = exec.slots[base + value as usize];
    Ok(())
}

#[inline(always)]
fn execute_table_size<M: MemoryBuffer>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    dst: u32,
    table: u32,
) -> Result<(), ExecError> {
    let t = store.instances[inst].tables[table as usize].index;
    exec.slots[base + dst as usize] = store.tables[t].elements.len() as u64;
    Ok(())
}

#[inline(always)]
fn execute_table_grow<M: MemoryBuffer, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    dst: u32,
    table: u32,
) -> Result<(), ExecError> {
    let t = store.instances[inst].tables[table as usize].index;
    let v = exec.slots[base + dst as usize];
    let delta = exec.slots[base + dst as usize + 1] as u32;
    exec.slots[base + dst as usize] = store.grow_table_index::<A>(t, delta, v) as u64;
    Ok(())
}

#[inline(always)]
fn execute_bulk<M: MemoryBuffer>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    function: usize,
    base: usize,
    instruction: Instr,
) -> Result<(), ExecError> {
    bulk::execute(store, inst, function, base, &exec.slots, instruction)
}

macro_rules! define_dispatch {
    (scalar {$($scalar:ident = $scalar_op:expr;)*}
     load {$($load:ident = $load_op:expr;)*}
     store {$($store:ident = $store_op:expr;)*}
     simd {$($simd:ident = $simd_op:expr;)*}) => {
        #[inline(always)]
        fn scalar_operands(instruction: Instr) -> (u32, u32, u32) {
            match instruction {
                $(Instr::$scalar { dst, a, b })|* => (dst, a, b),
                _ => (0, 0, 0),
            }
        }
        #[inline(always)]
        fn load_operands(instruction: Instr) -> (u32, u32, u32) {
            match instruction {
                $(Instr::$load { dst, addr, offset })|* => (dst, addr, offset),
                _ => (0, 0, 0),
            }
        }
        #[inline(always)]
        fn store_operands(instruction: Instr) -> (u32, u32, u32) {
            match instruction {
                $(Instr::$store { addr, value, offset })|* => (addr, value, offset),
                _ => (0, 0, 0),
            }
        }
        #[inline(always)]
        fn simd_operands(instruction: Instr) -> (u32, u32, u32) {
            match instruction {
                $(Instr::$simd { dst, a, entry })|* => (dst, a, entry),
                _ => (0, 0, 0),
            }
        }
        #[inline(always)]
        fn dispatch_scalar<F: FloatOps>(
            exec: &mut Execution,
            base: usize,
            op: u16,
            instruction: Instr,
        ) -> Result<(), ExecError> {
            let (dst, a, b) = scalar_operands(instruction);
            execute_scalar::<F>(exec, base, op, dst, a, b)
        }
        #[inline(always)]
        fn dispatch_load<M: MemoryBuffer>(
            exec: &mut Execution,
            store: &Store<M>,
            inst: usize,
            base: usize,
            op: u16,
            instruction: Instr,
        ) -> Result<(), ExecError> {
            let (dst, addr, offset) = load_operands(instruction);
            execute_load(exec, store, inst, base, op, dst, addr, offset)
        }
        #[inline(always)]
        fn dispatch_store<M: MemoryBuffer>(
            exec: &Execution,
            store: &mut Store<M>,
            inst: usize,
            base: usize,
            op: u16,
            instruction: Instr,
        ) -> Result<(), ExecError> {
            let (addr, value, offset) = store_operands(instruction);
            execute_store(exec, store, inst, base, op, addr, value, offset)
        }
        #[inline(always)]
        fn dispatch_simd<M: MemoryBuffer, F: FloatOps>(
            exec: &mut Execution,
            store: &mut Store<M>,
            inst: usize,
            function: usize,
            base: usize,
            op: u32,
            instruction: Instr,
        ) -> Result<(), ExecError> {
            let (dst, a, entry) = simd_operands(instruction);
            execute_simd::<M, F>(exec, store, inst, function, base, op, dst, a, entry)
        }
        #[inline(always)]
        fn dispatch<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
            exec: &mut Execution,
            store: &mut Store<M>,
            platform: &mut P,
            frame_index: usize,
            inst: usize,
            function: usize,
            base: usize,
            instruction: Instr,
        ) -> Result<(), ExecError> {
            match instruction {
                $(Instr::$scalar { .. } => dispatch_scalar::<F>(exec, base, $scalar_op, instruction),)*
                $(Instr::$load { .. } => dispatch_load(exec, store, inst, base, $load_op, instruction),)*
                $(Instr::$store { .. } => dispatch_store(exec, store, inst, base, $store_op, instruction),)*
                $(Instr::$simd { .. } => {
                    dispatch_simd::<M, F>(exec, store, inst, function, base, $simd_op, instruction)
                })*
                Instr::Copy { dst, src } => execute_copy(exec, base, dst, src),
                Instr::Copy2 { dst, src } => execute_copy2(exec, base, dst, src),
                Instr::CopyN { dst, src, n } => execute_copy_n(exec, base, dst, src, n),
                Instr::Const32 { dst, value } => execute_const32(exec, base, dst, value),
                Instr::Const64 { dst, value } => execute_const64(exec, base, dst, value),
                Instr::ConstV128 { dst, pool } => {
                    execute_const_v128(exec, store, inst, function, base, dst, pool)
                }
                Instr::Jump { target } => execute_jump(exec, frame_index, target),
                Instr::JumpIfZero { cond, target } => {
                    execute_jump_if_zero(exec, frame_index, base, cond, target)
                }
                Instr::JumpIfNonZero { cond, target } => {
                    execute_jump_if_non_zero(exec, frame_index, base, cond, target)
                }
                Instr::JumpTable { index, start, len } => execute_jump_table(
                    exec,
                    store,
                    frame_index,
                    inst,
                    function,
                    base,
                    index,
                    start,
                    len,
                ),
                Instr::LoopHead => execute_loop_head::<M, P>(platform),
                Instr::Call { func, base: callee } => {
                    execute_call::<M, P, F, A>(exec, store, platform, inst, base, func, callee)
                }
                Instr::CallIndirect {
                    entry,
                    index,
                    base: callee,
                } => execute_call_indirect::<M, P, F, A>(
                    exec, store, platform, inst, function, base, entry, index, callee,
                ),
                Instr::Return { src, n } => execute_return(exec, base, src, n),
                Instr::Unreachable => execute_unreachable(),
                Instr::Select { a, b, cond } => execute_select(exec, base, a, b, cond),
                Instr::Select2 { a, b, cond } => execute_select2(exec, base, a, b, cond),
                Instr::GlobalGet { dst, global } => {
                    execute_global_get(exec, store, inst, base, dst, global)
                }
                Instr::GlobalGet2 { dst, global } => {
                    execute_global_get2(exec, store, inst, base, dst, global)
                }
                Instr::GlobalSet { src, global } => {
                    execute_global_set(exec, store, inst, base, src, global)
                }
                Instr::GlobalSet2 { src, global } => {
                    execute_global_set2(exec, store, inst, base, src, global)
                }
                Instr::MemorySize { dst } => execute_memory_size(exec, store, inst, base, dst),
                Instr::MemoryGrow { dst } => execute_memory_grow(exec, store, inst, base, dst),
                Instr::RefNull { dst } => execute_ref_null(exec, base, dst),
                Instr::RefIsNull { dst, a } => execute_ref_is_null(exec, base, dst, a),
                Instr::RefFunc { dst, func } => execute_ref_func(exec, store, inst, base, dst, func),
                Instr::TableGet { dst, index, table } => {
                    execute_table_get(exec, store, inst, base, dst, index, table)
                }
                Instr::TableSet {
                    index,
                    value,
                    table,
                } => execute_table_set(exec, store, inst, base, index, value, table),
                Instr::TableSize { dst, table } => {
                    execute_table_size(exec, store, inst, base, dst, table)
                }
                Instr::TableGrow { dst, table } => {
                    execute_table_grow::<M, A>(exec, store, inst, base, dst, table)
                }
                Instr::MemoryFill { .. }
                | Instr::MemoryCopy { .. }
                | Instr::MemoryInit { .. }
                | Instr::DataDrop { .. }
                | Instr::TableFill { .. }
                | Instr::TableCopy { .. }
                | Instr::TableInit { .. }
                | Instr::ElemDrop { .. } => execute_bulk(exec, store, inst, function, base, instruction),
            }
        }
    };
}
super::operators::with_ops!(define_dispatch);

/// Runs compiler-generated initialization code through the ordinary step loop
/// and returns the first two result slots.
fn run_synthetic<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    store: &mut Store<M>,
    platform: &mut P,
    instance: usize,
    function: usize,
) -> Result<(u64, u64), ExecError> {
    let count = store.instances[instance].module.functions[function].slot_count as usize;
    let mut exec = Execution::new();
    exec.store = store.id;
    exec.ensure::<A>(count, store.limits.max_values)?;
    reserve::<A, _>(&mut exec.frames, 1)?;
    exec.frames.push(Frame {
        instance,
        function,
        pc: 0,
        base: 0,
    });
    let mut status = Ok(());
    while exec.frames.len() > 0 && status.is_ok() {
        status = step::<M, P, F, A>(&mut exec, store, platform);
    }
    status?;
    Ok((get(&exec.slots, 0), get(&exec.slots, 1)))
}

/// Evaluates a compiled constant expression of type `ty`.
pub(crate) fn eval_const<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    store: &mut Store<M>,
    platform: &mut P,
    instance: usize,
    function: usize,
    ty: ValueType,
) -> Result<Value, ExecError> {
    let (lo, hi) = run_synthetic::<M, P, F, A>(store, platform, instance, function)?;
    Ok(value::decode(ty, lo, hi, store.id))
}

/// Runs the instance's compiled active-segment writes and segment drops.
pub(crate) fn initialize_segments<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    store: &mut Store<M>,
    platform: &mut P,
    instance: usize,
) -> Result<(), ExecError> {
    let function = store.instances[instance].module.initialization;
    run_synthetic::<M, P, F, A>(store, platform, instance, function)?;
    Ok(())
}

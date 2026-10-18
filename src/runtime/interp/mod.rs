//! Generic slot interpreter and synchronous call boundary.
use super::bytecode::Instr;
use super::platform::Alloc;
use super::store::FunctionCode;
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
    let mut n = 0usize;
    let mut i = 0;
    let mut status = Ok(());
    while i < types.len() && status.is_ok() {
        match n.checked_add(value::width(types[i]) as usize) {
            Some(next) => n = next,
            None => status = Err(ExecError::Exhausted(ResourceLimit::Values)),
        }
        i += 1;
    }
    status?;
    Ok(n)
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
    while exec.frames.len() > 0 {
        exec.frames.pop();
    }
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
    while results.len() > 0 {
        results.pop();
    }
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
        FunctionCode::Wasm { instance, function } => {
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
        FunctionCode::Host(id) => {
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
            while exec.host_args.len() > 0 {
                exec.host_args.pop();
            }
            while exec.host_results.len() > 0 {
                exec.host_results.pop();
            }
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
        None => return Err(ExecError::BadArguments),
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
        None => return Err(ExecError::BadArguments),
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
fn admin_copy<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    base: usize,
    dst: u32,
    src: u32,
) -> Result<(), ExecError> {
    {
        Ok(exec.slots[base + dst as usize] = exec.slots[base + src as usize])
    }
}

#[inline(always)]
fn admin_copy2<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    base: usize,
    dst: u32,
    src: u32,
) -> Result<(), ExecError> {
    {
        Ok(copy(
            &mut exec.slots,
            base + dst as usize,
            base + src as usize,
            2,
        ))
    }
}

#[inline(always)]
fn admin_copy_n<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    base: usize,
    dst: u32,
    src: u32,
    n: u32,
) -> Result<(), ExecError> {
    Ok({
        copy(
            &mut exec.slots,
            base + dst as usize,
            base + src as usize,
            n as usize,
        )
    })
}

#[inline(always)]
fn admin_const32<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    base: usize,
    dst: u32,
    value: u32,
) -> Result<(), ExecError> {
    Ok(exec.slots[base + dst as usize] = value as u64)
}

#[inline(always)]
fn admin_const64<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    base: usize,
    dst: u32,
    value: u64,
) -> Result<(), ExecError> {
    Ok(exec.slots[base + dst as usize] = value)
}

#[inline(always)]
fn admin_const_v128<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    function: usize,
    base: usize,
    dst: u32,
    pool: u32,
) -> Result<(), ExecError> {
    Ok({
        let v = store.instances[inst].module.functions[function].v128_pool[pool as usize];
        exec.slots[base + dst as usize] = v as u64;
        exec.slots[base + dst as usize + 1] = (v >> 64) as u64;
    })
}

#[inline(always)]
fn admin_jump<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    frame_index: usize,
    target: u32,
) -> Result<(), ExecError> {
    Ok(exec.frames[frame_index].pc = target)
}

#[inline(always)]
fn admin_jump_if_zero<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    frame_index: usize,
    base: usize,
    cond: u32,
    target: u32,
) -> Result<(), ExecError> {
    Ok({
        if exec.slots[base + cond as usize] as u32 == 0 {
            exec.frames[frame_index].pc = target;
        }
    })
}

#[inline(always)]
fn admin_jump_if_non_zero<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    frame_index: usize,
    base: usize,
    cond: u32,
    target: u32,
) -> Result<(), ExecError> {
    Ok({
        if exec.slots[base + cond as usize] as u32 != 0 {
            exec.frames[frame_index].pc = target;
        }
    })
}

#[inline(always)]
fn admin_jump_table<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
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
    Ok({
        let index = exec.slots[base + index as usize] as u32;
        let selected = if index < len - 1 { index } else { len - 1 };
        let target = store.instances[inst].module.functions[function].jump_tables
            [(start + selected) as usize];
        exec.frames[frame_index].pc = target;
    })
}

#[inline(always)]
fn admin_loop_head<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    platform: &mut P,
) -> Result<(), ExecError> {
    Ok(interrupt::<M, P>(platform)?)
}

#[inline(always)]
fn admin_call<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    platform: &mut P,
    inst: usize,
    base: usize,
    func: u32,
    callee: u32,
) -> Result<(), ExecError> {
    Ok({
        let addr = store.instances[inst].funcs[func as usize];
        call::<M, P, F, A>(exec, store, platform, addr, base + callee as usize)?;
    })
}

#[inline(always)]
fn admin_call_indirect<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
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
    Ok({
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
        )?;
    })
}

#[inline(always)]
fn admin_return<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    base: usize,
    src: u32,
    n: u32,
) -> Result<(), ExecError> {
    Ok({
        copy(&mut exec.slots, base, base + src as usize, n as usize);
        exec.frames.pop();
    })
}

#[inline(always)]
fn admin_unreachable<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
) -> Result<(), ExecError> {
    Err(Trap::Unreachable.into())
}

#[inline(always)]
fn admin_select<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    base: usize,
    a: u32,
    b: u32,
    cond: u32,
) -> Result<(), ExecError> {
    Ok({
        if exec.slots[base + cond as usize] as u32 == 0 {
            exec.slots[base + a as usize] = exec.slots[base + b as usize];
        }
    })
}

#[inline(always)]
fn admin_select2<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    base: usize,
    a: u32,
    b: u32,
    cond: u32,
) -> Result<(), ExecError> {
    Ok({
        if exec.slots[base + cond as usize] as u32 == 0 {
            copy(&mut exec.slots, base + a as usize, base + b as usize, 2);
        }
    })
}

#[inline(always)]
fn admin_global_get<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    dst: u32,
    global: u32,
) -> Result<(), ExecError> {
    Ok({
        let g = &store.globals[store.instances[inst].globals[global as usize].index];
        exec.slots[base + dst as usize] = g.lo;
    })
}

#[inline(always)]
fn admin_global_get2<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    dst: u32,
    global: u32,
) -> Result<(), ExecError> {
    Ok({
        let g = &store.globals[store.instances[inst].globals[global as usize].index];
        exec.slots[base + dst as usize] = g.lo;
        exec.slots[base + dst as usize + 1] = g.hi;
    })
}

#[inline(always)]
fn admin_global_set<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    src: u32,
    global: u32,
) -> Result<(), ExecError> {
    Ok({
        let g = &mut store.globals[store.instances[inst].globals[global as usize].index];
        g.lo = exec.slots[base + src as usize];
    })
}

#[inline(always)]
fn admin_global_set2<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    src: u32,
    global: u32,
) -> Result<(), ExecError> {
    Ok({
        let g = &mut store.globals[store.instances[inst].globals[global as usize].index];
        g.lo = exec.slots[base + src as usize];
        g.hi = exec.slots[base + src as usize + 1];
    })
}

#[inline(always)]
fn admin_memory_size<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    dst: u32,
) -> Result<(), ExecError> {
    Ok({
        let m = store.instances[inst].memories[0].index;
        exec.slots[base + dst as usize] = (store.memories[m].buf.bytes().len() / 65536) as u64;
    })
}

#[inline(always)]
fn admin_memory_grow<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    dst: u32,
) -> Result<(), ExecError> {
    Ok({
        let m = store.instances[inst].memories[0].index;
        exec.slots[base + dst as usize] =
            store.grow_memory_index(m, exec.slots[base + dst as usize] as u32) as u64;
    })
}

#[inline(always)]
fn admin_ref_null<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    base: usize,
    dst: u32,
) -> Result<(), ExecError> {
    Ok(exec.slots[base + dst as usize] = 0)
}

#[inline(always)]
fn admin_ref_is_null<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    base: usize,
    dst: u32,
    a: u32,
) -> Result<(), ExecError> {
    Ok({
        exec.slots[base + dst as usize] = if exec.slots[base + a as usize] == 0 {
            1
        } else {
            0
        }
    })
}

#[inline(always)]
fn admin_ref_func<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    dst: u32,
    func: u32,
) -> Result<(), ExecError> {
    Ok({
        exec.slots[base + dst as usize] =
            match (store.instances[inst].funcs[func as usize].index as u64).checked_add(1) {
                Some(reference) => reference,
                None => return Err(ExecError::BadArguments),
            }
    })
}

#[inline(always)]
fn admin_table_get<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    dst: u32,
    index: u32,
    table: u32,
) -> Result<(), ExecError> {
    Ok({
        let t = store.instances[inst].tables[table as usize].index;
        let i = exec.slots[base + index as usize] as u32 as usize;
        if i >= store.tables[t].elements.len() {
            return Err(Trap::TableOutOfBounds.into());
        }
        exec.slots[base + dst as usize] = store.tables[t].elements[i];
    })
}

#[inline(always)]
fn admin_table_set<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    index: u32,
    value: u32,
    table: u32,
) -> Result<(), ExecError> {
    Ok({
        let t = store.instances[inst].tables[table as usize].index;
        let i = exec.slots[base + index as usize] as u32 as usize;
        if i >= store.tables[t].elements.len() {
            return Err(Trap::TableOutOfBounds.into());
        }
        store.tables[t].elements[i] = exec.slots[base + value as usize];
    })
}

#[inline(always)]
fn admin_table_size<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    dst: u32,
    table: u32,
) -> Result<(), ExecError> {
    Ok({
        let t = store.instances[inst].tables[table as usize].index;
        exec.slots[base + dst as usize] = store.tables[t].elements.len() as u64;
    })
}

#[inline(always)]
fn admin_table_grow<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    base: usize,
    dst: u32,
    table: u32,
) -> Result<(), ExecError> {
    Ok({
        let t = store.instances[inst].tables[table as usize].index;
        let v = exec.slots[base + dst as usize];
        let delta = exec.slots[base + dst as usize + 1] as u32;
        exec.slots[base + dst as usize] = store.grow_table_index::<A>(t, delta, v) as u64;
    })
}

#[inline(always)]
fn admin_memory_fill<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    exec: &mut Execution,
    store: &mut Store<M>,
    inst: usize,
    function: usize,
    base: usize,
    instruction: Instr,
) -> Result<(), ExecError> {
    {
        Ok(bulk::execute(
            store,
            inst,
            function,
            base,
            &exec.slots,
            instruction,
        )?)
    }
}

macro_rules! define_step {
    (scalar {$($scalar:ident = $scalar_op:expr;)*}
     load {$($load:ident = $load_op:expr;)*}
     store {$($store:ident = $store_op:expr;)*}
     simd {$($simd:ident = $simd_op:expr;)*}) => {
#[inline(always)]
fn scalar_operands(instruction: Instr) -> (u32, u32, u32) {
    match instruction { $(Instr::$scalar {dst,a,b})|* => (dst,a,b), _ => (0,0,0) }
}
#[inline(always)]
fn load_operands(instruction: Instr) -> (u32, u32, u32) {
    match instruction { $(Instr::$load {dst,addr,offset})|* => (dst,addr,offset), _ => (0,0,0) }
}
#[inline(always)]
fn store_operands(instruction: Instr) -> (u32, u32, u32) {
    match instruction { $(Instr::$store {addr,value,offset})|* => (addr,value,offset), _ => (0,0,0) }
}
#[inline(always)]
fn simd_operands(instruction: Instr) -> (u32, u32, u32) {
    match instruction { $(Instr::$simd {dst,a,entry})|* => (dst,a,entry), _ => (0,0,0) }
}
#[inline(always)]
fn dispatch_scalar<F: FloatOps>(exec: &mut Execution, base: usize, op: u16, instruction: Instr) -> Result<(), ExecError> {
    let (dst,a,b) = scalar_operands(instruction);
    execute_scalar::<F>(exec,base,op,dst,a,b)
}
#[inline(always)]
fn dispatch_load<M: MemoryBuffer>(exec: &mut Execution, store: &Store<M>, inst: usize, base: usize, op: u16, instruction: Instr) -> Result<(), ExecError> {
    let (dst,addr,offset) = load_operands(instruction);
    execute_load(exec,store,inst,base,op,dst,addr,offset)
}
#[inline(always)]
fn dispatch_store<M: MemoryBuffer>(exec: &Execution, store: &mut Store<M>, inst: usize, base: usize, op: u16, instruction: Instr) -> Result<(), ExecError> {
    let (addr,value,offset) = store_operands(instruction);
    execute_store(exec,store,inst,base,op,addr,value,offset)
}
#[inline(always)]
fn dispatch_simd<M: MemoryBuffer,F:FloatOps>(exec: &mut Execution, store: &mut Store<M>, inst: usize, function: usize, base: usize, op: u32, instruction: Instr) -> Result<(), ExecError> {
    let (dst,a,entry) = simd_operands(instruction);
    execute_simd::<M,F>(exec,store,inst,function,base,op,dst,a,entry)
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
        $(Instr::$scalar{..} => return dispatch_scalar::<F>(exec,base,$scalar_op,instruction),)*
        $(Instr::$load{..}=>return dispatch_load(exec,store,inst,base,$load_op,instruction),)*
        $(Instr::$store{..}=>return dispatch_store(exec,store,inst,base,$store_op,instruction),)*
        $(Instr::$simd{..}=>return dispatch_simd::<M,F>(exec,store,inst,function,base,$simd_op,instruction),)*
        Instr::Copy { dst, src } => return admin_copy::<M,P,F,A>(exec, base, dst, src),
        Instr::Copy2 { dst, src } => return admin_copy2::<M,P,F,A>(exec, base, dst, src),
        Instr::CopyN { dst, src, n } => return admin_copy_n::<M,P,F,A>(exec, base, dst, src, n),
        Instr::Const32 { dst, value } => return admin_const32::<M,P,F,A>(exec, base, dst, value),
        Instr::Const64 { dst, value } => return admin_const64::<M,P,F,A>(exec, base, dst, value),
        Instr::ConstV128 { dst, pool } => return admin_const_v128::<M,P,F,A>(exec, store, inst, function, base, dst, pool),
        Instr::Jump { target } => return admin_jump::<M,P,F,A>(exec, frame_index, target),
        Instr::JumpIfZero { cond, target } => return admin_jump_if_zero::<M,P,F,A>(exec, frame_index, base, cond, target),
        Instr::JumpIfNonZero { cond, target } => return admin_jump_if_non_zero::<M,P,F,A>(exec, frame_index, base, cond, target),
        Instr::JumpTable { index, start, len } => return admin_jump_table::<M,P,F,A>(exec, store, frame_index, inst, function, base, index, start, len),
        Instr::LoopHead => return admin_loop_head::<M,P,F,A>(platform),
        Instr::Call { func, base: callee } => return admin_call::<M,P,F,A>(exec, store, platform, inst, base, func, callee),
        Instr::CallIndirect {
            entry,
            index,
            base: callee,
        } => return admin_call_indirect::<M,P,F,A>(exec, store, platform, inst, function, base, entry, index, callee),
        Instr::Return { src, n } => return admin_return::<M,P,F,A>(exec, base, src, n),
        Instr::Unreachable => return admin_unreachable::<M,P,F,A>(),
        Instr::Select { a, b, cond } => return admin_select::<M,P,F,A>(exec, base, a, b, cond),
        Instr::Select2 { a, b, cond } => return admin_select2::<M,P,F,A>(exec, base, a, b, cond),
        Instr::GlobalGet { dst, global } => return admin_global_get::<M,P,F,A>(exec, store, inst, base, dst, global),
        Instr::GlobalGet2 { dst, global } => return admin_global_get2::<M,P,F,A>(exec, store, inst, base, dst, global),
        Instr::GlobalSet { src, global } => return admin_global_set::<M,P,F,A>(exec, store, inst, base, src, global),
        Instr::GlobalSet2 { src, global } => return admin_global_set2::<M,P,F,A>(exec, store, inst, base, src, global),
        Instr::MemorySize { dst } => return admin_memory_size::<M,P,F,A>(exec, store, inst, base, dst),
        Instr::MemoryGrow { dst } => return admin_memory_grow::<M,P,F,A>(exec, store, inst, base, dst),
        Instr::RefNull { dst } => return admin_ref_null::<M,P,F,A>(exec, base, dst),
        Instr::RefIsNull { dst, a } => return admin_ref_is_null::<M,P,F,A>(exec, base, dst, a),
        Instr::RefFunc { dst, func } => return admin_ref_func::<M,P,F,A>(exec, store, inst, base, dst, func),
        Instr::TableGet { dst, index, table } => return admin_table_get::<M,P,F,A>(exec, store, inst, base, dst, index, table),
        Instr::TableSet {
            index,
            value,
            table,
        } => return admin_table_set::<M,P,F,A>(exec, store, inst, base, index, value, table),
        Instr::TableSize { dst, table } => return admin_table_size::<M,P,F,A>(exec, store, inst, base, dst, table),
        Instr::TableGrow { dst, table } => return admin_table_grow::<M,P,F,A>(exec, store, inst, base, dst, table),
        Instr::MemoryFill { .. }
        | Instr::MemoryCopy { .. }
        | Instr::MemoryInit { .. }
        | Instr::DataDrop { .. }
        | Instr::TableFill { .. }
        | Instr::TableCopy { .. }
        | Instr::TableInit { .. }
        | Instr::ElemDrop { .. } => return admin_memory_fill::<M,P,F,A>(exec, store, inst, function, base, instruction),
    }
}

    };
}
super::operators::with_ops!(define_step);

/// Runs precompiled initialization code through the ordinary step loop.
pub(crate) fn synthetic<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
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

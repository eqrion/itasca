use super::compiler::{Branch, Instruction};
use super::store::FunctionCode;
use super::*;
use alloc::vec::Vec;

struct Frame {
    instance: usize,
    function: usize,
    address: FuncAddr,
    pc: usize,
    local_base: usize,
    operand_base: usize,
}
struct PendingHost {
    results: Vec<ValueType>,
}
/// A single-use invocation with explicit frames, value storage, and retained fuel.
///
/// Each instruction costs one unit. Bulk work additionally costs one unit per
/// 64 bytes/elements (rounded up); memory growth uses its requested byte count.
/// Wasm calls additionally cost one unit per initialized local. Host calls add
/// one per argument and two per expected result (request and continuation).
/// Costs are charged
/// atomically before any effect. Insufficient fuel leaves the instruction and
/// its operands unchanged. Counts may change with compiler versions.
pub struct Execution {
    store: usize,
    stack: Vec<Value>,
    locals: Vec<Value>,
    frames: Vec<Frame>,
    fuel: u64,
    initial: Option<FuncAddr>,
    host: Option<PendingHost>,
    finished: bool,
    failure: Option<RuntimeError>,
}
impl Execution {
    /// Runs synchronously through host calls, retaining continuation on suspension.
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
    /// Creates a typed invocation without executing or charging it.
    pub fn new(
        store: &Store,
        function: FuncAddr,
        arguments: &[Value],
    ) -> Result<Self, RuntimeError> {
        let ty = store.func_type(function)?;
        check_values(store, arguments, &ty.params)?;
        if arguments.len() > store.limits.max_values {
            return Err(RuntimeError::Resource(ResourceLimit::Values));
        }
        let mut stack = Vec::new();
        reserve(&mut stack, arguments.len())?;
        let mut i = 0;
        while i < arguments.len() {
            stack.push(arguments[i]);
            i += 1;
        }
        Ok(Self {
            store: store.id,
            stack,
            locals: Vec::new(),
            frames: Vec::new(),
            fuel: 0,
            initial: Some(function),
            host: None,
            finished: false,
            failure: None,
        })
    }
    /// Adds to the retained budget; arithmetic overflow is a resource error.
    pub fn add_fuel(&mut self, fuel: u64) -> Result<(), RuntimeError> {
        if self.finished {
            return Err(RuntimeError::InvalidState);
        }
        self.fuel = self
            .fuel
            .checked_add(fuel)
            .ok_or(RuntimeError::Resource(ResourceLimit::CostOverflow))?;
        Ok(())
    }
    /// Returns the fuel left, including fuel retained across suspension.
    pub fn fuel(&self) -> u64 {
        self.fuel
    }
    /// Returns the original module byte offset of the next instruction.
    pub fn source_offset(&self, store: &Store) -> Result<Option<usize>, RuntimeError> {
        store.check(self.store)?;
        match self.frames.last() {
            None => Ok(None),
            Some(f) => Ok(store.instances[f.instance].module.functions[f.function]
                .source_offsets
                .get(f.pc)
                .copied()),
        }
    }
    /// Completes exactly one outstanding host request after checking its results.
    ///
    /// Type or ownership errors leave the request pending for correction. A host
    /// failure terminates the invocation on its next run. No mutable store borrow
    /// or memory pointer is retained, so separate nested executions are permitted.
    pub fn resume_host(
        &mut self,
        store: &Store,
        result: Result<&[Value], RuntimeError>,
    ) -> Result<(), RuntimeError> {
        store.check(self.store)?;
        let pending = self.host.as_ref().ok_or(RuntimeError::InvalidState)?;
        match result {
            Ok(values) => {
                check_values(store, values, &pending.results)?;
                if self.stack.len() + self.locals.len() + values.len() > store.limits.max_values {
                    return Err(RuntimeError::Resource(ResourceLimit::Values));
                }
                reserve(&mut self.stack, values.len())?;
                let mut i = 0;
                while i < values.len() {
                    self.stack.push(values[i]);
                    i += 1;
                }
            }
            Err(e) => self.failure = Some(e),
        }
        self.host = None;
        Ok(())
    }
    /// Runs until completion, a trap/resource failure, a host call, or fuel shortage.
    pub fn run(&mut self, store: &mut Store) -> Outcome {
        if let Err(e) = store.check(self.store) {
            return Outcome::Failed(e);
        }
        if self.finished || self.host.is_some() {
            return Outcome::Failed(RuntimeError::InvalidState);
        }
        if let Some(e) = self.failure.take() {
            self.finished = true;
            return Outcome::Failed(e);
        }
        match self.run_inner(store) {
            Ok(outcome) => outcome,
            Err(e) => {
                self.finished = true;
                Outcome::Failed(e)
            }
        }
    }
    fn charge(&mut self, cost: u64) -> bool {
        if self.fuel < cost {
            false
        } else {
            self.fuel -= cost;
            true
        }
    }
    fn call_cost(&self, store: &Store, a: FuncAddr) -> Result<u64, RuntimeError> {
        let n = match store.funcs[a.index].code {
            FunctionCode::Host(_) => {
                let ty = &store.types[store.funcs[a.index].signature];
                ty.results
                    .len()
                    .checked_mul(2)
                    .and_then(|results| results.checked_add(ty.params.len()))
                    .ok_or(RuntimeError::Resource(ResourceLimit::CostOverflow))?
            }
            FunctionCode::Wasm { instance, function } => store.instances[instance].module.functions
                [function]
                .locals
                .len(),
        };
        1u64.checked_add(n as u64)
            .ok_or(RuntimeError::Resource(ResourceLimit::CostOverflow))
    }
    fn call(&mut self, store: &Store, a: FuncAddr) -> Result<Option<HostRequest>, RuntimeError> {
        let f = &store.funcs[a.index];
        let ty = &store.types[f.signature];
        let params = ty.params.len();
        let base = self
            .stack
            .len()
            .checked_sub(params)
            .ok_or(RuntimeError::InvalidState)?;
        match f.code {
            FunctionCode::Host(host_id) => {
                let mut arguments = Vec::new();
                reserve(&mut arguments, params)?;
                let mut i = base;
                while i < self.stack.len() {
                    arguments.push(self.stack[i]);
                    i += 1;
                }
                let mut expected = Vec::new();
                let mut results = Vec::new();
                reserve(&mut expected, ty.results.len())?;
                reserve(&mut results, ty.results.len())?;
                i = 0;
                while i < ty.results.len() {
                    expected.push(ty.results[i]);
                    results.push(ty.results[i]);
                    i += 1;
                }
                self.stack.truncate(base);
                self.host = Some(PendingHost { results: expected });
                Ok(Some(HostRequest {
                    host_id,
                    arguments,
                    results,
                }))
            }
            FunctionCode::Wasm { instance, function } => {
                if self.frames.len() >= store.limits.max_frames {
                    return Err(RuntimeError::Resource(ResourceLimit::CallStack));
                }
                let code = &store.instances[instance].module.functions[function];
                let required = self
                    .locals
                    .len()
                    .checked_add(code.locals.len())
                    .and_then(|n| n.checked_add(base))
                    .and_then(|n| n.checked_add(code.max_stack))
                    .ok_or(RuntimeError::Resource(ResourceLimit::Values))?;
                if required > store.limits.max_values {
                    return Err(RuntimeError::Resource(ResourceLimit::Values));
                }
                reserve(&mut self.frames, 1)?;
                reserve(&mut self.locals, code.locals.len())?;
                reserve(&mut self.stack, code.max_stack)?;
                let local_base = self.locals.len();
                let mut i = 0;
                while i < code.locals.len() {
                    self.locals.push(if i < params {
                        self.stack[base + i]
                    } else {
                        Value::zero(code.locals[i])
                    });
                    i += 1;
                }
                self.stack.truncate(base);
                self.frames.push(Frame {
                    instance,
                    function,
                    address: a,
                    pc: 0,
                    local_base,
                    operand_base: base,
                });
                Ok(None)
            }
        }
    }
    fn run_inner(&mut self, store: &mut Store) -> Result<Outcome, RuntimeError> {
        loop {
            if let Some(a) = self.initial {
                let cost = self.call_cost(store, a)?;
                if !self.charge(cost) {
                    return Ok(Outcome::Suspended);
                }
                self.initial = None;
                if let Some(request) = self.call(store, a)? {
                    return Ok(Outcome::NeedsHostCall(request));
                }
            }
            if self.frames.is_empty() {
                self.finished = true;
                return Ok(Outcome::Returned(core::mem::take(&mut self.stack)));
            }
            let frame = self.frames.last().ok_or(RuntimeError::InvalidState)?;
            let instance = frame.instance;
            let function = frame.function;
            let pc = frame.pc;
            let instruction = *store.instances[instance].module.functions[function]
                .instructions
                .get(pc)
                .ok_or(RuntimeError::InvalidState)?;
            let cost = self.cost(store, instance, instruction)?;
            if !self.charge(cost) {
                return Ok(Outcome::Suspended);
            }
            self.frames.last_mut().ok_or(RuntimeError::InvalidState)?.pc += 1;
            match instruction {
                Instruction::Jump(b) => self.branch(b)?,
                Instruction::JumpIf(b) => {
                    if pop(&mut self.stack)?.i32()? != 0 {
                        self.branch(b)?;
                    }
                }
                Instruction::JumpIfZero(target) => {
                    if pop(&mut self.stack)?.i32()? == 0 {
                        self.frames.last_mut().ok_or(RuntimeError::InvalidState)?.pc = target;
                    }
                }
                Instruction::JumpTable { start, len } => {
                    let index = pop(&mut self.stack)?.i32()? as usize;
                    let selected = if index < len - 1 { index } else { len - 1 };
                    let b = store.instances[instance].module.functions[function].branches
                        [start + selected];
                    self.branch(b)?;
                }
                Instruction::Return => self.return_frame(store)?,
                Instruction::Op { opcode, a, b, bits } => match opcode {
                    0x10 => {
                        let target = store.instances[instance].funcs[a as usize];
                        if let Some(request) = self.call(store, target)? {
                            return Ok(Outcome::NeedsHostCall(request));
                        }
                    }
                    0x11 => {
                        let target = self.indirect(store, instance, a, b)?;
                        pop(&mut self.stack)?;
                        if let Some(request) = self.call(store, target)? {
                            return Ok(Outcome::NeedsHostCall(request));
                        }
                    }
                    _ => self.op(store, instance, opcode, a, b, bits)?,
                },
            }
        }
    }
    fn indirect(
        &self,
        store: &Store,
        inst: usize,
        ty: u32,
        table: u32,
    ) -> Result<FuncAddr, RuntimeError> {
        let index = self.stack.last().ok_or(RuntimeError::InvalidState)?.i32()? as usize;
        let instance = &store.instances[inst];
        let t = &store.tables[instance.tables[table as usize].index];
        let value = t
            .elements
            .get(index)
            .ok_or(RuntimeError::Trap(Trap::TableOutOfBounds))?;
        let a = match value {
            Value::FuncRef(Some(a)) => *a,
            _ => return Err(Trap::UninitializedElement.into()),
        };
        if store.funcs[a.index].signature != instance.types[ty as usize] {
            return Err(Trap::IndirectCallTypeMismatch.into());
        }
        Ok(a)
    }
    fn cost(
        &self,
        store: &Store,
        inst: usize,
        instruction: Instruction,
    ) -> Result<u64, RuntimeError> {
        let n = match instruction {
            Instruction::Op {
                opcode: 0x10, a, ..
            } => return self.call_cost(store, store.instances[inst].funcs[a as usize]),
            Instruction::Op {
                opcode: 0x11, a, b, ..
            } => {
                return match self.indirect(store, inst, a, b) {
                    Ok(target) => self.call_cost(store, target),
                    Err(_) => Ok(1),
                }
            }
            Instruction::Op { opcode: 0x40, .. } => {
                self.stack.last().ok_or(RuntimeError::InvalidState)?.i32()? as u64 * 65536
            }
            Instruction::Op {
                opcode: 0x108 | 0x10a | 0x10b | 0x10c | 0x10e | 0x10f | 0x111,
                ..
            } => self.stack.last().ok_or(RuntimeError::InvalidState)?.i32()? as u64,
            _ => 0,
        };
        1u64.checked_add(n / 64 + u64::from(n % 64 != 0))
            .ok_or(RuntimeError::Resource(ResourceLimit::CostOverflow))
    }
    fn branch(&mut self, b: Branch) -> Result<(), RuntimeError> {
        let frame = self.frames.last_mut().ok_or(RuntimeError::InvalidState)?;
        let target = frame
            .operand_base
            .checked_add(b.height)
            .ok_or(RuntimeError::InvalidState)?;
        let source = self
            .stack
            .len()
            .checked_sub(b.keep)
            .ok_or(RuntimeError::InvalidState)?;
        if target > source {
            return Err(RuntimeError::InvalidState);
        }
        self.stack.copy_within(source.., target);
        self.stack.truncate(target + b.keep);
        frame.pc = b.target;
        Ok(())
    }
    fn return_frame(&mut self, store: &Store) -> Result<(), RuntimeError> {
        let f = self.frames.pop().ok_or(RuntimeError::InvalidState)?;
        let keep = store.types[store.funcs[f.address.index].signature]
            .results
            .len();
        let source = self
            .stack
            .len()
            .checked_sub(keep)
            .ok_or(RuntimeError::InvalidState)?;
        if f.operand_base > source {
            return Err(RuntimeError::InvalidState);
        }
        self.stack.copy_within(source.., f.operand_base);
        self.stack.truncate(f.operand_base + keep);
        self.locals.truncate(f.local_base);
        Ok(())
    }
    fn op(
        &mut self,
        store: &mut Store,
        inst: usize,
        opcode: u16,
        a: u32,
        b: u32,
        bits: u128,
    ) -> Result<(), RuntimeError> {
        match opcode {
            0x00 => return Err(Trap::Unreachable.into()),
            0x01 => (),
            0x1a => {
                pop(&mut self.stack)?;
            }
            0x1b | 0x1c => {
                let c = pop(&mut self.stack)?.i32()?;
                let rhs = pop(&mut self.stack)?;
                let lhs = pop(&mut self.stack)?;
                self.stack.push(if c != 0 { lhs } else { rhs });
            }
            0x20..=0x22 => {
                let base = self
                    .frames
                    .last()
                    .ok_or(RuntimeError::InvalidState)?
                    .local_base;
                match opcode {
                    0x20 => self.stack.push(self.locals[base + a as usize]),
                    0x21 => self.locals[base + a as usize] = pop(&mut self.stack)?,
                    _ => {
                        self.locals[base + a as usize] =
                            *self.stack.last().ok_or(RuntimeError::InvalidState)?
                    }
                }
            }
            0x23 => self
                .stack
                .push(store.globals[store.instances[inst].globals[a as usize].index].value),
            0x24 => {
                store.globals[store.instances[inst].globals[a as usize].index].value =
                    pop(&mut self.stack)?
            }
            0x25 => {
                let i = pop(&mut self.stack)?.i32()? as usize;
                let t = store.instances[inst].tables[a as usize].index;
                self.stack.push(
                    *store.tables[t]
                        .elements
                        .get(i)
                        .ok_or(RuntimeError::Trap(Trap::TableOutOfBounds))?,
                );
            }
            0x26 => {
                let v = pop(&mut self.stack)?;
                let i = pop(&mut self.stack)?.i32()? as usize;
                let t = store.instances[inst].tables[a as usize].index;
                *store.tables[t]
                    .elements
                    .get_mut(i)
                    .ok_or(RuntimeError::Trap(Trap::TableOutOfBounds))? = v;
            }
            0x28..=0x3e => {
                let index = store.instances[inst].memories[0].index;
                memory_op(opcode, a, &mut self.stack, &mut store.memories[index].bytes)?;
            }
            0x3f => self.stack.push(Value::I32(
                (store.memories[store.instances[inst].memories[0].index]
                    .bytes
                    .len()
                    / 65536) as u32,
            )),
            0x40 => {
                let delta = pop(&mut self.stack)?.i32()?;
                let index = store.instances[inst].memories[0].index;
                let result = store.grow_memory(index, delta);
                self.stack.push(Value::I32(result));
            }
            0x41 => self.stack.push(Value::I32(bits as u32)),
            0x42 => self.stack.push(Value::I64(bits as u64)),
            0x43 => self.stack.push(Value::F32(bits as u32)),
            0x44 => self.stack.push(Value::F64(bits as u64)),
            0x45..=0xc4 | 0x100..=0x107 => numeric::scalar(opcode, &mut self.stack)?,
            0xd0 => self.stack.push(if a == 0 {
                Value::FuncRef(None)
            } else {
                Value::ExternRef(None)
            }),
            0xd1 => {
                let v = pop(&mut self.stack)?;
                self.stack.push(Value::I32(u32::from(matches!(
                    v,
                    Value::FuncRef(None) | Value::ExternRef(None)
                ))));
            }
            0xd2 => self.stack.push(Value::FuncRef(Some(
                store.instances[inst].funcs[a as usize],
            ))),
            0x108..=0x111 => self.bulk(store, inst, opcode, a, b)?,
            0x200..=0x2ff => {
                let memory = match store.instances[inst].memories.first() {
                    Some(m) => Some(&mut store.memories[m.index].bytes),
                    None => None,
                };
                numeric::simd((opcode - 0x200) as u32, a, b, bits, &mut self.stack, memory)?;
            }
            _ => return Err(RuntimeError::InvalidState),
        }
        Ok(())
    }
    fn bulk(
        &mut self,
        store: &mut Store,
        inst: usize,
        op: u16,
        a: u32,
        b: u32,
    ) -> Result<(), RuntimeError> {
        match op {
            0x109 => store.instances[inst].data[a as usize] = false,
            0x10d => store.instances[inst].elements[a as usize].clear(),
            0x10f => {
                let delta = pop(&mut self.stack)?.i32()?;
                let value = pop(&mut self.stack)?;
                let table = store.instances[inst].tables[a as usize].index;
                let old = store.grow_table(table, delta, value);
                self.stack.push(Value::I32(old));
            }
            0x110 => {
                let table = store.instances[inst].tables[a as usize].index;
                self.stack
                    .push(Value::I32(store.tables[table].elements.len() as u32));
            }
            0x108 | 0x10a | 0x10b => {
                let len = pop(&mut self.stack)?.i32()? as u64;
                let source = pop(&mut self.stack)?.i32()?;
                let destination = pop(&mut self.stack)?.i32()? as u64;
                let memory = store.instances[inst].memories[0].index;
                let dst = range(
                    destination,
                    len,
                    store.memories[memory].bytes.len(),
                    Trap::MemoryOutOfBounds,
                )?;
                match op {
                    0x108 => {
                        let instance = &store.instances[inst];
                        let data = &instance.module.tail().data[a as usize].init;
                        let size = if instance.data[a as usize] {
                            data.len()
                        } else {
                            0
                        };
                        let src = range(source as u64, len, size, Trap::MemoryOutOfBounds)?;
                        store.memories[memory].bytes[dst].copy_from_slice(&data[src]);
                    }
                    0x10a => {
                        let src = range(
                            source as u64,
                            len,
                            store.memories[memory].bytes.len(),
                            Trap::MemoryOutOfBounds,
                        )?;
                        store.memories[memory].bytes.copy_within(src, dst.start);
                    }
                    _ => store.memories[memory].bytes[dst].fill(source as u8),
                }
            }
            0x10c | 0x10e => {
                let len = pop(&mut self.stack)?.i32()? as u64;
                let source = pop(&mut self.stack)?.i32()? as u64;
                let destination = pop(&mut self.stack)?.i32()? as u64;
                let table_index = if op == 0x10c { b } else { a };
                let table = store.instances[inst].tables[table_index as usize].index;
                let dst = range(
                    destination,
                    len,
                    store.tables[table].elements.len(),
                    Trap::TableOutOfBounds,
                )?;
                if op == 0x10c {
                    let src = range(
                        source,
                        len,
                        store.instances[inst].elements[a as usize].len(),
                        Trap::TableOutOfBounds,
                    )?;
                    let mut i = 0;
                    while i < dst.len() {
                        store.tables[table].elements[dst.start + i] =
                            store.instances[inst].elements[a as usize][src.start + i];
                        i += 1;
                    }
                } else {
                    let src_table = store.instances[inst].tables[b as usize].index;
                    let src = range(
                        source,
                        len,
                        store.tables[src_table].elements.len(),
                        Trap::TableOutOfBounds,
                    )?;
                    if table == src_table {
                        store.tables[table].elements.copy_within(src, dst.start);
                    } else {
                        let mut i = 0;
                        while i < dst.len() {
                            store.tables[table].elements[dst.start + i] =
                                store.tables[src_table].elements[src.start + i];
                            i += 1;
                        }
                    }
                }
            }
            0x111 => {
                let len = pop(&mut self.stack)?.i32()? as u64;
                let value = pop(&mut self.stack)?;
                let destination = pop(&mut self.stack)?.i32()? as u64;
                let table = store.instances[inst].tables[a as usize].index;
                let dst = range(
                    destination,
                    len,
                    store.tables[table].elements.len(),
                    Trap::TableOutOfBounds,
                )?;
                store.tables[table].elements[dst].fill(value);
            }
            _ => return Err(RuntimeError::InvalidState),
        }
        Ok(())
    }
}
fn pop(stack: &mut Vec<Value>) -> Result<Value, RuntimeError> {
    stack.pop().ok_or(RuntimeError::InvalidState)
}
fn check_values(store: &Store, values: &[Value], types: &[ValueType]) -> Result<(), RuntimeError> {
    if values.len() != types.len() {
        return Err(RuntimeError::TypeMismatch);
    }
    let mut i = 0;
    while i < values.len() {
        store.check_value(values[i])?;
        if values[i].value_type() != types[i] {
            return Err(RuntimeError::TypeMismatch);
        }
        i += 1;
    }
    Ok(())
}
fn memory_op(
    op: u16,
    offset: u32,
    stack: &mut Vec<Value>,
    memory: &mut [u8],
) -> Result<(), RuntimeError> {
    let size = match op {
        0x28 | 0x2a | 0x34 | 0x35 | 0x36 | 0x38 | 0x3e => 4,
        0x29 | 0x2b | 0x37 | 0x39 => 8,
        0x2c | 0x2d | 0x30 | 0x31 | 0x3a | 0x3c => 1,
        _ => 2,
    };
    let value = if op >= 0x36 { Some(pop(stack)?) } else { None };
    let address = pop(stack)?.i32()? as u64 + offset as u64;
    let r = range(address, size, memory.len(), Trap::MemoryOutOfBounds)?;
    if let Some(v) = value {
        let bits = match v {
            Value::I32(x) | Value::F32(x) => x as u64,
            Value::I64(x) | Value::F64(x) => x,
            _ => return Err(RuntimeError::TypeMismatch),
        };
        let mut i = 0;
        while i < size as usize {
            memory[r.start + i] = (bits >> (i * 8)) as u8;
            i += 1;
        }
    } else {
        let mut bits = 0u64;
        let mut i = 0;
        while i < size as usize {
            bits |= (memory[r.start + i] as u64) << (i * 8);
            i += 1;
        }
        let result = match op {
            0x28 => Value::I32(bits as u32),
            0x29 => Value::I64(bits),
            0x2a => Value::F32(bits as u32),
            0x2b => Value::F64(bits),
            0x2c => Value::I32(bits as i8 as i32 as u32),
            0x2d | 0x2f => Value::I32(bits as u32),
            0x2e => Value::I32(bits as i16 as i32 as u32),
            0x30 => Value::I64(bits as i8 as i64 as u64),
            0x32 => Value::I64(bits as i16 as i64 as u64),
            0x34 => Value::I64(bits as i32 as i64 as u64),
            _ => Value::I64(bits),
        };
        stack.push(result);
    }
    Ok(())
}

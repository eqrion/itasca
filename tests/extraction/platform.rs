#![allow(dead_code)]
pub trait MemoryBuffer {
    fn bytes(&self) -> &[u8];
    fn bytes_mut(&mut self) -> &mut [u8];
    fn grow(&mut self, len: usize) -> bool;
}
pub struct Store<M: MemoryBuffer> {
    pub memory: M,
    pub slots: Vec<u64>,
}
pub enum HostError {
    Trap,
    StackOverflow,
}
pub enum InterruptAction {
    Continue,
    Terminate,
}
pub trait Platform<M: MemoryBuffer> {
    fn interrupt(&mut self) -> InterruptAction;
    fn call_host(
        &mut self,
        store: &mut Store<M>,
        id: u64,
        args: &[u64],
        results: &mut [u64],
    ) -> Result<(), HostError>;
}
pub trait FloatOps {
    fn f32_add(a: u32, b: u32) -> u32;
}
pub trait Alloc {
    fn reserve<T>(v: &mut Vec<T>, additional: usize) -> bool;
}
pub struct JumpTable {
    pub targets: Vec<usize>,
    pub default: usize,
}
#[derive(Copy, Clone)]
pub enum Instr {
    Halt,
    Add(usize, usize, usize),
    Float(usize, u32, u32),
    Host(u64),
    Jump(usize),
    JumpTable(usize),
    Grow(usize),
}
pub enum Action {
    Continue(usize),
    Halt,
    Error,
}
pub fn step<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    store: &mut Store<M>,
    platform: &mut P,
    code: &[Instr],
    tables: &[JumpTable],
    pc: usize,
) -> Action {
    let instr = code[pc];
    match instr {
        Instr::Halt => Action::Halt,
        Instr::Add(dst, a, b) => {
            store.slots[dst] = store.slots[a].wrapping_add(store.slots[b]);
            Action::Continue(pc + 1)
        }
        Instr::Float(dst, a, b) => {
            store.slots[dst] = F::f32_add(a, b) as u64;
            Action::Continue(pc + 1)
        }
        Instr::Host(id) => {
            let args = [0u64];
            let mut results = [0u64];
            match platform.call_host(store, id, &args, &mut results) {
                Ok(()) => Action::Continue(pc + 1),
                Err(_) => Action::Error,
            }
        }
        Instr::Jump(target) => Action::Continue(target),
        Instr::JumpTable(index) => {
            let jt = &tables[index];
            let selector = store.slots[0] as usize;
            if selector < jt.targets.len() {
                Action::Continue(jt.targets[selector])
            } else {
                Action::Continue(jt.default)
            }
        }
        Instr::Grow(len) => {
            if A::reserve(&mut store.slots, len) && store.memory.grow(len) {
                let b = store.memory.bytes_mut();
                if b.len() > 0 {
                    b[0] = 0;
                }
                Action::Continue(pc + 1)
            } else {
                Action::Error
            }
        }
    }
}
pub fn invoke<M: MemoryBuffer, P: Platform<M>, F: FloatOps, A: Alloc>(
    store: &mut Store<M>,
    platform: &mut P,
    code: &[Instr],
    tables: &[JumpTable],
) -> bool {
    let mut pc = 0;
    loop {
        match platform.interrupt() {
            InterruptAction::Terminate => return false,
            InterruptAction::Continue => {}
        }
        match step::<M, P, F, A>(store, platform, code, tables, pc) {
            Action::Continue(next) => pc = next,
            Action::Halt => return true,
            Action::Error => return false,
        }
    }
}

// Disjoint bulk copies use the pinned slice models and compile to memcpy.
pub fn copy_disjoint(bytes: &mut [u8], dst: usize, src: usize, len: usize) {
    if dst + len <= src {
        let (left, right) = bytes.split_at_mut(src);
        left[dst..dst + len].copy_from_slice(&right[..len]);
    } else if src + len <= dst {
        let (left, right) = bytes.split_at_mut(dst);
        right[..len].copy_from_slice(&left[src..src + len]);
    }
}
pub fn fill_bytes(bytes: &mut [u8], start: usize, end: usize, value: u8) {
    bytes[start..end].fill(value);
}

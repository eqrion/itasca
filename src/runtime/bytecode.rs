//! Immutable slot bytecode. Every operand is relative to its function frame.
use super::compiler::ControlMap;
use crate::ValueType;
use alloc::vec::Vec;

#[cfg_attr(not(charon), derive(Debug))]
pub(crate) struct CompiledFunction {
    pub(crate) locals: Vec<ValueType>,
    pub(crate) local_slots: u32,
    pub(crate) param_slots: u32,
    pub(crate) slot_count: u32,
    pub(crate) max_stack: usize,
    pub(crate) code: Vec<Instr>,
    pub(crate) jump_tables: Vec<u32>,
    pub(crate) v128_pool: Vec<u128>,
    /// (table, type) for call_indirect, (destination, source) for table.copy,
    /// and (element, table) for table.init.
    pub(crate) indirect: Vec<(u32, u32)>,
    pub(crate) simd: Vec<SimdImmediate>,
    pub(crate) source_offsets: Vec<usize>,
    pub(crate) controls: Vec<ControlMap>,
    pub(crate) type_index: u32,
    pub(crate) body_start: usize,
    pub(crate) body_end: usize,
}

#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub(crate) struct SimdImmediate {
    pub(crate) offset: u32,
    pub(crate) lane: u32,
    pub(crate) bits: u128,
}

// Macro expansion gives Charon a flat enum with one variant per operator.
macro_rules! bytecode {
    (scalar {$($scalar:ident = $scalar_op:expr;)*}
     load {$($load:ident = $load_op:expr;)*}
     store {$($store:ident = $store_op:expr;)*}
     simd {$($simd:ident = $simd_op:expr;)*}) => {
        #[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
        #[derive(Clone, Copy)]
        pub(crate) enum Instr {
            Copy { dst: u32, src: u32 },
            Copy2 { dst: u32, src: u32 },
            CopyN { dst: u32, src: u32, n: u32 },
            Const32 { dst: u32, value: u32 },
            Const64 { dst: u32, value: u64 },
            ConstV128 { dst: u32, pool: u32 },
            Jump { target: u32 },
            JumpIfZero { cond: u32, target: u32 },
            JumpIfNonZero { cond: u32, target: u32 },
            JumpTable { index: u32, start: u32, len: u32 },
            LoopHead,
            Call { func: u32, base: u32 },
            CallIndirect { entry: u32, index: u32, base: u32 },
            Return { src: u32, n: u32 },
            Unreachable,
            Select { a: u32, b: u32, cond: u32 },
            Select2 { a: u32, b: u32, cond: u32 },
            GlobalGet { dst: u32, global: u32 },
            GlobalGet2 { dst: u32, global: u32 },
            GlobalSet { src: u32, global: u32 },
            GlobalSet2 { src: u32, global: u32 },
            $($scalar { dst: u32, a: u32, b: u32 },)*
            $($load { dst: u32, addr: u32, offset: u32 },)*
            $($store { addr: u32, value: u32, offset: u32 },)*
            MemorySize { dst: u32 },
            MemoryGrow { dst: u32 },
            MemoryFill { d: u32 },
            MemoryCopy { d: u32 },
            MemoryInit { d: u32, data: u32 },
            DataDrop { data: u32 },
            TableGet { dst: u32, index: u32, table: u32 },
            TableSet { index: u32, value: u32, table: u32 },
            TableSize { dst: u32, table: u32 },
            TableGrow { dst: u32, table: u32 },
            TableFill { d: u32, table: u32 },
            TableCopy { d: u32, entry: u32 },
            TableInit { d: u32, entry: u32 },
            ElemDrop { elem: u32 },
            RefNull { dst: u32 },
            RefIsNull { dst: u32, a: u32 },
            RefFunc { dst: u32, func: u32 },
            $($simd { dst: u32, a: u32, entry: u32 },)*
        }
        impl Instr {
            pub(crate) fn scalar(self) -> Option<(u16, u32, u32, u32)> {
                match self { $(Self::$scalar {dst,a,b} => Some(($scalar_op,dst,a,b)),)* _ => None }
            }
            pub(crate) fn make_scalar(op: u16, dst: u32, a: u32, b: u32) -> Option<Self> {
                match op { $($scalar_op => Some(Self::$scalar {dst,a,b}),)* _ => None }
            }
            pub(crate) fn load(self) -> Option<(u16, u32, u32, u32)> {
                match self { $(Self::$load {dst,addr,offset} => Some(($load_op,dst,addr,offset)),)* _ => None }
            }
            pub(crate) fn make_load(op: u16, dst: u32, addr: u32, offset: u32) -> Option<Self> {
                match op { $($load_op => Some(Self::$load {dst,addr,offset}),)* _ => None }
            }
            pub(crate) fn store(self) -> Option<(u16, u32, u32, u32)> {
                match self { $(Self::$store {addr,value,offset} => Some(($store_op,addr,value,offset)),)* _ => None }
            }
            pub(crate) fn make_store(op: u16, addr: u32, value: u32, offset: u32) -> Option<Self> {
                match op { $($store_op => Some(Self::$store {addr,value,offset}),)* _ => None }
            }
            pub(crate) fn simd(self) -> Option<(u32, u32, u32, u32)> {
                match self { $(Self::$simd {dst,a,entry} => Some(($simd_op,dst,a,entry)),)* _ => None }
            }
            pub(crate) fn make_simd(op: u32, dst: u32, a: u32, entry: u32) -> Option<Self> {
                match op { $($simd_op => Some(Self::$simd {dst,a,entry}),)* _ => None }
            }
        }
    }
}

super::operators::with_ops!(bytecode);

/// Slot widths of SIMD operands and result; absent operands have width zero.
pub(crate) fn simd_shape(op: u32) -> Option<(u32, u32, u32, u32)> {
    match op {
        0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 15 | 16 | 17 | 18 | 19 | 20 | 92 | 93 => {
            Some((1, 0, 0, 2))
        }
        11 | 88 | 89 | 90 | 91 => Some((1, 2, 0, 0)),
        84 | 85 | 86 | 87 => Some((1, 2, 0, 2)),
        21 | 22 | 24 | 25 | 27 | 29 | 31 | 33 | 83 | 99 | 100 | 131 | 132 | 163 | 164 | 195
        | 196 => Some((2, 0, 0, 1)),
        77 | 94 | 95 | 96 | 97 | 98 | 103 | 104 | 105 | 106 | 116 | 117 | 122 | 124 | 125 | 126
        | 127 | 128 | 129 | 135 | 136 | 137 | 138 | 148 | 160 | 161 | 167 | 168 | 169 | 170
        | 192 | 193 | 199 | 200 | 201 | 202 | 224 | 225 | 227 | 236 | 237 | 239 | 248 | 249
        | 250 | 251 | 252 | 253 | 254 | 255 => Some((2, 0, 0, 2)),
        23 | 26 | 28 | 30 | 32 | 34 | 107 | 108 | 109 | 139 | 140 | 141 | 171 | 172 | 173 | 203
        | 204 | 205 => Some((2, 1, 0, 2)),
        13 | 14 | 35 | 36 | 37 | 38 | 39 | 40 | 41 | 42 | 43 | 44 | 45 | 46 | 47 | 48 | 49 | 50
        | 51 | 52 | 53 | 54 | 55 | 56 | 57 | 58 | 59 | 60 | 61 | 62 | 63 | 64 | 65 | 66 | 67
        | 68 | 69 | 70 | 71 | 72 | 73 | 74 | 75 | 76 | 78 | 79 | 80 | 81 | 101 | 102 | 110
        | 111 | 112 | 113 | 114 | 115 | 118 | 119 | 120 | 121 | 123 | 130 | 133 | 134 | 142
        | 143 | 144 | 145 | 146 | 147 | 149 | 150 | 151 | 152 | 153 | 155 | 156 | 157 | 158
        | 159 | 174 | 177 | 181 | 182 | 183 | 184 | 185 | 186 | 188 | 189 | 190 | 191 | 206
        | 209 | 213 | 214 | 215 | 216 | 217 | 218 | 219 | 220 | 221 | 222 | 223 | 228 | 229
        | 230 | 231 | 232 | 233 | 234 | 235 | 240 | 241 | 242 | 243 | 244 | 245 | 246 | 247 => {
            Some((2, 2, 0, 2))
        }
        82 => Some((2, 2, 2, 2)),
        _ => None,
    }
}

fn is_return(instruction: Instr) -> bool {
    matches!(instruction, Instr::Return { .. })
}

impl CompiledFunction {
    fn slots_fit(&self, start: u32, n: u32) -> bool {
        start <= self.slot_count && n <= self.slot_count - start
    }

    fn instruction_valid(&self, instruction: Instr) -> bool {
        let length = self.code.len();
        if let Some((_, dst, a, b)) = instruction.scalar() {
            self.slots_fit(dst, 1) && self.slots_fit(a, 1) && self.slots_fit(b, 1)
        } else if let Some((_, dst, addr, _)) = instruction.load() {
            self.slots_fit(dst, 1) && self.slots_fit(addr, 1)
        } else if let Some((_, addr, value, _)) = instruction.store() {
            self.slots_fit(addr, 1) && self.slots_fit(value, 1)
        } else if let Some((op, dst, a, entry)) = instruction.simd() {
            match simd_shape(op) {
                Some((x, y, z, out)) => {
                    self.slots_fit(a, x + y + z)
                        && self.slots_fit(dst, out)
                        && (entry as usize) < self.simd.len()
                }
                None => false,
            }
        } else {
            match instruction {
                Instr::Copy { dst, src } => self.slots_fit(dst, 1) && self.slots_fit(src, 1),
                Instr::Copy2 { dst, src } => self.slots_fit(dst, 2) && self.slots_fit(src, 2),
                Instr::CopyN { dst, src, n } => {
                    dst <= src && self.slots_fit(dst, n) && self.slots_fit(src, n)
                }
                Instr::Const32 { dst, .. }
                | Instr::Const64 { dst, .. }
                | Instr::GlobalGet { dst, .. }
                | Instr::MemorySize { dst }
                | Instr::MemoryGrow { dst }
                | Instr::TableSize { dst, .. }
                | Instr::RefNull { dst }
                | Instr::RefFunc { dst, .. } => self.slots_fit(dst, 1),
                Instr::GlobalGet2 { dst, .. } => self.slots_fit(dst, 2),
                Instr::ConstV128 { dst, pool } => {
                    self.slots_fit(dst, 2) && (pool as usize) < self.v128_pool.len()
                }
                Instr::Jump { target } => (target as usize) < length,
                Instr::JumpIfZero { cond, target } | Instr::JumpIfNonZero { cond, target } => {
                    self.slots_fit(cond, 1) && (target as usize) < length
                }
                Instr::JumpTable { index, start, len } => {
                    self.slots_fit(index, 1)
                        && len > 0
                        && (start as usize) <= self.jump_tables.len()
                        && (len as usize) <= self.jump_tables.len() - start as usize
                }
                Instr::Call { base, .. } => self.slots_fit(base, 0),
                Instr::CallIndirect { entry, index, base } => {
                    self.slots_fit(base, 0)
                        && self.slots_fit(index, 1)
                        && (entry as usize) < self.indirect.len()
                }
                Instr::Return { src, n } => self.slots_fit(src, n),
                Instr::Select { a, b, cond } => {
                    self.slots_fit(a, 1) && self.slots_fit(b, 1) && self.slots_fit(cond, 1)
                }
                Instr::Select2 { a, b, cond } => {
                    self.slots_fit(a, 2) && self.slots_fit(b, 2) && self.slots_fit(cond, 1)
                }
                Instr::GlobalSet { src, .. } => self.slots_fit(src, 1),
                Instr::GlobalSet2 { src, .. } => self.slots_fit(src, 2),
                Instr::MemoryFill { d }
                | Instr::MemoryCopy { d }
                | Instr::MemoryInit { d, .. }
                | Instr::TableFill { d, .. } => self.slots_fit(d, 3),
                Instr::TableCopy { d, entry } | Instr::TableInit { d, entry } => {
                    self.slots_fit(d, 3) && (entry as usize) < self.indirect.len()
                }
                Instr::TableGet { dst, index, .. } => {
                    self.slots_fit(dst, 1) && self.slots_fit(index, 1)
                }
                Instr::TableSet { index, value, .. } => {
                    self.slots_fit(index, 1) && self.slots_fit(value, 1)
                }
                Instr::TableGrow { dst, .. } => self.slots_fit(dst, 2),
                Instr::RefIsNull { dst, a } => self.slots_fit(dst, 1) && self.slots_fit(a, 1),
                Instr::LoopHead
                | Instr::Unreachable
                | Instr::DataDrop { .. }
                | Instr::ElemDrop { .. } => true,
                _ => false,
            }
        }
    }

    /// Independent structural gate before compiled code can be published.
    pub(crate) fn well_formed(&self) -> bool {
        let length = self.code.len();
        let synthetic = self.body_start == 0 && self.body_end == 0;
        if length == 0
            || (!synthetic && self.source_offsets.len() != length)
            || (synthetic && !self.source_offsets.is_empty())
            || self.local_slots > self.slot_count
            || self.param_slots > self.local_slots
        {
            return false;
        }
        if !is_return(self.code[length - 1]) {
            return false;
        }
        let mut valid = true;
        let mut i = 0;
        while i < length && valid {
            if !synthetic {
                let source = self.source_offsets[i];
                if source < self.body_start
                    || source >= self.body_end
                    || (i > 0 && self.source_offsets[i - 1] > source)
                {
                    valid = false;
                }
            }
            let instruction = self.code[i];
            let instruction_valid = self.instruction_valid(instruction);
            if !instruction_valid {
                valid = false;
            }
            i += 1;
        }
        i = 0;
        while i < self.jump_tables.len() && valid {
            if self.jump_tables[i] as usize >= length {
                valid = false;
            }
            i += 1;
        }
        i = 0;
        while i < self.controls.len() && valid {
            let map = &self.controls[i];
            if map.start_pc > map.end_pc
                || map.end_pc >= length
                || map.source_start < self.body_start
                || map.source_end > self.body_end
                || map.source_start >= map.source_end
            {
                valid = false;
            }
            i += 1;
        }
        valid
    }
}

impl CompiledFunction {
    /// Internal code with no original opcode coordinates or declared locals.
    /// The caller supplies initialized slots and a terminating Return instruction.
    pub(crate) fn synthetic(code: Vec<Instr>, slot_count: u32) -> Self {
        Self {
            locals: Vec::new(),
            local_slots: 0,
            param_slots: 0,
            slot_count,
            max_stack: 0,
            code,
            jump_tables: Vec::new(),
            v128_pool: Vec::new(),
            indirect: Vec::new(),
            simd: Vec::new(),
            source_offsets: Vec::new(),
            controls: Vec::new(),
            type_index: 0,
            body_start: 0,
            body_end: 0,
        }
    }
}

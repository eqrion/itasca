//! Scalar, memory, table, and reference lowering.
use super::*;

fn top_is_v128(values: &[StackType]) -> bool {
    if values.is_empty() {
        return false;
    }
    let ty = values[values.len() - 1];
    matches!(ty, StackType::Val(ValueType::V128))
}

fn scalar_binary(opcode: u16) -> bool {
    matches!(
        opcode,
        0x46 | 0x47
            | 0x48
            | 0x49
            | 0x4a
            | 0x4b
            | 0x4c
            | 0x4d
            | 0x4e
            | 0x4f
            | 0x51
            | 0x52
            | 0x53
            | 0x54
            | 0x55
            | 0x56
            | 0x57
            | 0x58
            | 0x59
            | 0x5a
            | 0x5b
            | 0x5c
            | 0x5d
            | 0x5e
            | 0x5f
            | 0x60
            | 0x61
            | 0x62
            | 0x63
            | 0x64
            | 0x65
            | 0x66
            | 0x6a
            | 0x6b
            | 0x6c
            | 0x6d
            | 0x6e
            | 0x6f
            | 0x70
            | 0x71
            | 0x72
            | 0x73
            | 0x74
            | 0x75
            | 0x76
            | 0x77
            | 0x78
            | 0x7c
            | 0x7d
            | 0x7e
            | 0x7f
            | 0x80
            | 0x81
            | 0x82
            | 0x83
            | 0x84
            | 0x85
            | 0x86
            | 0x87
            | 0x88
            | 0x89
            | 0x8a
            | 0x92
            | 0x93
            | 0x94
            | 0x95
            | 0x96
            | 0x97
            | 0x98
            | 0xa0
            | 0xa1
            | 0xa2
            | 0xa3
            | 0xa4
            | 0xa5
            | 0xa6
    )
}

impl<A: Alloc> FunctionCompiler<'_, A> {
    #[inline(always)]
    fn finish_op(&mut self, st: &OpIterState, instruction: Instr) -> VisitResult {
        self.emit(instruction)?;
        self.observe(st)
    }

    /// Lowers one non-structural operator identified by its `operators` tag.
    ///
    /// `a` and `b` carry index or memory immediates and `bits` carries
    /// constant, shuffle, or lane bits. Operators that only move values between
    /// slots or need no code return early; all others emit one instruction.
    pub(super) fn op(
        &mut self,
        st: &OpIterState,
        opcode: u16,
        a: u32,
        b: u32,
        bits: u128,
    ) -> VisitResult {
        if !self.reachable {
            return self.observe(st);
        }
        let instruction = match opcode {
            0x00 => Instr::Unreachable,
            0x01 | 0x1a => return self.observe(st),
            0x10 => {
                let slots = self.func_param_slots[a as usize];
                let base = self
                    .height
                    .checked_sub(slots)
                    .ok_or(VisitError::OutOfMemory)?;
                Instr::Call { func: a, base }
            }
            0x11 => {
                let signature = self.signatures[a as usize];
                let base = self
                    .height
                    .checked_sub(
                        signature
                            .param_slots
                            .checked_add(1)
                            .ok_or(VisitError::OutOfMemory)?,
                    )
                    .ok_or(VisitError::OutOfMemory)?;
                let entry = self.pair(b, a)?;
                Instr::CallIndirect {
                    entry,
                    index: self.operand(1)?,
                    base,
                }
            }
            0x1b | 0x1c => {
                let lhs = self.operand(3)?;
                let rhs = self.operand(2)?;
                let cond = self.operand(1)?;
                if rhs - lhs == 2 {
                    Instr::Select2 {
                        a: lhs,
                        b: rhs,
                        cond,
                    }
                } else {
                    Instr::Select {
                        a: lhs,
                        b: rhs,
                        cond,
                    }
                }
            }
            0x20 => {
                let src = self.local_offsets[a as usize];
                let n = width(self.function.locals[a as usize]);
                self.copy(self.height, src, n)?;
                return self.observe(st);
            }
            0x21 | 0x22 => {
                let dst = self.local_offsets[a as usize];
                let src = self.operand(1)?;
                let n = width(self.function.locals[a as usize]);
                self.copy(dst, src, n)?;
                return self.observe(st);
            }
            0x23 => {
                if top_is_v128(&st.vals) {
                    Instr::GlobalGet2 {
                        dst: self.height,
                        global: a,
                    }
                } else {
                    Instr::GlobalGet {
                        dst: self.height,
                        global: a,
                    }
                }
            }
            0x24 => {
                let src = self.operand(1)?;
                if self.height - src == 2 {
                    Instr::GlobalSet2 { src, global: a }
                } else {
                    Instr::GlobalSet { src, global: a }
                }
            }
            0x25 => Instr::TableGet {
                dst: self.operand(1)?,
                index: self.operand(1)?,
                table: a,
            },
            0x26 => Instr::TableSet {
                index: self.operand(2)?,
                value: self.operand(1)?,
                table: a,
            },
            0x28 | 0x29 | 0x2a | 0x2b | 0x2c | 0x2d | 0x2e | 0x2f | 0x30 | 0x31 | 0x32 | 0x33
            | 0x34 | 0x35 => Instr::make_load(opcode, self.operand(1)?, self.operand(1)?, a)
                .ok_or(VisitError::OutOfMemory)?,
            0x36 | 0x37 | 0x38 | 0x39 | 0x3a | 0x3b | 0x3c | 0x3d | 0x3e => {
                Instr::make_store(opcode, self.operand(2)?, self.operand(1)?, a)
                    .ok_or(VisitError::OutOfMemory)?
            }
            0x3f => Instr::MemorySize { dst: self.height },
            0x40 => Instr::MemoryGrow {
                dst: self.operand(1)?,
            },
            0x41 | 0x43 => Instr::Const32 {
                dst: self.height,
                value: bits as u32,
            },
            0x42 | 0x44 => Instr::Const64 {
                dst: self.height,
                value: bits as u64,
            },
            0x45 | 0x46 | 0x47 | 0x48 | 0x49 | 0x4a | 0x4b | 0x4c | 0x4d | 0x4e | 0x4f | 0x50
            | 0x51 | 0x52 | 0x53 | 0x54 | 0x55 | 0x56 | 0x57 | 0x58 | 0x59 | 0x5a | 0x5b | 0x5c
            | 0x5d | 0x5e | 0x5f | 0x60 | 0x61 | 0x62 | 0x63 | 0x64 | 0x65 | 0x66 | 0x67 | 0x68
            | 0x69 | 0x6a | 0x6b | 0x6c | 0x6d | 0x6e | 0x6f | 0x70 | 0x71 | 0x72 | 0x73 | 0x74
            | 0x75 | 0x76 | 0x77 | 0x78 | 0x79 | 0x7a | 0x7b | 0x7c | 0x7d | 0x7e | 0x7f | 0x80
            | 0x81 | 0x82 | 0x83 | 0x84 | 0x85 | 0x86 | 0x87 | 0x88 | 0x89 | 0x8a | 0x8b | 0x8c
            | 0x8d | 0x8e | 0x8f | 0x90 | 0x91 | 0x92 | 0x93 | 0x94 | 0x95 | 0x96 | 0x97 | 0x98
            | 0x99 | 0x9a | 0x9b | 0x9c | 0x9d | 0x9e | 0x9f | 0xa0 | 0xa1 | 0xa2 | 0xa3 | 0xa4
            | 0xa5 | 0xa6 | 0xa7 | 0xa8 | 0xa9 | 0xaa | 0xab | 0xac | 0xad | 0xae | 0xaf | 0xb0
            | 0xb1 | 0xb2 | 0xb3 | 0xb4 | 0xb5 | 0xb6 | 0xb7 | 0xb8 | 0xb9 | 0xba | 0xbb | 0xbc
            | 0xbd | 0xbe | 0xbf | 0xc0 | 0xc1 | 0xc2 | 0xc3 | 0xc4 | 0x100 | 0x101 | 0x102
            | 0x103 | 0x104 | 0x105 | 0x106 | 0x107 => {
                let depth = if scalar_binary(opcode) { 2 } else { 1 };
                let x = self.operand(depth)?;
                let y = self.operand(1)?;
                Instr::make_scalar(opcode, x, x, y).ok_or(VisitError::OutOfMemory)?
            }
            0xd0 => Instr::RefNull { dst: self.height },
            0xd1 => Instr::RefIsNull {
                dst: self.operand(1)?,
                a: self.operand(1)?,
            },
            0xd2 => Instr::RefFunc {
                dst: self.height,
                func: a,
            },
            0x108 => Instr::MemoryInit {
                d: self.operand(3)?,
                data: a,
            },
            0x109 => Instr::DataDrop { data: a },
            0x10a => Instr::MemoryCopy {
                d: self.operand(3)?,
            },
            0x10b => Instr::MemoryFill {
                d: self.operand(3)?,
            },
            0x10c => {
                let entry = self.pair(a, b)?;
                Instr::TableInit {
                    d: self.operand(3)?,
                    entry,
                }
            }
            0x10d => Instr::ElemDrop { elem: a },
            0x10e => {
                let entry = self.pair(a, b)?;
                Instr::TableCopy {
                    d: self.operand(3)?,
                    entry,
                }
            }
            0x10f => Instr::TableGrow {
                dst: self.operand(2)?,
                table: a,
            },
            0x110 => Instr::TableSize {
                dst: self.height,
                table: a,
            },
            0x111 => Instr::TableFill {
                d: self.operand(3)?,
                table: a,
            },
            0x200 | 0x201 | 0x202 | 0x203 | 0x204 | 0x205 | 0x206 | 0x207 | 0x208 | 0x209
            | 0x20a | 0x20b | 0x20c | 0x20d | 0x20e | 0x20f | 0x210 | 0x211 | 0x212 | 0x213
            | 0x214 | 0x215 | 0x216 | 0x217 | 0x218 | 0x219 | 0x21a | 0x21b | 0x21c | 0x21d
            | 0x21e | 0x21f | 0x220 | 0x221 | 0x222 | 0x223 | 0x224 | 0x225 | 0x226 | 0x227
            | 0x228 | 0x229 | 0x22a | 0x22b | 0x22c | 0x22d | 0x22e | 0x22f | 0x230 | 0x231
            | 0x232 | 0x233 | 0x234 | 0x235 | 0x236 | 0x237 | 0x238 | 0x239 | 0x23a | 0x23b
            | 0x23c | 0x23d | 0x23e | 0x23f | 0x240 | 0x241 | 0x242 | 0x243 | 0x244 | 0x245
            | 0x246 | 0x247 | 0x248 | 0x249 | 0x24a | 0x24b | 0x24c | 0x24d | 0x24e | 0x24f
            | 0x250 | 0x251 | 0x252 | 0x253 | 0x254 | 0x255 | 0x256 | 0x257 | 0x258 | 0x259
            | 0x25a | 0x25b | 0x25c | 0x25d | 0x25e | 0x25f | 0x260 | 0x261 | 0x262 | 0x263
            | 0x264 | 0x265 | 0x266 | 0x267 | 0x268 | 0x269 | 0x26a | 0x26b | 0x26c | 0x26d
            | 0x26e | 0x26f | 0x270 | 0x271 | 0x272 | 0x273 | 0x274 | 0x275 | 0x276 | 0x277
            | 0x278 | 0x279 | 0x27a | 0x27b | 0x27c | 0x27d | 0x27e | 0x27f | 0x280 | 0x281
            | 0x282 | 0x283 | 0x284 | 0x285 | 0x286 | 0x287 | 0x288 | 0x289 | 0x28a | 0x28b
            | 0x28c | 0x28d | 0x28e | 0x28f | 0x290 | 0x291 | 0x292 | 0x293 | 0x294 | 0x295
            | 0x296 | 0x297 | 0x298 | 0x299 | 0x29a | 0x29b | 0x29c | 0x29d | 0x29e | 0x29f
            | 0x2a0 | 0x2a1 | 0x2a2 | 0x2a3 | 0x2a4 | 0x2a5 | 0x2a6 | 0x2a7 | 0x2a8 | 0x2a9
            | 0x2aa | 0x2ab | 0x2ac | 0x2ad | 0x2ae | 0x2af | 0x2b0 | 0x2b1 | 0x2b2 | 0x2b3
            | 0x2b4 | 0x2b5 | 0x2b6 | 0x2b7 | 0x2b8 | 0x2b9 | 0x2ba | 0x2bb | 0x2bc | 0x2bd
            | 0x2be | 0x2bf | 0x2c0 | 0x2c1 | 0x2c2 | 0x2c3 | 0x2c4 | 0x2c5 | 0x2c6 | 0x2c7
            | 0x2c8 | 0x2c9 | 0x2ca | 0x2cb | 0x2cc | 0x2cd | 0x2ce | 0x2cf | 0x2d0 | 0x2d1
            | 0x2d2 | 0x2d3 | 0x2d4 | 0x2d5 | 0x2d6 | 0x2d7 | 0x2d8 | 0x2d9 | 0x2da | 0x2db
            | 0x2dc | 0x2dd | 0x2de | 0x2df | 0x2e0 | 0x2e1 | 0x2e2 | 0x2e3 | 0x2e4 | 0x2e5
            | 0x2e6 | 0x2e7 | 0x2e8 | 0x2e9 | 0x2ea | 0x2eb | 0x2ec | 0x2ed | 0x2ee | 0x2ef
            | 0x2f0 | 0x2f1 | 0x2f2 | 0x2f3 | 0x2f4 | 0x2f5 | 0x2f6 | 0x2f7 | 0x2f8 | 0x2f9
            | 0x2fa | 0x2fb | 0x2fc | 0x2fd | 0x2fe | 0x2ff => {
                return self.simd_op(st, opcode, a, bits);
            }
            _ => return Err(VisitError::OutOfMemory),
        };
        self.finish_op(st, instruction)
    }
}

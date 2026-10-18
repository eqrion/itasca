//! Operator callbacks and their lowering into slot bytecode.
use super::*;

macro_rules! simple_hooks {
    ($($name:ident => $opcode:expr;)*) => { $(
        fn $name(&mut self, st: &OpIterState) -> VisitResult { self.op(st, $opcode, 0, 0, 0) }
    )* };
}
macro_rules! index_hooks {
    ($($name:ident => $opcode:expr;)*) => { $(
        fn $name(&mut self, st: &OpIterState, index: u32) -> VisitResult {
            self.op(st, $opcode, index, 0, 0)
        }
    )* };
}
macro_rules! memory_hooks {
    ($($name:ident => $opcode:expr;)*) => { $(
        fn $name(&mut self, st: &OpIterState, arg: MemArg) -> VisitResult {
            self.op(st, $opcode, arg.offset, arg.align, 0)
        }
    )* };
}

impl<A: Alloc> OpVisitor for FunctionCompiler<'_, A> {
    fn on_function_start(
        &mut self,
        ctx: &Context,
        type_idx: u32,
        body_begin: usize,
        body_end: usize,
    ) -> VisitResult {
        self.function.type_index = type_idx;
        self.function.body_start = self.batch_start + body_begin;
        self.function.body_end = self.batch_start + body_end;
        let sig = self.signatures[type_idx as usize];
        self.function.param_slots = sig.param_slots;
        let mut i = 0;
        let mut result = Ok(());
        while i < ctx.locals.len() && result.is_ok() {
            result = self.add_local(ctx.locals[i]);
            i += 1;
        }
        result?;
        self.height = self.function.local_slots;
        self.function.slot_count = self.height;
        self.budget.charge(CompileResource::Controls)?;
        self.budget.push(
            &mut self.function.controls,
            ControlMap {
                kind: LabelKind::Body,
                source_start: self.function.body_start,
                source_end: 0,
                start_pc: 0,
                end_pc: 0,
                stack_height: 0,
                parameters: 0,
                results: sig.results,
            },
        )?;
        self.budget.push(
            &mut self.frames,
            Frame {
                map: 0,
                kind: LabelKind::Body,
                height: self.height,
                params: 0,
                results: sig.result_slots,
                start_pc: 0,
                if_pc: None,
                entry_reachable: true,
                end_reachable: false,
                fixups: Vec::new(),
            },
        )?;
        Ok(())
    }
    fn on_block(&mut self, st: &OpIterState, bt: BlockType) -> VisitResult {
        self.enter(st, LabelKind::Block, bt)
    }
    fn on_loop(&mut self, st: &OpIterState, bt: BlockType) -> VisitResult {
        self.enter(st, LabelKind::Loop, bt)
    }
    fn on_if(&mut self, st: &OpIterState, bt: BlockType) -> VisitResult {
        self.enter(st, LabelKind::Then, bt)
    }
    fn on_else(&mut self, st: &OpIterState, _bt: BlockType) -> VisitResult {
        let was_reachable = self.reachable;
        let pc = self.function.code.len();
        if self.frames.is_empty() {
            return Err(VisitError::OutOfMemory);
        }
        let frame_index = self.frames.len() - 1;
        let frame = &mut self.frames[frame_index];
        frame.end_reachable |= was_reachable;
        self.reachable = frame.entry_reachable;
        frame.kind = LabelKind::Else;
        let if_pc = frame.if_pc.take();
        if was_reachable {
            self.budget.push(&mut frame.fixups, pc)?;
            self.emit(Instr::Jump { target: u32::MAX })?;
        }
        if let Some(if_pc) = if_pc {
            let target = self.pc()?;
            self.patch(if_pc, target)?;
        }
        self.observe(st)
    }
    fn on_end(&mut self, st: &OpIterState, _kind: LabelKind, _bt: BlockType) -> VisitResult {
        let frame = self.frames.pop().ok_or(VisitError::OutOfMemory)?;
        let target = self.pc()?;
        if let Some(if_pc) = frame.if_pc {
            self.patch(if_pc, target)?;
        }
        let mut i = 0;
        let mut result = Ok(());
        while i < frame.fixups.len() && result.is_ok() {
            result = self.patch(frame.fixups[i], target);
            i += 1;
        }
        result?;
        let map = &mut self.function.controls[frame.map];
        map.end_pc = target as usize;
        map.source_end = self.function.body_start + st.pos;
        self.reachable = self.reachable
            || frame.end_reachable
            || (matches!(frame.kind, LabelKind::Then) && frame.entry_reachable);
        if matches!(frame.kind, LabelKind::Body) {
            let n = if self.reachable { frame.results } else { 0 };
            self.emit(Instr::Return {
                src: frame.height,
                n,
            })?;
        }
        self.observe(st)
    }
    fn on_br(&mut self, st: &OpIterState, depth: u32, _types: ResultType) -> VisitResult {
        if self.reachable {
            self.branch(depth, 0, false)?;
        }
        self.reachable = false;
        self.observe(st)
    }
    fn on_br_if(&mut self, st: &OpIterState, depth: u32, _types: ResultType) -> VisitResult {
        if self.reachable {
            self.branch(depth, 1, true)?;
        }
        self.observe(st)
    }
    fn on_br_table_label(&mut self, _st: &OpIterState, depth: u32) -> VisitResult {
        self.budget.charge(CompileResource::BranchTableEntries)?;
        self.budget.push(&mut self.table_depths, depth)
    }
    fn on_br_table(&mut self, st: &OpIterState, default: u32, _types: ResultType) -> VisitResult {
        self.on_br_table_label(st, default)?;
        if self.reachable {
            self.lower_table_branches()?;
        }
        clear_depths(&mut self.table_depths);
        self.reachable = false;
        self.observe(st)
    }
    fn on_return(&mut self, st: &OpIterState) -> VisitResult {
        if self.reachable {
            let n = self.frames[0].results;
            let src = self.height.checked_sub(n).ok_or(VisitError::OutOfMemory)?;
            self.emit(Instr::Return { src, n })?;
        }
        self.reachable = false;
        self.observe(st)
    }
    fn on_unreachable(&mut self, st: &OpIterState) -> VisitResult {
        if self.reachable {
            self.emit(Instr::Unreachable)?;
        }
        self.reachable = false;
        self.observe(st)
    }
    fn on_call_indirect(&mut self, st: &OpIterState, type_idx: u32, table_idx: u32) -> VisitResult {
        self.op(st, 0x11, type_idx, table_idx, 0)
    }
    fn on_drop(&mut self, st: &OpIterState, _ty: StackType) -> VisitResult {
        self.op(st, 0x1a, 0, 0, 0)
    }
    fn on_select(&mut self, st: &OpIterState, _ty: StackType) -> VisitResult {
        self.op(st, 0x1b, 0, 0, 0)
    }
    fn on_select_typed(&mut self, st: &OpIterState, _ty: ValueType) -> VisitResult {
        self.op(st, 0x1c, 0, 0, 0)
    }
    fn on_i32_const(&mut self, st: &OpIterState, v: i32) -> VisitResult {
        self.op(st, 0x41, 0, 0, v as u32 as u128)
    }
    fn on_i64_const(&mut self, st: &OpIterState, v: i64) -> VisitResult {
        self.op(st, 0x42, 0, 0, v as u64 as u128)
    }
    fn on_f32_const(&mut self, st: &OpIterState, bits: u32) -> VisitResult {
        self.op(st, 0x43, 0, 0, bits as u128)
    }
    fn on_f64_const(&mut self, st: &OpIterState, bits: u64) -> VisitResult {
        self.op(st, 0x44, 0, 0, bits as u128)
    }
    fn on_ref_null(&mut self, st: &OpIterState, ty: ElemType) -> VisitResult {
        let reference_type = if matches!(ty, ElemType::FuncRef) {
            0
        } else {
            1
        };
        self.op(st, 0xd0, reference_type, 0, 0)
    }
    fn on_table_init(&mut self, st: &OpIterState, element: u32, table: u32) -> VisitResult {
        self.op(st, 0x10c, element, table, 0)
    }
    fn on_table_copy(&mut self, st: &OpIterState, destination: u32, source: u32) -> VisitResult {
        self.op(st, 0x10e, destination, source, 0)
    }
    fn on_simd(&mut self, st: &OpIterState, subopcode: u32) -> VisitResult {
        self.op(st, 0x200 + subopcode as u16, 0, 0, 0)
    }
    fn on_simd_lane(&mut self, st: &OpIterState, subopcode: u32, lane: u8) -> VisitResult {
        self.op(st, 0x200 + subopcode as u16, lane as u32, 0, 0)
    }
    fn on_simd_memory(&mut self, st: &OpIterState, subopcode: u32, arg: MemArg) -> VisitResult {
        self.op(st, 0x200 + subopcode as u16, arg.offset, arg.align, 0)
    }
    fn on_simd_memory_lane(
        &mut self,
        st: &OpIterState,
        subopcode: u32,
        arg: MemArg,
        lane: u8,
    ) -> VisitResult {
        self.op(
            st,
            0x200 + subopcode as u16,
            arg.offset,
            arg.align,
            lane as u128,
        )
    }
    fn on_simd_const(&mut self, st: &OpIterState, low: u64, high: u64) -> VisitResult {
        self.op(st, 0x20c, 0, 0, low as u128 | ((high as u128) << 64))
    }
    fn on_simd_shuffle(&mut self, st: &OpIterState, low: u64, high: u64) -> VisitResult {
        self.op(st, 0x20d, 0, 0, low as u128 | ((high as u128) << 64))
    }

    index_hooks! {
        on_call => 0x10;
        on_local_get => 0x20; on_local_set => 0x21; on_local_tee => 0x22;
        on_global_get => 0x23; on_global_set => 0x24;
        on_table_get => 0x25; on_table_set => 0x26;
        on_ref_func => 0xd2;
        on_memory_init => 0x108; on_data_drop => 0x109;
        on_elem_drop => 0x10d; on_table_grow => 0x10f;
        on_table_size => 0x110; on_table_fill => 0x111;
    }
    simple_hooks! {
        on_nop => 0x01; on_memory_size => 0x3f; on_memory_grow => 0x40;
        on_ref_is_null => 0xd1;
        on_memory_copy => 0x10a; on_memory_fill => 0x10b;
        on_i32_extend8_s => 0xc0; on_i32_extend16_s => 0xc1;
        on_i64_extend8_s => 0xc2; on_i64_extend16_s => 0xc3; on_i64_extend32_s => 0xc4;
        on_i32_trunc_sat_f32_s => 0x100; on_i32_trunc_sat_f32_u => 0x101;
        on_i32_trunc_sat_f64_s => 0x102; on_i32_trunc_sat_f64_u => 0x103;
        on_i64_trunc_sat_f32_s => 0x104; on_i64_trunc_sat_f32_u => 0x105;
        on_i64_trunc_sat_f64_s => 0x106; on_i64_trunc_sat_f64_u => 0x107;
    }
    simple_hooks! {
        on_i32_eqz => 0x45;
        on_i32_eq => 0x46;
        on_i32_ne => 0x47;
        on_i32_lt_s => 0x48;
        on_i32_lt_u => 0x49;
        on_i32_gt_s => 0x4a;
        on_i32_gt_u => 0x4b;
        on_i32_le_s => 0x4c;
        on_i32_le_u => 0x4d;
        on_i32_ge_s => 0x4e;
        on_i32_ge_u => 0x4f;
        on_i64_eqz => 0x50;
        on_i64_eq => 0x51;
        on_i64_ne => 0x52;
        on_i64_lt_s => 0x53;
        on_i64_lt_u => 0x54;
        on_i64_gt_s => 0x55;
        on_i64_gt_u => 0x56;
        on_i64_le_s => 0x57;
        on_i64_le_u => 0x58;
        on_i64_ge_s => 0x59;
        on_i64_ge_u => 0x5a;
        on_f32_eq => 0x5b;
        on_f32_ne => 0x5c;
        on_f32_lt => 0x5d;
        on_f32_gt => 0x5e;
        on_f32_le => 0x5f;
        on_f32_ge => 0x60;
        on_f64_eq => 0x61;
        on_f64_ne => 0x62;
        on_f64_lt => 0x63;
        on_f64_gt => 0x64;
        on_f64_le => 0x65;
        on_f64_ge => 0x66;
        on_i32_sub => 0x6b;
        on_i32_mul => 0x6c;
        on_i32_div_s => 0x6d;
        on_i32_div_u => 0x6e;
        on_i32_rem_s => 0x6f;
        on_i32_rem_u => 0x70;
        on_i32_and => 0x71;
        on_i32_or => 0x72;
        on_i32_xor => 0x73;
        on_i32_shl => 0x74;
        on_i32_shr_s => 0x75;
        on_i32_shr_u => 0x76;
        on_i32_rotl => 0x77;
        on_i32_rotr => 0x78;
        on_i64_add => 0x7c;
        on_i64_sub => 0x7d;
        on_i64_mul => 0x7e;
        on_i64_div_s => 0x7f;
        on_i64_div_u => 0x80;
        on_i64_rem_s => 0x81;
        on_i64_rem_u => 0x82;
        on_i64_and => 0x83;
        on_i64_or => 0x84;
        on_i64_xor => 0x85;
        on_i64_shl => 0x86;
        on_i64_shr_s => 0x87;
        on_i64_shr_u => 0x88;
        on_i64_rotl => 0x89;
        on_i64_rotr => 0x8a;
        on_f32_add => 0x92;
        on_f32_sub => 0x93;
        on_f32_mul => 0x94;
        on_f32_div => 0x95;
        on_f32_min => 0x96;
        on_f32_max => 0x97;
        on_f32_copysign => 0x98;
        on_f64_add => 0xa0;
        on_f64_sub => 0xa1;
        on_f64_mul => 0xa2;
        on_f64_div => 0xa3;
        on_f64_min => 0xa4;
        on_f64_max => 0xa5;
        on_f64_copysign => 0xa6;
        on_i32_clz => 0x67;
        on_i32_ctz => 0x68;
        on_i32_popcnt => 0x69;
        on_i32_add => 0x6a;
        on_i64_clz => 0x79;
        on_i64_ctz => 0x7a;
        on_i64_popcnt => 0x7b;
        on_f32_abs => 0x8b;
        on_f32_neg => 0x8c;
        on_f32_ceil => 0x8d;
        on_f32_floor => 0x8e;
        on_f32_trunc => 0x8f;
        on_f32_nearest => 0x90;
        on_f32_sqrt => 0x91;
        on_f64_abs => 0x99;
        on_f64_neg => 0x9a;
        on_f64_ceil => 0x9b;
        on_f64_floor => 0x9c;
        on_f64_trunc => 0x9d;
        on_f64_nearest => 0x9e;
        on_f64_sqrt => 0x9f;
        on_i32_wrap_i64 => 0xa7;
        on_i32_trunc_f32_s => 0xa8;
        on_i32_trunc_f32_u => 0xa9;
        on_i32_trunc_f64_s => 0xaa;
        on_i32_trunc_f64_u => 0xab;
        on_i64_extend_i32_s => 0xac;
        on_i64_extend_i32_u => 0xad;
        on_i64_trunc_f32_s => 0xae;
        on_i64_trunc_f32_u => 0xaf;
        on_i64_trunc_f64_s => 0xb0;
        on_i64_trunc_f64_u => 0xb1;
        on_f32_convert_i32_s => 0xb2;
        on_f32_convert_i32_u => 0xb3;
        on_f32_convert_i64_s => 0xb4;
        on_f32_convert_i64_u => 0xb5;
        on_f32_demote_f64 => 0xb6;
        on_f64_convert_i32_s => 0xb7;
        on_f64_convert_i32_u => 0xb8;
        on_f64_convert_i64_s => 0xb9;
        on_f64_convert_i64_u => 0xba;
        on_f64_promote_f32 => 0xbb;
        on_i32_reinterpret_f32 => 0xbc;
        on_i64_reinterpret_f64 => 0xbd;
        on_f32_reinterpret_i32 => 0xbe;
        on_f64_reinterpret_i64 => 0xbf;
    }
    memory_hooks! {
        on_i32_load => 0x28;
        on_i64_load => 0x29;
        on_f32_load => 0x2a;
        on_f64_load => 0x2b;
        on_i32_load8_s => 0x2c;
        on_i32_load8_u => 0x2d;
        on_i32_load16_s => 0x2e;
        on_i32_load16_u => 0x2f;
        on_i64_load8_s => 0x30;
        on_i64_load8_u => 0x31;
        on_i64_load16_s => 0x32;
        on_i64_load16_u => 0x33;
        on_i64_load32_s => 0x34;
        on_i64_load32_u => 0x35;
        on_i32_store => 0x36;
        on_i64_store => 0x37;
        on_f32_store => 0x38;
        on_f64_store => 0x39;
        on_i32_store8 => 0x3a;
        on_i32_store16 => 0x3b;
        on_i64_store8 => 0x3c;
        on_i64_store16 => 0x3d;
        on_i64_store32 => 0x3e;
    }
}

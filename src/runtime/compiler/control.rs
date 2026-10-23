//! Control labels, slot transfers, and forward branch fixups.
use super::*;

fn block_signature(signatures: &[Signature], bt: BlockType) -> Signature {
    match bt {
        BlockType::Empty => Signature {
            params: 0,
            results: 0,
            param_slots: 0,
            result_slots: 0,
        },
        BlockType::Value(t) => Signature {
            params: 0,
            results: 1,
            param_slots: 0,
            result_slots: width(t),
        },
        BlockType::TypeIndex(index) => signatures[index as usize],
    }
}

fn stack_height(values: &[StackType], count: usize, initial: u32) -> u32 {
    let mut height = initial;
    let mut i = 0;
    while i < count {
        height += stack_width(values[i]);
        i += 1;
    }
    height
}

impl<A: Alloc> FunctionCompiler<'_, A> {
    pub(super) fn lower_table_branches(&mut self) -> VisitResult {
        let start = bounded_index(self.function.jump_tables.len())?;
        let len = bounded_index(self.table_depths.len())?;
        let index = self.operand(1)?;
        self.emit(Instr::JumpTable { index, start, len })?;
        let mut i = 0;
        let mut result = Ok(());
        while i < self.table_depths.len() && result.is_ok() {
            result = self.table_branch(i);
            i += 1;
        }
        result
    }
    fn table_branch(&mut self, index: usize) -> VisitResult {
        let target = self.pc()?;
        self.budget.push(&mut self.function.jump_tables, target)?;
        self.branch(self.table_depths[index], 1, false)
    }
    pub(super) fn branch(&mut self, depth: u32, skip: u32, conditional: bool) -> VisitResult {
        let index = self.frames.len() - 1 - depth as usize;
        let frame = &self.frames[index];
        let dst = frame.height;
        let n = if matches!(frame.kind, LabelKind::Loop) {
            frame.params
        } else {
            frame.results
        };
        let src = self
            .height
            .checked_sub(skip.checked_add(n).ok_or(VisitError::OutOfMemory)?)
            .ok_or(VisitError::OutOfMemory)?;
        let cond = if conditional { self.operand(1)? } else { 0 };
        let copy = n != 0 && src != dst;
        let guard = if conditional && copy {
            let pc = self.function.code.len();
            self.emit(Instr::JumpIfZero {
                cond,
                target: u32::MAX,
            })?;
            Some(pc)
        } else {
            None
        };
        if copy {
            self.copy(dst, src, n)?;
        }
        let pc = self.function.code.len();
        let frame = &mut self.frames[index];
        let target = if matches!(frame.kind, LabelKind::Loop) {
            frame.start_pc
        } else {
            self.budget.push(&mut frame.fixups, pc)?;
            frame.end_reachable = true;
            u32::MAX
        };
        let instruction = if conditional && !copy {
            Instr::JumpIfNonZero { cond, target }
        } else {
            Instr::Jump { target }
        };
        self.emit(instruction)?;
        if let Some(pc) = guard {
            let target = self.pc()?;
            self.patch(pc, target)?;
        }
        Ok(())
    }
    pub(super) fn patch(&mut self, pc: usize, target: u32) -> VisitResult {
        match &mut self.function.code[pc] {
            Instr::Jump { target: t }
            | Instr::JumpIfZero { target: t, .. }
            | Instr::JumpIfNonZero { target: t, .. } => *t = target,
            _ => return Err(VisitError::OutOfMemory),
        }
        Ok(())
    }
    pub(super) fn enter(
        &mut self,
        st: &OpIterState,
        kind: LabelKind,
        bt: BlockType,
    ) -> VisitResult {
        let control_count = st.ctrls.len();
        if control_count == 0 {
            return Err(VisitError::OutOfMemory);
        }
        let value_height = st.ctrls[control_count - 1].value_stack_base;
        let signature = block_signature(self.signatures, bt);
        let height = stack_height(&st.vals, value_height, self.function.local_slots);
        let source_start = self.function.body_start + self.next_source;
        let then_label = matches!(kind, LabelKind::Then);
        let loop_label = matches!(kind, LabelKind::Loop);
        let if_pc = if self.reachable && then_label {
            let pc = self.function.code.len();
            let cond = self.operand(1)?;
            self.emit(Instr::JumpIfZero {
                cond,
                target: u32::MAX,
            })?;
            Some(pc)
        } else {
            None
        };
        let start_pc = self.pc()?;
        if self.reachable && loop_label {
            self.emit(Instr::LoopHead)?;
        }
        let map = self.function.controls.len();
        self.budget.charge(CompileResource::Controls)?;
        self.budget.push(
            &mut self.function.controls,
            ControlMap {
                kind,
                source_start,
                source_end: 0,
                start_pc: start_pc as usize,
                end_pc: 0,
                stack_height: value_height,
                parameters: signature.params,
                results: signature.results,
            },
        )?;
        self.budget.push(
            &mut self.frames,
            Frame {
                map,
                kind,
                height,
                params: signature.param_slots,
                results: signature.result_slots,
                start_pc,
                if_pc,
                entry_reachable: self.reachable,
                end_reachable: false,
                fixups: Vec::new(),
            },
        )?;
        self.observe(st)
    }
}

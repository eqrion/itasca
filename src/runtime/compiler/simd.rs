//! SIMD lowering into flat operators and immediate pools.
use super::*;

impl<A: Alloc> FunctionCompiler<'_, A> {
    pub(super) fn simd_op(
        &mut self,
        st: &OpIterState,
        opcode: u16,
        a: u32,
        bits: u128,
    ) -> VisitResult {
        let instruction = match opcode {
            0x20c => {
                let pool = bounded_index(self.function.v128_pool.len())?;
                self.budget.push(&mut self.function.v128_pool, bits)?;
                Instr::ConstV128 {
                    dst: self.height,
                    pool,
                }
            }
            0x200..=0x2ff => {
                let sub = (opcode - 0x200) as u32;
                let store = sub == 11 || (88 <= sub && sub <= 91);
                let outputs = if store { 0 } else { 1 };
                let consumed = self
                    .before
                    .len()
                    .checked_add(outputs)
                    .ok_or(VisitError::OutOfMemory)?
                    .checked_sub(st.vals.len())
                    .ok_or(VisitError::OutOfMemory)?;
                let src = self.operand(consumed)?;
                let entry = bounded_index(self.function.simd.len())?;
                let lane = if 84 <= sub && sub <= 91 {
                    bits as u32
                } else {
                    a
                };
                self.budget.push(
                    &mut self.function.simd,
                    SimdImmediate {
                        offset: a,
                        lane,
                        bits,
                    },
                )?;
                Instr::make_simd(sub, src, src, entry).ok_or(VisitError::OutOfMemory)?
            }
            _ => return Err(VisitError::OutOfMemory),
        };
        self.emit(instruction)?;
        self.observe(st)
    }
}

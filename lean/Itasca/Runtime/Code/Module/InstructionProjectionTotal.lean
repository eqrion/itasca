import Itasca.Runtime.Code.Module.CodeRegion
import Mathlib.Tactic.IntervalCases
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
@[step] theorem slots_fit_total (f : runtime.bytecode.CompiledFunction) (start count : U32) :
    runtime.bytecode.CompiledFunction.slots_fit f start count ⦃ _ => True ⦄ := by
  unfold runtime.bytecode.CompiledFunction.slots_fit
  split <;> step*

@[step] theorem instruction_scalar_total (instruction : runtime.bytecode.Instr) :
    runtime.bytecode.Instr.scalar instruction ⦃ _ => True ⦄ := by
  cases instruction <;> simp [runtime.bytecode.Instr.scalar]

@[step] theorem instruction_load_total (instruction : runtime.bytecode.Instr) :
    runtime.bytecode.Instr.load instruction ⦃ _ => True ⦄ := by
  cases instruction <;> simp [runtime.bytecode.Instr.load]

@[step] theorem instruction_store_total (instruction : runtime.bytecode.Instr) :
    runtime.bytecode.Instr.store instruction ⦃ _ => True ⦄ := by
  cases instruction <;> simp [runtime.bytecode.Instr.store]

@[step] theorem instruction_simd_total (instruction : runtime.bytecode.Instr) :
    runtime.bytecode.Instr.simd instruction ⦃ result => match result with
      | none => True
      | some (op,_,_,_) => op.val < 256 ⦄ := by
  cases instruction <;> norm_num [runtime.bytecode.Instr.simd, WP.spec_ok]


end Itasca.Runtime.Code

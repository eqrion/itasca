import Exec.Code.Module.InstructionProjectionTotal
import Mathlib.Tactic.IntervalCases
namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
 @[step] theorem simd_shape_total (op : U32) (bound : op.val < 256) :
    runtime.bytecode.simd_shape op ⦃ result => match result with
      | none => True
      | some (a,b,c,d) => a.val ≤ 2 ∧ b.val ≤ 2 ∧ c.val ≤ 2 ∧ d.val ≤ 2 ⦄ := by
  rcases op with ⟨⟨n,hn⟩⟩
  change n < 256 at bound
  interval_cases n <;> with_unfolding_all
    (apply (WP.spec_ok _).mpr; first | exact True.intro | exact ⟨by decide, by decide, by decide, by decide⟩)

@[step] theorem other_valid_total (f : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) :
    runtime.bytecode.CompiledFunction.other_valid f instruction ⦃ _ => True ⦄ := by
  cases instruction <;> simp only [runtime.bytecode.CompiledFunction.other_valid, WP.spec_ok]
  all_goals step*

theorem instruction_valid_total (f : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) :
    runtime.bytecode.CompiledFunction.instruction_valid f instruction ⦃ _ => True ⦄ := by
  unfold runtime.bytecode.CompiledFunction.instruction_valid
  step as ⟨scalar, _⟩
  cases scalar with
  | some values =>
    rcases values with ⟨op, dst, a, b⟩
    simp only [bind_ok]
    step*
  | none =>
    simp only [bind_ok]
    step as ⟨load, _⟩
    cases load with
    | some values =>
      rcases values with ⟨op, dst, addr, offset⟩
      simp only [bind_ok]
      step*
    | none =>
      simp only [bind_ok]
      step as ⟨store, _⟩
      cases store with
      | some values =>
        rcases values with ⟨op, addr, value, offset⟩
        simp only [bind_ok]
        step*
      | none =>
        simp only [bind_ok]
        step as ⟨simd, opcodeBound⟩
        cases simd with
        | some values =>
          rcases values with ⟨op, dst, a, entry⟩
          simp only [bind_ok]
          step with simd_shape_total op opcodeBound as ⟨shape, bounded⟩
          cases shape with
          | none => simp
          | some widths =>
            rcases widths with ⟨x,y,z,out⟩
            simp only [bind_ok]
            step*
        | none =>
          simp only [bind_ok]
          step*
end Exec.Code

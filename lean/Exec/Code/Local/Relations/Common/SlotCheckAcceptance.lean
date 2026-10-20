import Exec.Code.Local.Relations.Common.WellFormed

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Exact arithmetic acceptance of the concrete slot-range check. The upper
bound is expressed in natural coordinates, avoiding unsigned subtraction. -/
theorem slots_fit_accepts (function : runtime.bytecode.CompiledFunction) (start count : U32)
    (inside : start.val+count.val ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.slots_fit function start count = .ok true := by
  have lower : start ≤ function.slot_count := by scalar_tac
  have accepted : runtime.bytecode.CompiledFunction.slots_fit function start count ⦃ result => result = true ⦄ := by
    unfold runtime.bytecode.CompiledFunction.slots_fit
    simp only [if_pos lower]
    step as ⟨remaining,subtracted⟩
    have fits : count ≤ remaining := by scalar_tac
    simp [fits]
  obtain ⟨result,called,rfl⟩ := WP.spec_imp_exists accepted
  exact called

/-- Increasing the function's allocated slot bound retains every slot range
that previously fit. This is used when later source observations raise capacity. -/
theorem slots_fit_monotone (before after : runtime.bytecode.CompiledFunction) (start count : U32)
    (capacity : before.slot_count.val ≤ after.slot_count.val)
    (accepted : runtime.bytecode.CompiledFunction.slots_fit before start count = .ok true) :
    runtime.bytecode.CompiledFunction.slots_fit after start count = .ok true := by
  have inside : start.val+count.val ≤ before.slot_count.val := by
    unfold runtime.bytecode.CompiledFunction.slots_fit at accepted
    split at accepted
    · obtain ⟨remaining,subtracted,returned⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ accepted
      have arithmetic := UScalar.sub_equiv before.slot_count start
      rw [subtracted] at arithmetic
      simp at arithmetic
      have fits : count ≤ remaining := by simpa only [Result.ok.injEq,decide_eq_true_eq] using returned
      scalar_tac
    · simp at accepted
  exact slots_fit_accepts after start count (by omega)

end Exec.Code

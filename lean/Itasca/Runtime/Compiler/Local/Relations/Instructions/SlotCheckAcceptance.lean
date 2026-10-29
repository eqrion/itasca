import Itasca.Runtime.Compiler.Local.Relations.Instructions.WellFormed

/-!
Exact arithmetic acceptance of the concrete slot-range check. The upper bound is expressed in natural coordinates, avoiding unsigned subtraction.

Main declarations: `slots_fit_accepts`. A direct consumer is `Compiler.Local.Relations.Instructions.CoreInstructionAcceptance`.
-/

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

import Exec.Code.Local.Relations.Common.CoreEmissionAcceptance
import Exec.Code.Local.Lowering.Float.FloatInstructionPublication
import Exec.Code.Local.Lowering.Float.FloatCoreEmission

namespace Exec.Code
open Aeneas Aeneas.Std

/-- All ordinary core and scalar float emissions satisfy the instruction
checker from independent source stack capacities. -/
theorem FloatCoreEmission.instructions_accept {C before source emitted after}
    (emission : FloatCoreEmission C before source emitted after)
    (function : runtime.bytecode.CompiledFunction)
    (inputs : slots C.LOCALS+slots before ≤ function.slot_count.val)
    (outputs : slots C.LOCALS+slots after ≤ function.slot_count.val) :
    ∀ instruction ∈ emitted,
      runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  cases emission with
  | core head => exact head.instructions_accept function inputs outputs
  | scalar stack op left right first second =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact float_instruction_accepts function C.LOCALS stack op left right first second inputs

end Exec.Code

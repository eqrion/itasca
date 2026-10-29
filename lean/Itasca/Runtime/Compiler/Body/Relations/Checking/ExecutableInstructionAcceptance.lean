import Itasca.Runtime.Compiler.Body.Relations.Executable.ExecutableEmission
import Itasca.Runtime.Compiler.Local.Relations.Instructions.StatefulInstructionAcceptance
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdInstructionAcceptance

/-!
Explicit select has the same width-specific checker as ordinary select.

Main declarations: `TypedSelectEmission.instructions_accept` and `ExecutableEmission.ordinary_instructions_accept`. A direct consumer is `Compiler.Body.Relations.Checking.ExecutableInstructionPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Explicit select has the same width-specific checker as ordinary select. -/
theorem TypedSelectEmission.instructions_accept {C before source emitted after}
    (emission : TypedSelectEmission C before source emitted after)
    (function : runtime.bytecode.CompiledFunction)
    (inputs : slots C.LOCALS+slots before ≤ function.slot_count.val)
    (outputs : slots C.LOCALS+slots after ≤ function.slot_count.val) :
    ∀ instruction ∈ emitted,
      runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  cases emission with
  | select front ty left right condition first second test =>
    exact (ScalarEmission.select front ty left right condition first second test).instructions_accept function inputs outputs

/-- Every ordinary complete-profile emission passes the bytecode checker from
source stack capacities and the exact retained tables. Branch-table gates are
checked separately with their structural target-table layout. -/
theorem ExecutableEmission.ordinary_instructions_accept (function : runtime.bytecode.CompiledFunction)
    {C before source emitted after}
    (emission : ExecutableEmission (CompilerTables.ofFunction function) C before source emitted after)
    (ordinary : ∀ depths fallback, source ≠ .BR_TABLE depths fallback)
    (inputs : slots C.LOCALS+slots before ≤ function.slot_count.val)
    (outputs : slots C.LOCALS+slots after ≤ function.slot_count.val) :
    ∀ instruction ∈ emitted,
      runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  cases emission with
  | scalar head => exact head.instructions_accept function inputs outputs
  | stateful head => exact head.instructions_accept function rfl inputs outputs
  | indirect head => exact head.instructions_accept function rfl inputs
  | simd head => exact head.instructions_accept function rfl rfl inputs outputs
  | typedSelect head => exact head.instructions_accept function inputs outputs
  | branchTable stack depths fallback selector start len => exact False.elim (ordinary depths fallback rfl)

end Itasca.Runtime.Compiler

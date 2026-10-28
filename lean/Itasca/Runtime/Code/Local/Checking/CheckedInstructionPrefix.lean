import Itasca.Runtime.Code.Local.Relations.Common.InstructionCheckMonotone
import Itasca.Runtime.Code.Local.Callbacks.Table.CompilerTablePreservation
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerMetadata

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Every instruction in this concrete code vector passes its local checker.
Open control fixups require a separate pending-branch invariant. -/
def CheckedInstructionPrefix (function : runtime.bytecode.CompiledFunction) : Prop :=
  ∀ instruction ∈ function.code.val,
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true

theorem CheckedInstructionPrefix.indexed {function : runtime.bytecode.CompiledFunction}
    (held : CheckedInstructionPrefix function) (index : Nat) (bound : index < function.code.length) :
    runtime.bytecode.CompiledFunction.instruction_valid function function.code.val[index] = .ok true :=
  held _ (List.getElem_mem bound)

theorem InstructionCheckExtends.refl (function : runtime.bytecode.CompiledFunction) :
    InstructionCheckExtends function function := ⟨le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl⟩

theorem InstructionCheckExtends.trans {first middle last : runtime.bytecode.CompiledFunction}
    (left : InstructionCheckExtends first middle) (right : InstructionCheckExtends middle last) :
    InstructionCheckExtends first last :=
  ⟨left.slots.trans right.slots,left.code.trans right.code,left.indirect.trans right.indirect,
    left.simd.trans right.simd,left.constants.trans right.constants,left.targets.trans right.targets⟩

/-- Actual emission extends all checker capacities, without changing tables. -/
theorem Emitted.instructionCheckExtends {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} (emitted : Emitted before after instruction) :
    InstructionCheckExtends before.function after.function := by
  obtain ⟨budget,code,sources,rfl,appended,_⟩ := emitted
  refine ⟨le_rfl,?_,le_rfl,le_rfl,le_rfl,le_rfl⟩
  change before.function.code.val.length ≤ code.val.length
  rw [appended,List.length_append,List.length_singleton]
  omega

end Itasca.Runtime.Code

import Exec.Abs.Slice
import Exec.Code.Local.Lowering.Common.NumericEncoding
import Itasca.Spec.DeclaredReferences
namespace Exec.Abs
open Itasca

/-- The integer/control slice contains no reference-producing instruction,
including inside its structured bodies. -/
theorem SliceInstr.declared {instruction} (supported : SliceInstr instruction) (refs : List funcidx) :
    DeclaredReferences.Instruction refs instruction := by
  induction supported <;> try simp_all [DeclaredReferences.Instruction.block_iff,
    DeclaredReferences.Instruction.loop_iff, DeclaredReferences.Instruction.ifElse_iff,
    DeclaredReferences.Instructions.iff_forall, Forall]
  case numeric op => exact Exec.Code.integer_source_declared op refs
  all_goals simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]
end Exec.Abs

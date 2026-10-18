import Exec.Code.Local.Lowering.Float.FloatOpcode
import Itasca.Spec.DeclaredReferences
namespace Exec.Code
open Itasca

theorem float_source_declared (op : Abs.Float.Instruction) (refs : List funcidx) :
    DeclaredReferences.Instruction refs op.source := by
  cases op <;> simp [Abs.Float.Instruction.source,DeclaredReferences.Instruction,DeclaredReferences.instructionIndices]
end Exec.Code

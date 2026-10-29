import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatOpcode
import Itasca.Spec.DeclaredReferences
namespace Itasca.Runtime.Compiler
open Itasca

theorem float_source_declared (op : SourceMachine.Float.Instruction) (refs : List funcidx) :
    DeclaredReferences.Instruction refs op.source := by
  cases op <;> simp [SourceMachine.Float.Instruction.source,DeclaredReferences.Instruction,DeclaredReferences.instructionIndices]
end Itasca.Runtime.Compiler

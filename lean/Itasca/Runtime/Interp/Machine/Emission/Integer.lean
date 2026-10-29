import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Numeric.Integer.NumericCodePoint

/-!
Pure scalar-emission inversion for integer operations.

Main declarations: `scalarEmission_numeric_pure`. A direct consumer is `Interp.Machine.Numeric`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem scalarEmission_numeric_pure {C before after emitted} (op : Abs.Numeric.Instruction)
    (emission : Code.ScalarEmission C before op.source emitted after) :
    Code.LinearEmission C.LOCALS before op.source emitted after := by
  generalize equality : op.source = instruction at emission
  cases emission with
  | linear head => simpa only [equality] using head
  | float stack other =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    cases other <;> simp [Abs.Float.Instruction.source,Abs.Numeric.decodeInstruction] at decoded
  | _ =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction,Abs.Memory.Load.source,Abs.Memory.Store.source] at decoded
end Itasca.Runtime.Interp

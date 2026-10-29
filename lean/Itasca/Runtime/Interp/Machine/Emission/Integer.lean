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

Main declarations: `scalar_emission_numeric_pure`. A direct consumer is `Interp.Machine.Numeric`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem scalar_emission_numeric_pure {C before after emitted} (op : SourceMachine.Numeric.Instruction)
    (emission : Compiler.ScalarEmission C before op.source emitted after) :
    Compiler.LinearEmission C.LOCALS before op.source emitted after := by
  generalize equality : op.source = instruction at emission
  cases emission with
  | linear head => simpa only [equality] using head
  | float stack other =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Numeric.decodeInstruction] at decoded
  | _ =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decodeInstruction,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at decoded
end Itasca.Runtime.Interp

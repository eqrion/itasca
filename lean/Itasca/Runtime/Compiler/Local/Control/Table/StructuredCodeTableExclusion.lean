import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodePoint
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
namespace Itasca.Runtime.Code
open Aeneas.Std

private theorem numeric_not_branchTable (op : Abs.Numeric.Instruction) (depths fallback) :
    op.source ≠ .BR_TABLE depths fallback := by
  cases op with
  | conversion op => cases op <;> simp [Abs.Numeric.Instruction.source,Abs.Numeric.Conversion.source]
  | _ => simp [Abs.Numeric.Instruction.source]

theorem LinearEmission.not_branchTable {locals before instruction emitted after}
    (h : LinearEmission locals before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  cases h with
  | binary stack ty op => cases op <;> simp [IntegerBinary.source]
  | numeric stack op => exact numeric_not_branchTable op depths fallback
  | _ => simp

theorem ScalarEmission.not_branchTable {C before instruction emitted after}
    (h : ScalarEmission C before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  cases h with
  | linear h => exact h.not_branchTable depths fallback
  | float stack op => cases op <;> simp [Abs.Float.Instruction.source]
  | load => simp [Abs.Memory.Load.source]
  | store => simp [Abs.Memory.Store.source]
  | _ => simp

end Itasca.Runtime.Code

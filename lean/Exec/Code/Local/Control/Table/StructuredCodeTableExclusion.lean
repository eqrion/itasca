import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Control.Table.StructuredCodePoint
import Exec.Code.Local.Relations.Common.ScalarEmission
namespace Exec.Code
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

end Exec.Code

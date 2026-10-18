import Exec.Code.Local.Control.Table.StructuredCodeTableLegacy
import Exec.Code.Local.Lowering.Float.FloatCoreEmission
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

theorem CoreEmission.not_branchTable {C before instruction emitted after}
    (h : CoreEmission C before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  cases h with
  | pure h => exact h.not_branchTable depths fallback
  | load => simp [Abs.Memory.Load.source]
  | store => simp [Abs.Memory.Store.source]
  | _ => simp

theorem FloatCoreEmission.not_branchTable {C before instruction emitted after}
    (h : FloatCoreEmission C before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  cases h with
  | core h => exact h.not_branchTable depths fallback
  | scalar stack op => cases op <;> simp [Abs.Float.Instruction.source]
end Exec.Code

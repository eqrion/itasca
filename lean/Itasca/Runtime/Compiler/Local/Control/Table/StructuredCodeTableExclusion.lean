import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodePoint
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
namespace Itasca.Runtime.Compiler
open Aeneas.Std

private theorem numeric_not_branch_table (op : SourceMachine.Numeric.Instruction) (depths fallback) :
    op.source ≠ .BR_TABLE depths fallback := by
  cases op with
  | conversion op => cases op <;> simp [SourceMachine.Numeric.Instruction.source,SourceMachine.Numeric.Conversion.source]
  | _ => simp [SourceMachine.Numeric.Instruction.source]

theorem LinearEmission.not_branch_table {locals before instruction emitted after}
    (h : LinearEmission locals before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  cases h with
  | binary stack ty op => cases op <;> simp [IntegerBinary.source]
  | numeric stack op => exact numeric_not_branch_table op depths fallback
  | _ => simp

theorem ScalarEmission.not_branch_table {C before instruction emitted after}
    (h : ScalarEmission C before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  cases h with
  | linear h => exact h.not_branch_table depths fallback
  | float stack op => cases op <;> simp [SourceMachine.Float.Instruction.source]
  | load => simp [SourceMachine.Memory.Load.source]
  | store => simp [SourceMachine.Memory.Store.source]
  | _ => simp

end Itasca.Runtime.Compiler

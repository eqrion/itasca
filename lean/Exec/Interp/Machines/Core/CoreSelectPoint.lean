import Exec.Code.Local.Relations.Common.ScalarEmission
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Control.Common.StructuredLabels
import Exec.Interp.Control.StructuredPoint
import Exec.Abs.ModuleBindingsExtension
import Exec.Abs.Numeric.Decode
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem linearEmission_not_select {locals before after emitted}
    (emission : Code.LinearEmission locals before (.SELECT none) emitted after) : False := by
  generalize equality : instr.SELECT none = instruction at emission
  cases emission with
  | binary stack ty op a b left right => cases op <;> simp [Code.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction] at decoded
  | _ => cases equality

theorem scalarEmission_select_inv {C before after emitted}
    (emission : Code.ScalarEmission C before (.SELECT none) emitted after) :
    ∃ front ty left right condition, before = front ++ [ty,ty,.I32] ∧
      emitted = [Code.selectInstruction (decide (Code.width ty = 2)) left right condition] ∧
      after = front ++ [ty] ∧ left.val = Code.slots C.LOCALS+Code.slots front ∧
      right.val = left.val+Code.width ty ∧ condition.val = right.val+Code.width ty := by
  generalize equality : instr.SELECT none = instruction at emission
  cases emission with
  | linear pure => rw [← equality] at pure; exact False.elim (linearEmission_not_select pure)
  | select stack ty left right condition leftPos rightPos conditionPos => exact ⟨stack,ty,left,right,condition,rfl,rfl,rfl,leftPos,rightPos,conditionPos⟩
  | float stack other => cases other <;> simp [Abs.Float.Instruction.source,Abs.Memory.Load.source,Abs.Memory.Store.source] at equality
  | _ => simp [Abs.Memory.Load.source,Abs.Memory.Store.source] at equality

end Itasca.Runtime.Interp

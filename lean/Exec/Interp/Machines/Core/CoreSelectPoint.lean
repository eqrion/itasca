import Exec.Interp.Core.Point
import Exec.Abs.Numeric.Decode
namespace Exec.Interp
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

theorem coreEmission_select_inv {C before after emitted}
    (emission : Code.CoreEmission C before (.SELECT none) emitted after) :
    ∃ front ty left right condition, before = front ++ [ty,ty,.I32] ∧
      emitted = [Code.selectInstruction (decide (Code.width ty = 2)) left right condition] ∧
      after = front ++ [ty] ∧ left.val = Code.slots C.LOCALS+Code.slots front ∧
      right.val = left.val+Code.width ty ∧ condition.val = right.val+Code.width ty := by
  generalize equality : instr.SELECT none = instruction at emission
  cases emission with
  | pure pure => rw [← equality] at pure; exact False.elim (linearEmission_not_select pure)
  | select stack ty left right condition leftPos rightPos conditionPos => exact ⟨stack,ty,left,right,condition,rfl,rfl,rfl,leftPos,rightPos,conditionPos⟩
  | _ => simp [Abs.Memory.Load.source,Abs.Memory.Store.source] at equality

theorem corePoint_select_head {C returns code labels stack pc next output} (after : List instr)
    (point : Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
      (.SELECT none :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
        (.SELECT none :: after) target.val next output) ∨
    (∃ front ty left right condition, stack = front ++ [ty,ty,.I32] ∧
      left.val = Code.slots C.LOCALS+Code.slots front ∧ right.val = left.val+Code.width ty ∧
      condition.val = right.val+Code.width ty ∧
      code[pc]? = some (Code.selectInstruction (decide (Code.width ty = 2)) left right condition) ∧
      Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels
        (front ++ [ty]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.SELECT none :: after = source at relation
  cases relation with
  | linear head fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,ty,left,right,condition,input,emitted,result,leftPos,rightPos,conditionPos⟩ := coreEmission_select_inv head
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,ty,left,right,condition,rfl,leftPos,rightPos,conditionPos,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp at sourceEq
end Exec.Interp

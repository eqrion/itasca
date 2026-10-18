import Exec.Interp.Numeric.Float.FloatPoint
import Exec.Code.Local.Lowering.Float.FloatCoreProjection
import Exec.Interp.Machines.Core.CoreSelectPoint
namespace Exec.Interp.FloatSelect
open Aeneas Aeneas.Std SpecExt Exec.Interp
theorem corePoint_select_head {C returns code labels stack pc next output} (after : List instr)
    (point : Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
      (.SELECT none :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
        (.SELECT none :: after) target.val next output) ∨
    (∃ front ty left right condition, stack = front ++ [ty,ty,.I32] ∧
      left.val = Code.slots C.LOCALS+Code.slots front ∧ right.val = left.val+Code.width ty ∧
      condition.val = right.val+Code.width ty ∧
      code[pc]? = some (Code.selectInstruction (decide (Code.width ty = 2)) left right condition) ∧
      Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels
        (front ++ [ty]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.SELECT none :: after = source at relation
  cases relation with
  | linear head fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,ty,left,right,condition,input,emitted,result,leftPos,rightPos,conditionPos⟩ := coreEmission_select_inv (head.core_inv rfl)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,ty,left,right,condition,rfl,leftPos,rightPos,conditionPos,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp at sourceEq

end Exec.Interp.FloatSelect

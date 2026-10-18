import Exec.Interp.StructuredMachine.TypedSelectHeads
import Exec.Code.Local.Lowering.Float.FloatCoreProjection
import Exec.Interp.Machines.Core.CoreSelectPoint
namespace Exec.Interp.StructuredMachine.TypedSelect
variable {jumpTables : List Aeneas.Std.U32}
variable {family : ContextEmission} [TypedSelectHeads family]
open Aeneas Aeneas.Std SpecExt Exec.Interp
theorem point_select_head {declared : valtype} {C returns code labels stack pc next output} (after : List instr)
    (point : Code.StructuredCodeWithTables.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.SELECT (some [declared]) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCodeWithTables.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.SELECT (some [declared]) :: after) target.val next output) ∨
    (∃ front ty left right condition, stack = front ++ [ty,ty,.I32] ∧
      left.val = Code.slots C.LOCALS+Code.slots front ∧ right.val = left.val+Code.width ty ∧
      condition.val = right.val+Code.width ty ∧
      code[pc]? = some (Code.selectInstruction (decide (Code.width ty = 2)) left right condition) ∧
      Code.StructuredCodeWithTables.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (front ++ [ty]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.SELECT (some [declared]) :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    have selected := TypedSelectHeads.project head
    cases selected with
    | select front ty left right condition leftPos rightPos conditionPos =>
      have fetch := fragment.fetch (index := 0) (by rfl)
      obtain ⟨_,_,_,_,nextEq⟩ := fragment
      refine Or.inr ⟨front,declared,left,right,condition,rfl,leftPos,rightPos,conditionPos,by simpa using fetch,?_⟩
      exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp at sourceEq

end Exec.Interp.StructuredMachine.TypedSelect

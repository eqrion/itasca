import Itasca.Runtime.Interp.StructuredMachine.OrdinaryHeads
import Itasca.Runtime.Code.Local.Lowering.Float.FloatEmissionInversion
import Itasca.Runtime.Interp.Machines.Core.CoreSelectPoint
namespace Itasca.Runtime.Interp.StructuredMachine.Select
variable {jumpTables : List Aeneas.Std.U32}
variable {family : ContextEmission} [FloatHeads family]
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp
theorem corePoint_select_head {C returns code labels stack pc next output} (after : List instr)
    (point : Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.SELECT none :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.SELECT none :: after) target.val next output) ∨
    (∃ front ty left right condition, stack = front ++ [ty,ty,.I32] ∧
      left.val = Code.slots C.LOCALS+Code.slots front ∧ right.val = left.val+Code.width ty ∧
      condition.val = right.val+Code.width ty ∧
      code[pc]? = some (Code.selectInstruction (decide (Code.width ty = 2)) left right condition) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (front ++ [ty]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.SELECT none :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,ty,left,right,condition,input,emitted,result,leftPos,rightPos,conditionPos⟩ := scalarEmission_select_inv (FloatHeads.project (.core .select) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,ty,left,right,condition,rfl,leftPos,rightPos,conditionPos,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp at sourceEq

end Itasca.Runtime.Interp.StructuredMachine.Select

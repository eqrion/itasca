import Exec.Interp.StructuredMachine.OrdinaryHeads
import Exec.Code.Local.Lowering.Float.FloatEmissionInversion
import Exec.Interp.State.GlobalCoreEmission

namespace Itasca.Runtime.Interp.StructuredMachine.Global
variable {jumpTables : List Aeneas.Std.U32}
variable {family : ContextEmission} [FloatHeads family]
open Aeneas Aeneas.Std

theorem corePoint_globalGet_head {C returns code labels stack pc next output}
    (index : Nat) (after : List instr)
    (point : Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.GLOBAL_GET (.mk_uN index) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.GLOBAL_GET (.mk_uN index) :: after) target.val next output) ∨
    (∃ mutability ty idx dst, index = idx.val ∧
      C.GLOBALS[index]? = some (.mk_globaltype mutability ty) ∧
      dst.val = Code.slots C.LOCALS + Code.slots stack ∧
      code[pc]? = some (Code.globalGetInstruction (decide (Code.width ty = 2)) dst idx) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (stack ++ [ty]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.GLOBAL_GET (.mk_uN index) :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨mutability,ty,idx,dst,indexEq,lookup,emitted,result,position⟩ := scalarEmission_globalGet_inv index (FloatHeads.project (.core (.global_get (.mk_uN index))) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨mutability,ty,idx,dst,rfl,lookup,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq

theorem corePoint_globalSet_head {C returns code labels stack pc next output}
    (index : Nat) (after : List instr)
    (point : Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.GLOBAL_SET (.mk_uN index) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.GLOBAL_SET (.mk_uN index) :: after) target.val next output) ∨
    (∃ front ty idx src, index = idx.val ∧ stack = front ++ [ty] ∧
      C.GLOBALS[index]? = some (.mk_globaltype (some .MUT) ty) ∧
      src.val = Code.slots C.LOCALS + Code.slots front ∧
      code[pc]? = some (Code.globalSetInstruction (decide (Code.width ty = 2)) src idx) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        front after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.GLOBAL_SET (.mk_uN index) :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,ty,idx,src,indexEq,input,lookup,emitted,result,position⟩ := scalarEmission_globalSet_inv index (FloatHeads.project (.core (.global_set (.mk_uN index))) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,ty,idx,src,rfl,rfl,lookup,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq
end Itasca.Runtime.Interp.StructuredMachine.Global

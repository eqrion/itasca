import Exec.Interp.StructuredMachine.Point
import Exec.Code.Local.Relations.Calls.IndirectCallInversion
namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas.Std
variable {jumpTables : List Aeneas.Std.U32}

/-- The indirect call head is independent of the following instruction family.
The projection is purely syntactic and is discharged by each cumulative emission. -/
theorem indirect_point_head {emission : ContextEmission} {pairs C returns code labels stack pc next output}
    (table type : Nat) (after : List instr)
    (project : ∀ before emitted result,
      emission C before (.CALL_INDIRECT (.mk_uN table) (.mk_uN type)) emitted result →
        Code.IndirectCallEmission pairs C before (.CALL_INDIRECT (.mk_uN table) (.mk_uN type)) emitted result)
    (point : Code.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
      code jumpTables labels stack (.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels stack (.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after) target.val next output) ∨
    (∃ (front params results : List valtype) (typeIndex tableIndex entry index base : U32) (bounds : limits),
      typeIndex.val = type ∧ tableIndex.val = table ∧ stack = (front ++ params) ++ [.I32] ∧
      C.TYPES[type]? = some ⟨.mk_list params,.mk_list results⟩ ∧
      C.TABLES[table]? = some (.mk_tabletype bounds .FUNCREF) ∧
      pairs[entry.val]? = some (tableIndex,typeIndex) ∧
      base.val = Code.slots C.LOCALS + Code.slots front ∧ index.val = base.val + Code.slots params ∧
      code[pc]? = some (.CallIndirect entry index base) ∧
      Code.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels (front ++ results) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,params,results,typeIndex,tableIndex,entry,index,base,bounds,typeEq,tableEq,stackEq,resultEq,emitted,
      signature,tableFound,pair,basePosition,indexPosition⟩ := (project _ _ _ head).invert
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,params,results,typeIndex,tableIndex,entry,index,base,bounds,rfl,rfl,rfl,
      signature,tableFound,pair,basePosition,indexPosition,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp at sourceEq
end Itasca.Runtime.Interp.StructuredMachine

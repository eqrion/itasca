import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallEmission
namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem IndirectCallEmission.invert {pairs C before emitted after table type}
    (head : IndirectCallEmission pairs C before (.CALL_INDIRECT (.mk_uN table) (.mk_uN type)) emitted after) :
    ∃ (front params results : List valtype) (typeIndex tableIndex entry index base : U32) (bounds : limits),
      typeIndex.val = type ∧ tableIndex.val = table ∧
      before = (front ++ params) ++ [.I32] ∧ after = front ++ results ∧
      emitted = [.CallIndirect entry index base] ∧
      C.TYPES[type]? = some ⟨.mk_list params,.mk_list results⟩ ∧
      C.TABLES[table]? = some (.mk_tabletype bounds .FUNCREF) ∧
      pairs[entry.val]? = some (tableIndex,typeIndex) ∧
      base.val = slots C.LOCALS + slots front ∧ index.val = base.val + slots params := by
  generalize sourceEq : instr.CALL_INDIRECT (.mk_uN table) (.mk_uN type) = source at head
  cases head with
  | call front params results typeIndex tableIndex entry index base bounds signature tableFound pair basePosition indexPosition =>
    cases sourceEq
    exact ⟨front,params,results,typeIndex,tableIndex,entry,index,base,bounds,rfl,rfl,rfl,rfl,rfl,
      signature,tableFound,pair,basePosition,indexPosition⟩
end Itasca.Runtime.Compiler

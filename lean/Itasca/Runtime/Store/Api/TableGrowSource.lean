import Itasca.Runtime.Representation.StoreInvariant
import Itasca.Runtime.Store.Api.Grow
import Itasca.Runtime.Store.Invariant.ObjectExtension
import Itasca.Runtime.Interp.State.TableSource
import Itasca.Runtime.Spec.TableGrowth
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

/-- The exact runtime append is the generated table-growth operation. -/
theorem decode_table_growth (old : runtime.store.TableInst) (elements : alloc.vec.Vec U64)
    (delta : U32) (value : U64)
    (values : elements.val = old.elements.val ++ List.replicate delta.val value)
    (capacity : old.elements.length + delta.val ≤ U32.max)
    (maximum : old.elements.length + delta.val ≤ (core.option.Option.unwrap_or old.maximum core.num.U32.MAX).val) :
    fun_growtable (decodeTable old) delta.val (decodeRef old.ty value)
      (some (decodeTable {old with elements})) := by
  have lengthEq : elements.length = old.elements.length + delta.val := by
    simpa only [alloc.vec.Vec.length,List.length_append,List.length_replicate] using congrArg List.length values
  have oldWf : wf_tableinst (decodeTable old) := by
    apply wf_tableinst.tableinst_case_
    apply wf_tabletype.tabletype_case_0
    exact decode_limits_wf _ _ (by omega)
  have freshWf : wf_tableinst (decodeTable {old with elements}) := by
    apply wf_tableinst.tableinst_case_
    apply wf_tabletype.tabletype_case_0
    exact decode_limits_wf _ _ (by simpa only [lengthEq] using capacity)
  have bound : Forall (fun x => old.elements.length + delta.val ≤ proj_uN_0 x)
      (Option.toList (old.maximum.map (fun x => uN.mk_uN x.val))) := by
    cases hm : old.maximum with
    | none => simp [Forall]
    | some mx =>
      intro x member
      simp only [Option.map_some,Option.toList_some,List.mem_singleton] at member
      subst x
      simpa only [hm,core.option.Option.unwrap_or,proj_uN_0] using maximum
  have exactTable : decodeTable {old with elements} =
      {TYPE := .mk_tabletype (.mk_limits (.mk_uN (old.elements.length+delta.val))
        (old.maximum.map (fun x => .mk_uN x.val))) (decodeElemType old.ty),
       REFS := old.elements.val.map (decodeRef old.ty) ++ List.replicate delta.val (decodeRef old.ty value)} := by
    simp only [decodeTable,decode_limits_option]
    simp [OMap,Function.comp_def,values,List.map_append,List.map_replicate,alloc.vec.Vec.length]
  apply fun_growtable.fun_growtable_case_0 _ _ _ _ (.mk_uN old.elements.length)
    (old.maximum.map (fun x => .mk_uN x.val)) (decodeElemType old.ty)
    (old.elements.val.map (decodeRef old.ty)) (old.elements.length+delta.val)
  · simp [decodeTable,decodeLimits,OMap]
  · simp [alloc.vec.Vec.length]
  · exact bound
  · exact exactTable
  · exact freshWf
  · simpa only [← (show ({TYPE := .mk_tabletype (.mk_limits (.mk_uN old.elements.length)
      (old.maximum.map (fun x => .mk_uN x.val))) (decodeElemType old.ty),REFS := old.elements.val.map (decodeRef old.ty)} : tableinst) = decodeTable old by rfl)] using oldWf
  · rw [← exactTable]
    exact freshWf

end Itasca.Runtime.Store

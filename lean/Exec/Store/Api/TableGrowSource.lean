import Exec.Store.Api.TableGrowExtension
import Exec.Interp.State.TableSource
import Exec.Spec.TableGrowth
namespace Exec.Store
open Aeneas Aeneas.Std SpecExt

/-- The exact runtime append is the generated table-growth operation. -/
theorem decode_table_growth (old : runtime.store.Table) (elements : alloc.vec.Vec U64)
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
    exact decodeLimits_wf _ _ (by omega)
  have freshWf : wf_tableinst (decodeTable {old with elements}) := by
    apply wf_tableinst.tableinst_case_
    apply wf_tabletype.tabletype_case_0
    exact decodeLimits_wf _ _ (by simpa only [lengthEq] using capacity)
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
    simp only [decodeTable,decodeLimits_option]
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
/-- Actual table growth follows the generated success or permitted failure
step, including the zero-growth maximum-size sentinel boundary. -/
theorem table_grow_source {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (shape : Shape view store) (syntaxProof : StoreSyntax code store)
    (inst : runtime.store.Instance) (ambient : frame) (table : U32)
    (address : runtime.TableAddr) (object : runtime.store.Table) (delta : U32) (value : U64)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.tables.val[table.val]? = some address)
    (issued : store.tables.val[address.index.val]? = some object)
    (ambientWf : wf_frame ambient) (reference : ReferenceShape store object.ty value) :
    runtime.store.Store.grow_table_index memory allocator store address.index delta value ⦃ out =>
      Shape view out.2 ∧ StoreSyntax code out.2 ∧
      Extend_store (decodeStore view code store) (decodeStore view code out.2) ∧
      StepH ⟨⟨decodeStore view code store,ambient⟩,
        [admininstr_ref (decodeRef object.ty value),Spec.Segment.i32 delta.val,.TABLE_GROW (.mk_uN table.val)]⟩ []
        ⟨⟨decodeStore view code out.2,ambient⟩,[Spec.Segment.i32 out.1.val]⟩ ⦄ := by
  obtain ⟨addressBound,objectFound⟩ := List.getElem?_eq_some_iff.mp issued
  obtain ⟨out,run,effect⟩ := WP.spec_imp_exists (table_grow_effect memory allocator allocation store address.index delta value addressBound
    (fun table member => (shape.tables table member).1))
  have preserved := table_grow_extends memory allocator allocation view code store shape syntaxProof address.index delta value addressBound
    (by simpa only [objectFound] using reference)
  rw [run,WP.spec_ok] at preserved ⊢
  refine ⟨preserved.1,preserved.2.1,preserved.2.2,?_⟩
  have oldWf := decodeStore_wf view code store shape syntaxProof
  rcases effect with ⟨failed,unchanged⟩ | ⟨old,elements,count,lookup,values,capacity,used,limit,maximum,result⟩
  · rw [failed,unchanged]
    have sentinel : core.num.U32.MAX.val = 2^32-1 := by rfl
    rw [sentinel]
    exact Spec.table_grow_fail_step
      (decodeStore view code store) ambient table.val delta.val (decodeRef object.ty value)
      oldWf ambientWf (by scalar_tac) (by scalar_tac)
  · have oldEq : old = object := Option.some.inj (lookup.symm.trans issued)
    subst old
    have oldShape := shape.tables object (List.mem_of_getElem? issued)
    have grown := decode_table_growth object elements delta value values capacity maximum
    have sourceTable := Interp.table_lookup_decodes view code store inst ambient table address object moduleEq mapped issued
    have mapping : ambient.MODULE.TABLES[table.val]! = address.index.val := by
      simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,mapped]
    have decoded : decodeStore view code out.2 =
        {decodeStore view code store with TABLES := (decodeStore view code store).TABLES.modify ambient.MODULE.TABLES[table.val]! (fun _ => decodeTable {object with elements})} := by
      rw [result,mapping,List.modify_eq_set_getElem?]
      simp only [decodeStore,List.getElem?_map,issued,Option.map_some,Option.getD_some,
        alloc.vec.Vec.set_val_eq,List.map_set]
      rfl
    have freshWf := decodeStore_wf view code out.2 preserved.1 preserved.2.1
    rw [decoded] at freshWf
    have originalSize : out.1.val = object.elements.length := by
      rw [result]
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      have bound := oldShape.1
      change object.elements.length < 2^32
      scalar_tac
    have source := Spec.table_grow_success_step (decodeStore view code store) ambient table.val delta.val
      (decodeRef object.ty value) (decodeTable {object with elements}) oldWf ambientWf (by scalar_tac) (by scalar_tac)
      (by simpa [moduleEq,decodeInstance] using (List.getElem?_eq_some_iff.mp mapped).1)
      (by rw [sourceTable]; simp only [decodeTable,List.length_map]; have bound := oldShape.1; scalar_tac)
      (by rw [sourceTable]; exact grown) freshWf
    rw [sourceTable] at source
    rw [decoded,originalSize]
    simpa only [decodeTable,List.length_map,alloc.vec.Vec.length] using source

end Exec.Store

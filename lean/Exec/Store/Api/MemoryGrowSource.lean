import Exec.Store.Api.MemoryGrowExtension
import Exec.Interp.Memory.MemoryDecode
import Exec.Spec.MemoryGrowth
namespace Exec.Store
open Aeneas Aeneas.Std SpecExt

/-- A page-aligned natural byte count has the same rational page quotient used
by the generated memory-growth rule. -/
theorem memory_page_quotient (length : Nat) (aligned : length % 65536 = 0) :
    (length : Rat) / 65536 = ((length / 65536 : Nat) : Rat) := by
  have parts : length = length / 65536 * 65536 := by omega
  conv_lhs => rw [parts]
  push_cast
  ring

theorem decode_memory_growth {M : Type} (view : M → Slice U8)
    (old : runtime.store.MemInst M) (buffer : M) (delta : U32)
    (shape : MemoryShape view old)
    (values : (view buffer).val = (view old.buf).val ++ List.replicate (delta.val * 65536) 0#u8)
    (capacity : (view old.buf).length / 65536 + delta.val ≤ 65536)
    (maximum : (view old.buf).length / 65536 + delta.val ≤
      (core.option.Option.unwrap_or old.maximum 65536#u32).val) :
    fun_growmemory (decodeMemory view old) delta.val
      (some (decodeMemory view {old with buf := buffer})) := by
  have lengths : (view buffer).length = (view old.buf).length + delta.val * 65536 := by
    simpa only [List.length_append,List.length_replicate] using congrArg List.length values
  have pages : (view buffer).length / 65536 = (view old.buf).length / 65536 + delta.val := by omega
  have oldWf : wf_meminst (decodeMemory view old) := by
    apply wf_meminst.meminst_case_
    · apply wf_memtype.memtype_case_0
      exact decodeLimits_wf _ _ (by have bound := shape.2.1; scalar_tac)
    · exact decodeBytes_wf _
  have freshWf : wf_meminst (decodeMemory view {old with buf := buffer}) := by
    apply wf_meminst.meminst_case_
    · apply wf_memtype.memtype_case_0
      exact decodeLimits_wf _ _ (by change (view buffer).length / 65536 ≤ U32.max; rw [pages]; scalar_tac)
    · exact decodeBytes_wf _
  have bound : Forall (fun x => (((view old.buf).length / 65536 + delta.val : Nat) : Rat) ≤ (proj_uN_0 x : Rat))
      (Option.toList (old.maximum.map (fun x => uN.mk_uN x.val))) := by
    cases hm : old.maximum with
    | none => simp [Forall]
    | some mx =>
      intro x member
      simp only [Option.map_some,Option.toList_some,List.mem_singleton] at member
      subst x
      have : (view old.buf).length / 65536 + delta.val ≤ mx.val := by
        simpa only [hm,core.option.Option.unwrap_or] using maximum
      exact_mod_cast this
  have natValue : rat_to_nat (((view old.buf).length / 65536 + delta.val : Nat) : Rat) =
      (view old.buf).length / 65536 + delta.val := by
    simp only [rat_to_nat,Rat.num_natCast,Rat.den_natCast]
    change ((((((view old.buf).length / 65536 + delta.val) : Nat) : _root_.Int).tdiv 1).toNat) = _
    simp only [_root_.Int.tdiv_one,_root_.Int.toNat_natCast]
  have exactMemory : decodeMemory view {old with buf := buffer} =
      {TYPE := .PAGE (.mk_limits (.mk_uN (rat_to_nat (((view old.buf).length / 65536 + delta.val : Nat) : Rat)))
        (old.maximum.map (fun x => .mk_uN x.val))),
       BYTES := decodeBytes (view old.buf).val ++ List.replicate (delta.val * (64 * Ki)) (.mk_byte 0)} := by
    simp only [decodeMemory,decodeLimits_option,natValue,pages]
    simp [OMap,Function.comp_def,decodeBytes,values,List.map_append,List.map_replicate,Ki]
  apply fun_growmemory.fun_growmemory_case_0 _ _ _ (.mk_uN ((view old.buf).length / 65536))
    (old.maximum.map (fun x => .mk_uN x.val)) (decodeBytes (view old.buf).val)
    (((view old.buf).length / 65536 + delta.val : Nat) : Rat)
  · simp [decodeMemory,decodeLimits,OMap]
  · simp only [decodeBytes,List.length_map,Ki]
    norm_num
    rw [memory_page_quotient _ shape.1]
  · exact bound
  · norm_num
    exact_mod_cast capacity
  · exact exactMemory
  · exact freshWf
  · exact oldWf
  · rw [← exactMemory]
    exact freshWf
/-- Actual memory growth implements generated success or permitted refusal;
opaque buffer representation changes on failure preserve the source store. -/
theorem memory_grow_source {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (code : CodeInterpretation) (store : runtime.store.Store M)
    (shape : Shape view store) (syntaxProof : StoreSyntax code store)
    (inst : runtime.store.ModuleInst) (ambient : frame)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M) (delta : U32)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.memories.val[0]? = some address)
    (issued : store.memories.val[address.index.val]? = some object)
    (ambientWf : wf_frame ambient) :
    runtime.store.Store.grow_memory_index memory store address.index delta ⦃ out =>
      Shape view out.2 ∧ StoreSyntax code out.2 ∧
      Extend_store (decodeStore view code store) (decodeStore view code out.2) ∧
      StepH ⟨⟨decodeStore view code store,ambient⟩,[Spec.Segment.i32 delta.val,.MEMORY_GROW]⟩ []
        ⟨⟨decodeStore view code out.2,ambient⟩,[Spec.Segment.i32 out.1.val]⟩ ⦄ := by
  obtain ⟨addressBound,objectFound⟩ := List.getElem?_eq_some_iff.mp issued
  obtain ⟨out,run,effect⟩ := WP.spec_imp_exists (memory_grow_effect memory view laws code store address.index delta addressBound
    (fun m member => (shape.memories m member).length_bound)
    (fun m member => (shape.memories m member).1))
  have preserved := memory_grow_extends memory view laws code store shape syntaxProof address.index delta addressBound
  rw [run,WP.spec_ok] at preserved ⊢
  refine ⟨preserved.1,preserved.2.1,preserved.2.2,?_⟩
  have oldWf := decodeStore_wf view code store shape syntaxProof
  rcases effect with ⟨failed,unchanged,_⟩ |
    ⟨old,buffer,count,lookup,values,used,limit,capacity,maximum,originalSize,result⟩
  · rw [failed,unchanged]
    have sentinel : core.num.U32.MAX.val = 2^32-1 := by rfl
    rw [sentinel]
    exact Spec.memory_grow_fail_step (decodeStore view code store) ambient delta.val oldWf ambientWf (by scalar_tac)
  · have oldEq : old = object := Option.some.inj (lookup.symm.trans issued)
    subst old
    have oldShape := shape.memories object (List.mem_of_getElem? issued)
    have grown := decode_memory_growth view object buffer delta oldShape values capacity maximum
    have sourceMemory := Interp.memory_lookup_decodes view code store inst ambient address object moduleEq mapped issued
    have mapping : ambient.MODULE.MEMS[0]! = address.index.val := by
      simp [moduleEq,decodeInstance,List.getElem!_eq_getElem?_getD,mapped]
    have decoded : decodeStore view code out.2 =
        {decodeStore view code store with MEMS := (decodeStore view code store).MEMS.modify ambient.MODULE.MEMS[0]! (fun _ => decodeMemory view {object with buf := buffer})} := by
      rw [result,mapping,List.modify_eq_set_getElem?]
      simp only [decodeStore,List.getElem?_map,issued,Option.map_some,Option.getD_some,
        alloc.vec.Vec.set_val_eq,List.map_set]
      rfl
    have freshWf := decodeStore_wf view code out.2 preserved.1 preserved.2.1
    rw [decoded] at freshWf
    have source := Spec.memory_grow_success_step (decodeStore view code store) ambient delta.val
      (decodeMemory view {object with buf := buffer}) oldWf ambientWf (by scalar_tac)
      (by simpa [moduleEq,decodeInstance] using (List.getElem?_eq_some_iff.mp mapped).1)
      (by rw [sourceMemory]; simp only [decodeMemory,decodeBytes,List.length_map];
          have bound := oldShape.2.1; scalar_tac)
      (by rw [sourceMemory]; exact grown) freshWf
    rw [sourceMemory] at source
    rw [decoded,originalSize]
    simpa only [decodeMemory,decodeBytes,List.length_map] using source
end Exec.Store

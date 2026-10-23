import Exec.Interp.Relations.InitializerExecute
import Exec.Interp.Relations.ReferenceSource
import Exec.Spec.ReferenceFunction
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt Exec.Store

/-- REF_NULL writes the unique zero-word representation of either null type.
Its source instruction is already a value, so no source reduction is required. -/
theorem ref_null_source_effect
    (exec : runtime.interp.Execution) (base : Usize) (dst : U32)
    (ty : Itasca.types.ElemType) (slotBound : base.val+dst.val < exec.slots.length) :
    runtime.interp.execute_ref_null exec base dst ⦃ out =>
      out.1 = .Ok () ∧ SlotsEffect exec out.2 (exec.slots.val.set (base.val+dst.val) 0#u64) ∧
      decodeRef ty 0#u64 = .REF_NULL (decodeElemType ty) ⦄ := by
  apply WP.spec_mono (ref_null_effect exec base dst slotBound)
  intro out effect
  exact ⟨effect.1,effect.2,by simp [decodeRef]⟩

/-- The encoded address written by actual REF_FUNC is precisely the address
selected by the generated source instruction. -/
theorem ref_func_source_effect {M : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst func : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.FuncAddr) (ambient : frame)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.funcs.val[func.val]? = some address)
    (issued : address.index.val < store.funcs.length)
    (slotBound : base.val+dst.val < exec.slots.length)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (storeWf : wf_store (decodeStore view code store)) (ambientWf : wf_frame ambient) :
    runtime.interp.execute_ref_func memory exec store instanceIndex base dst func ⦃ out =>
      out.1 = .Ok () ∧ out.2.2 = store ∧ ∃ word : U64,
        word.val = address.index.val+1 ∧ decodeRef .FuncRef word = .REF_FUNC_ADDR address.index.val ∧
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) word) ∧
        StepH ⟨⟨decodeStore view code store,ambient⟩,[.REF_FUNC (.mk_uN func.val)]⟩ []
          ⟨⟨decodeStore view code store,ambient⟩,[admininstr_ref (decodeRef .FuncRef word)]⟩ ⦄ := by
  have addressBound : address.index.val < U64.max := by
    have bound := store.funcs.property
    rcases Usize.bounds_eq with h | h <;> scalar_tac
  have source := Spec.ref_func_step (decodeStore view code store) ambient func.val address.index.val storeWf ambientWf
    (by scalar_tac) (by simp [moduleEq,decodeInstance,List.getElem?_map,mapped])
  apply WP.spec_mono (ref_func_effect memory exec store instanceIndex base dst func inst address found mapped addressBound slotBound)
  intro out effect
  obtain ⟨success,same,word,wordEq,slots⟩ := effect
  have decoded : decodeRef .FuncRef word = .REF_FUNC_ADDR address.index.val := by
    simp [decodeRef,wordEq]
  exact ⟨success,same,word,wordEq,decoded,slots,by simpa only [decoded,admininstr_ref] using source⟩
end Exec.Interp

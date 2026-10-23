import Exec.Interp.Memory.MemoryGrow
import Exec.Interp.Relations.FrameStoreMetadata
import Exec.Store.Api.MemoryGrowSource
import Exec.Theorems.Composition.Certified.CertifiedCoreContent
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

/-- Actual MEMORY_GROW preserves the decoded Core store certificate and follows
source success or permitted refusal, even when opaque allocation refusal changes
the buffer representation without changing its byte view. -/
theorem memory_grow_instruction_certified {M : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M) (amount : U64) (ambient : frame)
    (certified : CertifiedCoreStore view code store)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address)
    (issued : store.memories.val[address.index.val]? = some object)
    (amountSlot : exec.slots.val[base.val+dst.val]? = some amount)
    (moduleEq : ambient.MODULE = decodeInstance store inst) (ambientWf : wf_frame ambient) :
    runtime.interp.execute_memory_grow memory exec store instanceIndex base dst ⦃ out =>
      out.1 = .Ok () ∧ CertifiedCoreStore view code out.2.2 ∧ FrameStoreMetadata store out.2.2 ∧
      Extend_store (decodeStore view code store) (decodeStore view code out.2.2) ∧
      ∃ result : U32, SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 result)) ∧
        StepH ⟨⟨decodeStore view code store,ambient⟩,
          [Spec.Segment.i32 (UScalar.cast .U32 amount).val,.MEMORY_GROW]⟩ []
          ⟨⟨decodeStore view code out.2.2,ambient⟩,[Spec.Segment.i32 result.val]⟩ ⦄ := by
  let post : U32 × runtime.store.Store M → Prop := fun out =>
    CertifiedCoreStore view code out.2 ∧ FrameStoreMetadata store out.2 ∧
      Extend_store (decodeStore view code store) (decodeStore view code out.2) ∧
      StepH ⟨⟨decodeStore view code store,ambient⟩,
        [Spec.Segment.i32 (UScalar.cast .U32 amount).val,.MEMORY_GROW]⟩ []
        ⟨⟨decodeStore view code out.2,ambient⟩,[Spec.Segment.i32 out.1.val]⟩
  have primitive : runtime.store.Store.grow_memory_index memory store address.index (UScalar.cast .U32 amount) ⦃ post ⦄ := by
    obtain ⟨result,run,source⟩ := WP.spec_imp_exists (memory_grow_source memory view laws code store certified.shape certified.storeSyntax
      inst ambient address object (UScalar.cast .U32 amount) moduleEq mapped issued ambientWf)
    have effect := memory_grow_effect memory view laws code store address.index (UScalar.cast .U32 amount)
      (List.getElem?_eq_some_iff.mp issued).1
      (fun m member => (certified.shape.memories m member).length_bound)
      (fun m member => (certified.shape.memories m member).1)
    rw [run,WP.spec_ok] at effect ⊢
    dsimp only [post]
    refine ⟨?_,?_,source.2.2.1,source.2.2.2⟩
    · rcases effect with ⟨_,_,unchanged | ⟨old,buffer,lookup,viewEq,changed⟩⟩ |
        ⟨old,buffer,count,lookup,values,used,limit,capacity,maximum,originalSize,changed⟩
      · simpa only [unchanged] using certified
      · exact certified.content_update (by rw [changed]) (by rw [changed]) (by rw [changed]) (by rw [changed]) (by rw [changed]) (by rw [changed]) source.1 source.2.2.1
      · exact certified.content_update (by rw [changed]) (by rw [changed]) (by rw [changed]) (by rw [changed]) (by rw [changed]) (by rw [changed]) source.1 source.2.2.1
    · rcases effect with ⟨_,_,unchanged | ⟨old,buffer,lookup,viewEq,changed⟩⟩ |
        ⟨old,buffer,count,lookup,values,used,limit,capacity,maximum,originalSize,changed⟩
      · rw [unchanged]; exact .refl _
      · rw [changed]; exact ⟨rfl,rfl,rfl,rfl⟩
      · rw [changed]; exact ⟨rfl,rfl,rfl,rfl⟩
  apply WP.spec_mono (memory_grow_handler memory exec store instanceIndex base dst inst address amount
    found mapped amountSlot post primitive)
  intro out effect
  obtain ⟨result,success,⟨fresh,metadata,extension,source⟩,slots⟩ := effect
  exact ⟨success,fresh,metadata,extension,result,slots,source⟩
end Exec.Theorems

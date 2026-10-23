import Exec.Interp.State.TableGrow
import Exec.Interp.Relations.FrameStoreMetadata
import Exec.Store.Api.TableGrowSource
import Exec.Theorems.Composition.Certified.CertifiedCoreContent
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

/-- Actual TABLE_GROW is total under allocator correctness, preserves the
Core store certificate, and follows the generated success/failure source rule. -/
theorem table_grow_instruction_certified {M A : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst table : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (reference amount : U64) (ambient : frame)
    (certified : CertifiedCoreStore view code store)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address)
    (issued : store.tables.val[address.index.val]? = some object)
    (referenceSlot : exec.slots.val[base.val+dst.val]? = some reference)
    (amountSlot : exec.slots.val[base.val+dst.val+1]? = some amount)
    (moduleEq : ambient.MODULE = decodeInstance store inst) (ambientWf : wf_frame ambient)
    (owned : ReferenceShape store object.ty reference) :
    runtime.interp.execute_table_grow memory allocator exec store instanceIndex base dst table ⦃ out =>
      out.1 = .Ok () ∧ CertifiedCoreStore view code out.2.2 ∧ FrameStoreMetadata store out.2.2 ∧
      Extend_store (decodeStore view code store) (decodeStore view code out.2.2) ∧
      ∃ result : U32, SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 result)) ∧
        StepH ⟨⟨decodeStore view code store,ambient⟩,
          [admininstr_ref (decodeRef object.ty reference),Spec.Segment.i32 (UScalar.cast .U32 amount).val,.TABLE_GROW (.mk_uN table.val)]⟩ []
          ⟨⟨decodeStore view code out.2.2,ambient⟩,[Spec.Segment.i32 result.val]⟩ ⦄ := by
  let post : U32 × runtime.store.Store M → Prop := fun out =>
    CertifiedCoreStore view code out.2 ∧ FrameStoreMetadata store out.2 ∧
      Extend_store (decodeStore view code store) (decodeStore view code out.2) ∧
      StepH ⟨⟨decodeStore view code store,ambient⟩,
        [admininstr_ref (decodeRef object.ty reference),Spec.Segment.i32 (UScalar.cast .U32 amount).val,.TABLE_GROW (.mk_uN table.val)]⟩ []
        ⟨⟨decodeStore view code out.2,ambient⟩,[Spec.Segment.i32 out.1.val]⟩
  have primitive : runtime.store.Store.grow_table_index memory allocator store address.index (UScalar.cast .U32 amount) reference ⦃ post ⦄ := by
    obtain ⟨result,run,source⟩ := WP.spec_imp_exists (table_grow_source memory allocator allocation view code store certified.shape certified.storeSyntax
      inst ambient table address object (UScalar.cast .U32 amount) reference moduleEq mapped issued ambientWf owned)
    have effect := table_grow_effect memory allocator allocation store address.index (UScalar.cast .U32 amount) reference
      (List.getElem?_eq_some_iff.mp issued).1 (fun table member => (certified.shape.tables table member).1)
    rw [run,WP.spec_ok] at effect ⊢
    dsimp only [post]
    refine ⟨?_,?_,source.2.2.1,source.2.2.2⟩
    · rcases effect with ⟨_,unchanged⟩ | ⟨old,elements,count,lookup,values,capacity,used,limit,maximum,changed⟩
      · simpa only [unchanged] using certified
      · exact certified.content_update (by rw [changed]) (by rw [changed]) (by rw [changed]) (by rw [changed]) (by rw [changed]) (by rw [changed]) source.1 source.2.2.1
    · rcases effect with ⟨_,unchanged⟩ | ⟨old,elements,count,lookup,values,capacity,used,limit,maximum,changed⟩
      · rw [unchanged]; exact .refl _
      · rw [changed]; exact ⟨rfl,rfl,rfl,rfl⟩
  apply WP.spec_mono (table_grow_handler memory allocator exec store instanceIndex base dst table inst address reference amount
    found mapped referenceSlot amountSlot post primitive)
  intro out effect
  obtain ⟨result,success,⟨fresh,metadata,extension,source⟩,slots⟩ := effect
  exact ⟨success,fresh,metadata,extension,result,slots,source⟩
end Exec.Theorems

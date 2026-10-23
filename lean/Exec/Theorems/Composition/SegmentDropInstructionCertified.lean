import Exec.Store.Initialization.SegmentDropExecution
import Exec.Store.Initialization.SegmentObjectEffects
import Exec.Theorems.Composition.Certified.CertifiedCoreSegments
import Exec.Interp.Relations.FrameStoreMetadata
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

theorem data_drop_core_certified {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (index : U32) (address : Usize) (ambient : frame)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.datas.val[index.val]? = some address) (issued : address.val < store.datas.length)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (certified : CertifiedCoreStore view code store) (ambientWf : wf_frame ambient) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.DataDrop index) ⦃ out =>
      out.1 = .Ok () ∧ CertifiedCoreStore view code out.2 ∧
      Extend_store (decodeStore view code store) (decodeStore view code out.2) ∧ FrameStoreMetadata store out.2 ∧
      StepH ⟨⟨decodeStore view code store,ambient⟩,[.DATA_DROP (.mk_uN index.val)]⟩ []
        ⟨⟨decodeStore view code out.2,ambient⟩,[]⟩ ⦄ := by
  apply WP.spec_mono (bulk_data_drop memory store instIndex function base slots inst index address found mapped issued)
  rintro out rfl
  have metadata := SegmentObjectMetadata.data_drop view store address store.datas.val[address.val] (List.getElem?_eq_getElem issued)
  obtain ⟨fresh,extension⟩ := certified.segments metadata (certified.shape.data_drop address)
  exact ⟨rfl,fresh,extension,⟨rfl,rfl,rfl,rfl⟩,
    data_drop_refines view code store inst ambient index address store.datas.val[address.val]
      certified.shape certified.storeSyntax ambientWf moduleEq mapped (List.getElem?_eq_getElem issued)⟩

theorem element_drop_core_certified {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (index : U32) (address : Usize) (ambient : frame)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.elems.val[index.val]? = some address) (issued : address.val < store.elems.length)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (certified : CertifiedCoreStore view code store) (ambientWf : wf_frame ambient) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.ElemDrop index) ⦃ out =>
      out.1 = .Ok () ∧ CertifiedCoreStore view code out.2 ∧
      Extend_store (decodeStore view code store) (decodeStore view code out.2) ∧ FrameStoreMetadata store out.2 ∧
      StepH ⟨⟨decodeStore view code store,ambient⟩,[.ELEM_DROP (.mk_uN index.val)]⟩ []
        ⟨⟨decodeStore view code out.2,ambient⟩,[]⟩ ⦄ := by
  apply WP.spec_mono (bulk_element_drop memory store instIndex function base slots inst index address found mapped issued)
  rintro out rfl
  have metadata := SegmentObjectMetadata.element_drop view store address store.elems.val[address.val] (List.getElem?_eq_getElem issued)
  obtain ⟨fresh,extension⟩ := certified.segments metadata (certified.shape.element_drop address store.elems.val[address.val])
  exact ⟨rfl,fresh,extension,⟨rfl,rfl,rfl,rfl⟩,
    element_drop_refines view code store inst ambient index address store.elems.val[address.val]
      certified.shape certified.storeSyntax ambientWf moduleEq mapped (List.getElem?_eq_getElem issued)⟩
end Exec.Theorems

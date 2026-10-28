import Itasca.Runtime.Store.Initialization.SegmentDropSemantics

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

theorem bulk_data_drop_refines {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (index : U32) (address : Usize) (ambient : frame)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.datas.val[index.val]? = some address) (issued : address.val < store.datas.length)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (ambientWf : wf_frame ambient)
    (moduleEq : ambient.MODULE = decodeInstance store inst) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.DataDrop index)
      ⦃ out => out.1 = .Ok () ∧
        StepH ⟨⟨decodeStore view code store,ambient⟩,[.DATA_DROP (.mk_uN index.val)]⟩ []
          ⟨⟨decodeStore view code out.2,ambient⟩,[]⟩ ⦄ := by
  apply WP.spec_mono (bulk_data_drop memory store instIndex function base slots inst index address found mapped issued)
  rintro out rfl
  exact ⟨rfl, data_drop_refines view code store inst ambient index address store.datas.val[address.val]
    shape sourceSyntax ambientWf moduleEq mapped (List.getElem?_eq_getElem issued)⟩

theorem bulk_element_drop_refines {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (instIndex function base : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (index : U32) (address : Usize) (ambient : frame)
    (found : store.instances.val[instIndex.val]? = some inst)
    (mapped : inst.elems.val[index.val]? = some address) (issued : address.val < store.elems.length)
    (shape : Shape view store) (sourceSyntax : StoreSyntax code store) (ambientWf : wf_frame ambient)
    (moduleEq : ambient.MODULE = decodeInstance store inst) :
    runtime.interp.bulk.execute memory store instIndex function base slots (.ElemDrop index)
      ⦃ out => out.1 = .Ok () ∧
        StepH ⟨⟨decodeStore view code store,ambient⟩,[.ELEM_DROP (.mk_uN index.val)]⟩ []
          ⟨⟨decodeStore view code out.2,ambient⟩,[]⟩ ⦄ := by
  apply WP.spec_mono (bulk_element_drop memory store instIndex function base slots inst index address found mapped issued)
  rintro out rfl
  exact ⟨rfl, element_drop_refines view code store inst ambient index address store.elems.val[address.val]
    shape sourceSyntax ambientWf moduleEq mapped (List.getElem?_eq_getElem issued)⟩

end Itasca.Runtime.Store

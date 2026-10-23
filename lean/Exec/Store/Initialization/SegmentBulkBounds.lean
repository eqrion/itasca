import Exec.Store.Initialization.SegmentCompatible
import Exec.Store.Initialization.SegmentBoundsEffects

namespace Exec.Store
open Aeneas Aeneas.Std

theorem segment_bulk_bounds {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (instIndex function : Usize) (slots : Slice U64)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (capacity : (∃ entry, instruction = .MemoryInit 0#u32 entry ∨ instruction = .TableInit 0#u32 entry) → 3 ≤ slots.length)
    (ready : SegmentBulkReady store inst code instruction)
    (bounded : SegmentBounds store) :
    runtime.interp.bulk.execute memory store instIndex function 0#usize slots instruction
      ⦃ out => SegmentBounds out.2 ⦄ := by
  cases ready with
  | memory data address target mapped issued mappedMemory issuedMemory =>
    have capacity := capacity ⟨data, Or.inl rfl⟩
    change 3 ≤ slots.val.length at capacity
    have slot0 : slots.val[0]? = some slots.val[0] := List.getElem?_eq_getElem (by omega)
    have slot1 : slots.val[1]? = some slots.val[1] := List.getElem?_eq_getElem (by omega)
    have slot2 : slots.val[2]? = some slots.val[2] := List.getElem?_eq_getElem (by omega)
    apply WP.spec_mono (bulk_memory_init memory view laws store instIndex function slots inst data address target
      store.memories.val[target.index.val] store.datas.val[address.val] _ _ _ found mapped
      (List.getElem?_eq_getElem issued) mappedMemory (List.getElem?_eq_getElem issuedMemory) slot0 slot1 slot2)
    intro out effect
    exact effect.bounds bounded
  | table entry element tableId address target descriptor mapped issued mappedTable issuedTable =>
    have capacity := capacity ⟨entry, Or.inr rfl⟩
    change 3 ≤ slots.val.length at capacity
    have slot0 : slots.val[0]? = some slots.val[0] := List.getElem?_eq_getElem (by omega)
    have slot1 : slots.val[1]? = some slots.val[1] := List.getElem?_eq_getElem (by omega)
    have slot2 : slots.val[2]? = some slots.val[2] := List.getElem?_eq_getElem (by omega)
    apply WP.spec_mono (bulk_table_init memory store instIndex function slots inst code entry element tableId address target
      store.tables.val[target.index.val] store.elems.val[address.val] _ _ _ found functionFound descriptor mapped
      (List.getElem?_eq_getElem issued) mappedTable (List.getElem?_eq_getElem issuedTable) slot0 slot1 slot2)
    intro out effect
    exact effect.bounds bounded
  | dataDrop data address mapped issued =>
    apply WP.spec_mono (bulk_data_drop memory store instIndex function 0#usize slots inst data address found mapped issued)
    rintro out rfl
    exact SegmentBounds.data_drop store bounded address store.datas.val[address.val]
  | elementDrop element address mapped issued =>
    apply WP.spec_mono (bulk_element_drop memory store instIndex function 0#usize slots inst element address found mapped issued)
    rintro out rfl
    exact SegmentBounds.element_drop store bounded address _


end Exec.Store

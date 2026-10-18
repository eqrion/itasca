import Exec.Store.Initialization.SegmentStep

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Segment execution changes buffers, table words and dropped-segment contents,
but preserves the address spaces and every constant-read/code lookup. -/
structure SegmentAddressSpace {M : Type} (before after : runtime.store.Store M) : Prop where
  identity : after.id = before.id
  functions : after.funcs = before.funcs
  signatures : after.types = before.types
  globals : after.globals = before.globals
  instances : after.instances = before.instances
  tables : after.tables.length = before.tables.length
  memories : after.memories.length = before.memories.length
  elements : after.elems.length = before.elems.length
  datas : after.datas.length = before.datas.length
  frozen : after = {before with tables := after.tables, memories := after.memories, elems := after.elems, datas := after.datas}

theorem SegmentAddressSpace.refl {M : Type} (store : runtime.store.Store M) :
    SegmentAddressSpace store store := by constructor <;> rfl

theorem SegmentAddressSpace.trans {M : Type} {a b c : runtime.store.Store M}
    (ab : SegmentAddressSpace a b) (bc : SegmentAddressSpace b c) : SegmentAddressSpace a c := by
  constructor
  all_goals first
    | exact bc.identity.trans ab.identity
    | exact bc.functions.trans ab.functions
    | exact bc.signatures.trans ab.signatures
    | exact bc.globals.trans ab.globals
    | exact bc.instances.trans ab.instances
    | exact bc.tables.trans ab.tables
    | exact bc.memories.trans ab.memories
    | exact bc.elements.trans ab.elements
    | exact bc.datas.trans ab.datas
    | rw [bc.frozen, ab.frozen]

/-- Issued indices required by the four emitted bulk instruction forms. Buffer
range bounds are deliberately absent: their failure is an ordinary Wasm trap. -/
inductive SegmentBulkReady {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.Instance) (code : runtime.bytecode.CompiledFunction) : runtime.bytecode.Instr → Prop where
  | memory (data : U32) (address : Usize) (memory : runtime.MemoryAddr)
      (mapped : inst.data.val[data.val]? = some address) (issued : address.val < store.datas.length)
      (mappedMemory : inst.memories.val[0]? = some memory) (issuedMemory : memory.index.val < store.memories.length) :
      SegmentBulkReady store inst code (.MemoryInit 0#u32 data)
  | table (entry element tableId : U32) (address : Usize) (table : runtime.TableAddr)
      (descriptor : code.indirect.val[entry.val]? = some (element, tableId))
      (mapped : inst.elements.val[element.val]? = some address) (issued : address.val < store.elems.length)
      (mappedTable : inst.tables.val[tableId.val]? = some table) (issuedTable : table.index.val < store.tables.length) :
      SegmentBulkReady store inst code (.TableInit 0#u32 entry)
  | dataDrop (data : U32) (address : Usize)
      (mapped : inst.data.val[data.val]? = some address) (issued : address.val < store.datas.length) :
      SegmentBulkReady store inst code (.DataDrop data)
  | elementDrop (element : U32) (address : Usize)
      (mapped : inst.elements.val[element.val]? = some address) (issued : address.val < store.elems.length) :
      SegmentBulkReady store inst code (.ElemDrop element)

theorem SegmentBulkReady.kind {M : Type} {store : runtime.store.Store M} {inst code instruction}
    (ready : SegmentBulkReady store inst code instruction) : SegmentBulk instruction := by
  cases ready <;> constructor

theorem SegmentBulkReady.transport {M : Type} {store after : runtime.store.Store M}
    {inst code instruction} (ready : SegmentBulkReady store inst code instruction)
    (same : SegmentAddressSpace store after) : SegmentBulkReady after inst code instruction := by
  cases ready with
  | memory data address memory mapped issued mappedMemory issuedMemory =>
    exact .memory data address memory mapped (same.datas.symm ▸ issued) mappedMemory (same.memories.symm ▸ issuedMemory)
  | table entry element tableId address table descriptor mapped issued mappedTable issuedTable =>
    exact .table entry element tableId address table descriptor mapped (same.elements.symm ▸ issued)
      mappedTable (same.tables.symm ▸ issuedTable)
  | dataDrop data address mapped issued => exact .dataDrop data address mapped (same.datas.symm ▸ issued)
  | elementDrop element address mapped issued => exact .elementDrop element address mapped (same.elements.symm ▸ issued)

def SegmentStatus (result : core.result.Result Unit runtime.ExecError) : Prop :=
  result = .Ok () ∨ result = .Err (.Trap .MemoryOutOfBounds) ∨ result = .Err (.Trap .TableOutOfBounds)

private theorem memory_effect_metadata {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {index memory segment destination source count out}
    (effect : MemoryInitializationEffect view store index memory segment destination source count out) :
    SegmentStatus out.1 ∧ SegmentAddressSpace store out.2 := by
  unfold MemoryInitializationEffect at effect
  split at effect
  · obtain ⟨buffer, rfl, _⟩ := effect
    constructor
    · exact Or.inl rfl
    · constructor <;> simp
  · rw [effect]
    exact ⟨Or.inr (Or.inl rfl), .refl store⟩

private theorem table_effect_metadata {M : Type} {store : runtime.store.Store M}
    {index table segment destination source count out}
    (effect : TableInitializationEffect store index table segment destination source count out) :
    SegmentStatus out.1 ∧ SegmentAddressSpace store out.2 := by
  unfold TableInitializationEffect at effect
  split at effect
  · obtain ⟨words, rfl, _⟩ := effect
    constructor
    · exact Or.inl rfl
    · constructor <;> simp
  · rw [effect]
    exact ⟨Or.inr (Or.inr rfl), .refl store⟩

theorem segment_bulk_total {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (instIndex function : Usize) (slots : Slice U64)
    (inst : runtime.store.Instance) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr)
    (found : store.instances.val[instIndex.val]? = some inst)
    (functionFound : inst.module.functions.val[function.val]? = some code)
    (capacity : (∃ entry, instruction = .MemoryInit 0#u32 entry ∨ instruction = .TableInit 0#u32 entry) → 3 ≤ slots.length)
    (ready : SegmentBulkReady store inst code instruction) :
    runtime.interp.bulk.execute memory store instIndex function 0#usize slots instruction
      ⦃ out => SegmentStatus out.1 ∧ SegmentAddressSpace store out.2 ⦄ := by
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
    exact memory_effect_metadata effect
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
    exact table_effect_metadata effect
  | dataDrop data address mapped issued =>
    apply WP.spec_mono (bulk_data_drop memory store instIndex function 0#usize slots inst data address found mapped issued)
    rintro out rfl
    constructor
    · exact Or.inl rfl
    · constructor <;> simp
  | elementDrop element address mapped issued =>
    apply WP.spec_mono (bulk_element_drop memory store instIndex function 0#usize slots inst element address found mapped issued)
    rintro out rfl
    constructor
    · exact Or.inl rfl
    · constructor <;> simp

end Exec.Store

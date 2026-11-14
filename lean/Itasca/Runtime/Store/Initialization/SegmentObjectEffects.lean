import Itasca.Runtime.Store.Initialization.SegmentExtension

/-!
Sections, each formerly its own module: SegmentCompatible, SegmentObjectEffects.
-/

/-! ## SegmentCompatible -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- For an emitted table initialization, source-segment words and destination
slots have the same reference type. Other instructions impose no type equality. -/
def SegmentBulkCompatible {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) : Prop :=
  match instruction with
  | .TableInit _ entry => ∀ element tableId address target segment table,
      code.indirect.val[entry.val]? = some (element, tableId) →
      inst.elems.val[element.val]? = some address → inst.tables.val[tableId.val]? = some target →
      store.elems.val[address.val]? = some segment → store.tables.val[target.index.val]? = some table →
      segment.ty = table.ty
  | _ => True

theorem SegmentBulkCompatible.transport {M : Type} {store after : runtime.store.Store M}
    {inst code instruction} (compatible : SegmentBulkCompatible store inst code instruction)
    (same : SegmentTypes store after) : SegmentBulkCompatible after inst code instruction := by
  cases instruction <;> simp only [SegmentBulkCompatible] at compatible ⊢
  all_goals try trivial
  intro element tableId address target segment table descriptor mapped tableMapped sourceFound targetFound
  have elementTags := congrArg (fun values : List Itasca.wasm_types.ElemType => values[address.val]?) same.elements
  have tableTags := congrArg (fun values : List Itasca.wasm_types.ElemType => values[target.index.val]?) same.tables
  simp only [List.getElem?_map, sourceFound, Option.map_some] at elementTags
  simp only [List.getElem?_map, targetFound, Option.map_some] at tableTags
  cases oldSource : store.elems.val[address.val]? with
  | none => simp [oldSource] at elementTags
  | some oldSegment =>
    cases oldTarget : store.tables.val[target.index.val]? with
    | none => simp [oldTarget] at tableTags
    | some oldTable =>
      have sourceType : segment.ty = oldSegment.ty := by simpa [oldSource] using elementTags
      have targetType : table.ty = oldTable.ty := by simpa [oldTarget] using tableTags
      rw [sourceType, targetType]
      exact compatible element tableId address target oldSegment oldTable descriptor mapped tableMapped oldSource oldTarget

/-- Source typing and source/raw type-map agreement establish the needed equality
for a compiler-selected active element segment. -/
theorem segment_table_compatible {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (entry element tableId : U32) (segment : Itasca.metadata.Element) (tableType : Itasca.wasm_types.TableType)
    (descriptor : code.indirect.val[entry.val]? = some (element, tableId))
    (source : inst.module.module.env.elements.val[element.val]? = some segment)
    (target : inst.module.module.env.table_types.val[tableId.val]? = some tableType)
    (same : segment.elem = tableType.elem) (bindings : SegmentTypeBindings store inst) :
    SegmentBulkCompatible store inst code (.TableInit 0#u32 entry) := by
  intro actualElement actualTable address tableAddress values table actualDescriptor mapped tableMapped valuesFound tableFound
  have pair := Option.some.inj (actualDescriptor.symm.trans descriptor)
  have first := congrArg Prod.fst pair
  have second := congrArg Prod.snd pair
  dsimp only at first second
  subst actualElement actualTable
  rw [bindings.elements element.val segment address values source mapped valuesFound,
    bindings.tables tableId.val tableType tableAddress table target tableMapped tableFound, same]

end Itasca.Runtime.Store

end

/-! ## SegmentObjectEffects -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem TableInitializationEffect.object_metadata {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {index table segment destination source count out}
    (effect : TableInitializationEffect store index table segment destination source count out)
    (target : store.tables.val[index.val]? = some table) : SegmentObjectMetadata view store out.2 := by
  unfold TableInitializationEffect at effect
  split at effect
  · obtain ⟨words, rfl, values⟩ := effect
    have length : words.length = table.elements.length := by
      simpa only [alloc.vec.Vec.length] using (congrArg List.length values).trans (copy_segment_length _ _ _ _ _)
    refine ⟨by constructor <;> simp, ?_, ?_, ?_, ?_⟩
    · simpa only [alloc.vec.Vec.set_val_eq] using lookup_set_relation store.tables.val index.val table
        {table with elements := words} target
        (fun old next => next.ty = old.ty ∧ next.maximum = old.maximum ∧ next.elements.length = old.elements.length)
        (fun _ => ⟨rfl,rfl,rfl⟩) ⟨rfl,rfl,length⟩
    · intro i old found; exact ⟨old, found, rfl,rfl⟩
    · intro i old found; exact ⟨old, found, rfl,Or.inl rfl⟩
    · intro i old found; exact ⟨old, found, Or.inl rfl⟩
  · rw [effect]; exact .refl _ _

theorem MemoryInitializationEffect.object_metadata {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {index memory segment destination source count out}
    (effect : MemoryInitializationEffect view store index memory segment destination source count out)
    (target : store.memories.val[index.val]? = some memory) : SegmentObjectMetadata view store out.2 := by
  unfold MemoryInitializationEffect at effect
  split at effect
  · obtain ⟨buffer, rfl, values⟩ := effect
    have length : (view buffer).length = (view memory.buf).length := by
      simpa only [List.length_setSlice!] using congrArg List.length values
    refine ⟨by constructor <;> simp, ?_, ?_, ?_, ?_⟩
    · intro i old found; exact ⟨old, found, rfl,rfl,rfl⟩
    · simpa only [alloc.vec.Vec.set_val_eq] using lookup_set_relation store.memories.val index.val memory
        {memory with buf := buffer} target
        (fun old next => next.maximum = old.maximum ∧ (view next.buf).length = (view old.buf).length)
        (fun _ => ⟨rfl,rfl⟩) ⟨rfl,length⟩
    · intro i old found; exact ⟨old, found, rfl,Or.inl rfl⟩
    · intro i old found; exact ⟨old, found, Or.inl rfl⟩
  · rw [effect]; exact .refl _ _

theorem SegmentObjectMetadata.data_drop {M : Type} (view : M → Slice U8)
    (store : runtime.store.Store M) (index : Usize) (old : runtime.store.DataInst)
    (target : store.datas.val[index.val]? = some old) :
    SegmentObjectMetadata view store {store with datas := store.datas.set index ⟨alloc.vec.Vec.new U8⟩} := by
  refine ⟨by constructor <;> simp, ?_, ?_, ?_, ?_⟩
  · intro i old found; exact ⟨old, found, rfl,rfl,rfl⟩
  · intro i old found; exact ⟨old, found, rfl,rfl⟩
  · intro i old found; exact ⟨old, found, rfl,Or.inl rfl⟩
  · simpa only [alloc.vec.Vec.set_val_eq] using lookup_set_relation store.datas.val index.val old
      ⟨alloc.vec.Vec.new U8⟩ target
      (fun old next => next.bytes.val = old.bytes.val ∨ next.bytes.val = [])
      (fun _ => Or.inl rfl) (Or.inr rfl)

theorem SegmentObjectMetadata.element_drop {M : Type} (view : M → Slice U8)
    (store : runtime.store.Store M) (index : Usize) (old : runtime.store.ElemInst)
    (target : store.elems.val[index.val]? = some old) :
    SegmentObjectMetadata view store {store with elems := store.elems.set index {old with refs := alloc.vec.Vec.new U64}} := by
  refine ⟨by constructor <;> simp, ?_, ?_, ?_, ?_⟩
  · intro i old found; exact ⟨old, found, rfl,rfl,rfl⟩
  · intro i old found; exact ⟨old, found, rfl,rfl⟩
  · simpa only [alloc.vec.Vec.set_val_eq] using lookup_set_relation store.elems.val index.val old
      {old with refs := alloc.vec.Vec.new U64} target
      (fun old next => next.ty = old.ty ∧ (next.refs.val = old.refs.val ∨ next.refs.val = []))
      (fun _ => ⟨rfl,Or.inl rfl⟩) ⟨rfl,Or.inr rfl⟩
  · intro i old found; exact ⟨old, found, Or.inl rfl⟩

end Itasca.Runtime.Store

end

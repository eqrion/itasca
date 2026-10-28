import Itasca.Runtime.Store.Initialization.SegmentObjectMetadata

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
      simpa only [alloc.vec.Vec.length] using (congrArg List.length values).trans (copySegment_length _ _ _ _ _)
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

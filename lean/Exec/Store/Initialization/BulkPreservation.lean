import Exec.Store.Initialization.BulkMemory
import Exec.Store.Invariant.FunctionTables

namespace Exec.Store
open Aeneas Aeneas.Std

theorem copySegment_all (predicate : U64 → Prop) (before source : List U64)
    (dst src count : Nat) (sourceBound : src + count ≤ source.length)
    (old : ∀ word ∈ before, predicate word) (input : ∀ word ∈ source, predicate word) :
    ∀ word ∈ copySegment before source dst src count, predicate word := by
  induction count with
  | zero => exact old
  | succ n ih =>
    intro word member
    simp only [copySegment] at member
    rcases List.mem_or_eq_of_mem_set member with previous | changed
    · exact ih (by omega) word previous
    · subst word
      have bound : src + n < source.length := by omega
      exact input _ (by simp [bound])

theorem TableInitializationEffect.shape {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {tableIndex : Usize} {table : runtime.store.TableInst}
    {segment : runtime.store.ElemInst} {destination source count : U64}
    {out : core.result.Result Unit runtime.ExecError × runtime.store.Store M}
    (effect : TableInitializationEffect store tableIndex table segment destination source count out)
    (shape : Shape view store) (target : store.tables.val[tableIndex.val]? = some table)
    (references : ∀ word ∈ segment.refs.val, ReferenceShape store table.ty word) : Shape view out.2 := by
  unfold TableInitializationEffect at effect
  split at effect
  · rename_i fits
    obtain ⟨words, rfl, values⟩ := effect
    have bound := (List.getElem?_eq_some_iff.mp target).1
    have read := (List.getElem?_eq_some_iff.mp target).2
    have old := shape.tables table (List.mem_of_getElem? target)
    have length : words.length = table.elements.length := by
      simpa only [alloc.vec.Vec.length] using (congrArg List.length values).trans (copySegment_length _ _ _ _ _)
    apply shape.table_replace_same_length tableIndex bound {table with elements := words}
    · refine ⟨by simpa [length] using old.1, ?_, ?_⟩
      · simpa [length] using old.2.1
      · intro word member
        rw [values] at member
        exact copySegment_all (ReferenceShape store table.ty) _ _ _ _ _ fits.2 old.2.2 references word member
    · simpa only [read] using length
  · rw [effect]
    exact shape

theorem MemoryInitializationEffect.shape {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {memoryIndex : Usize} {memory : runtime.store.MemInst M}
    {segment : runtime.store.DataInst} {destination source count : U64}
    {out : core.result.Result Unit runtime.ExecError × runtime.store.Store M}
    (effect : MemoryInitializationEffect view store memoryIndex memory segment destination source count out)
    (shape : Shape view store) (target : store.memories.val[memoryIndex.val]? = some memory) : Shape view out.2 := by
  unfold MemoryInitializationEffect at effect
  split at effect
  · obtain ⟨buffer, rfl, values⟩ := effect
    have bound := (List.getElem?_eq_some_iff.mp target).1
    have read := (List.getElem?_eq_some_iff.mp target).2
    apply shape.memory_replace_same_length memoryIndex bound {memory with buf := buffer}
    · have lengths := congrArg List.length values
      simpa only [List.length_setSlice!, read] using lengths
    · simp only [read]
  · rw [effect]
    exact shape

theorem Shape.data_drop {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    (shape : Shape view store) (address : Usize) :
    Shape view {store with datas := store.datas.set address ⟨alloc.vec.Vec.new U8⟩} := by
  constructor
  · exact shape.identity
  · simpa [FunctionShape] using shape.functions
  · exact shape.memories
  · simpa [TableShape, ReferenceShape] using shape.tables
  · simpa [GlobalShape, ReferenceShape] using shape.globals
  · simpa [ReferenceShape] using shape.elements
  · simpa [InstanceShape] using shape.instances
  · exact shape.canonicalTypes
  · exact shape.objectLimit
  · exact shape.instanceLimit
  · exact shape.instanceAccounting
  · exact shape.instanceItemLimit
  · exact shape.signatureAccounting
  · exact shape.signatureLimit
  · exact shape.memoryAccounting
  · exact shape.memoryLimit
  · exact shape.tableAccounting
  · exact shape.tableLimit

theorem Shape.element_drop {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    (shape : Shape view store) (address : Usize) (segment : runtime.store.ElemInst) :
    Shape view {store with elems := store.elems.set address {segment with refs := alloc.vec.Vec.new U64}} := by
  have elements : ∀ e ∈ (store.elems.set address {segment with refs := alloc.vec.Vec.new U64}).val,
      ∀ word ∈ e.refs.val, ReferenceShape store e.ty word := by
    intro e member
    simp only [alloc.vec.Vec.set_val_eq] at member
    rcases List.mem_or_eq_of_mem_set member with previous | changed
    · exact shape.elements e previous
    · subst e; simp
  constructor
  · exact shape.identity
  · simpa [FunctionShape] using shape.functions
  · exact shape.memories
  · simpa [TableShape, ReferenceShape] using shape.tables
  · simpa [GlobalShape, ReferenceShape] using shape.globals
  · simpa [ReferenceShape] using elements
  · simpa [InstanceShape] using shape.instances
  · exact shape.canonicalTypes
  · exact shape.objectLimit
  · exact shape.instanceLimit
  · exact shape.instanceAccounting
  · exact shape.instanceItemLimit
  · exact shape.signatureAccounting
  · exact shape.signatureLimit
  · exact shape.memoryAccounting
  · exact shape.memoryLimit
  · exact shape.tableAccounting
  · exact shape.tableLimit

end Exec.Store

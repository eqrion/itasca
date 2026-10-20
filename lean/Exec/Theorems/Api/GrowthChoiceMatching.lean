import Exec.Store.Api.Grow
import Exec.Spec.Choices.Steps
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- The observable Wasm reply uses the failure sentinel, independently of a
buffer's opaque representation changes on refusal. -/
def memoryGrowthReply {M : Type} (view : M → Slice U8) (index : Usize)
    (out : U32 × runtime.store.Store M) : Option meminst :=
  if out.1.val=2^32-1 then none else (out.2.memories.val[index.val]?).map (Store.decodeMemory view)

def tableGrowthReply {M : Type} (index : Usize)
    (out : U32 × runtime.store.Store M) : Option tableinst :=
  if out.1.val=2^32-1 then none else (out.2.tables.val[index.val]?).map Store.decodeTable

/-- Primitive growth compatibility is a law of actual API replies on concrete
objects. It assumes no invocation result, source trace, or exhaustion exclusion. -/
structure GrowthChoicesCompatible {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (view : M → Slice U8) (choices : Spec.SourceChoices) : Prop where
  memoryReply : ∀ occurrence (store : runtime.store.Store M) index delta object out,
    store.memories.val[index.val]?=some object →
    runtime.store.Store.grow_memory_index memory store index delta=.ok out →
    choices.memory occurrence (Store.decodeMemory view object) delta.val=memoryGrowthReply view index out
  tableReply : ∀ occurrence (store : runtime.store.Store M) index delta value object out,
    store.tables.val[index.val]?=some object →
    runtime.store.Store.grow_table_index memory allocator store index delta value=.ok out →
    choices.table occurrence (Store.decodeTable object) delta.val (Store.decodeRef object.ty value)=tableGrowthReply index out
end Exec.Theorems

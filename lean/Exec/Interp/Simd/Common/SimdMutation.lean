import Exec.Interp.Memory.MemoryMutation
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- SIMD retains the store or replaces the opaque buffer of one issued memory
without changing its length. Source semantics separately constrain its bytes. -/
def SimdStoreMutation {M : Type} (view : M → Slice U8)
    (before after : runtime.store.Store M) : Prop :=
  after = before ∨ ∃ address object, before.memories.val[address.index.val]? = some object ∧
    MemoryMutation view before after address object

theorem SimdStoreMutation.frame_metadata {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} (mutation : SimdStoreMutation view before after) :
    FrameStoreMetadata before after := by
  rcases mutation with rfl | ⟨address,object,issued,mutation⟩
  · exact ⟨rfl,rfl,rfl,rfl⟩
  · exact mutation.frame_metadata
end Exec.Interp

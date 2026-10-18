import Exec.Interp.Memory.MemoryMutation
import Exec.Interp.State.GlobalMutation
import Exec.Abs.Ownership.Core
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A live source value is already present in an operand or local region, or
in the invocation's final result vector. -/
def CoreLiveValue (source : Abs.AState) (value : val) : Prop :=
  value ∈ source.results ∨ ∃ f ∈ source.frames, value ∈ f.locals ∨ value ∈ f.vals

theorem CoreLiveValue.owned {bounds source value} (present : CoreLiveValue source value)
    (owned : Abs.Ownership.CoreOwned bounds source) : Abs.Ownership.ValueOwned bounds value := by
  rcases present with member | ⟨f,frame,member | member⟩
  · exact owned.values.1 value member
  · exact (owned.values.2 f frame).1 value member
  · exact (owned.values.2 f frame).2 value member

/-- Concrete scalar execution changes only payloads of existing objects.
Global writes carry their original live source value, retaining provenance. -/
inductive CoreStoreMutation {M : Type} (view : M → Slice U8) (source : Abs.AState)
    (before : runtime.store.Store M) : runtime.store.Store M → Prop where
  | unchanged : CoreStoreMutation view source before before
  | memory {after address object} (issued : before.memories.val[address.index.val]? = some object)
      (mutation : MemoryMutation view before after address object) : CoreStoreMutation view source before after
  | global {after value} (live : CoreLiveValue source value) (wellFormed : wf_val value)
      (mutation : GlobalMutation before after value) : CoreStoreMutation view source before after

theorem CoreStoreMutation.metadata {M : Type} {view source} {before after : runtime.store.Store M}
    (mutation : CoreStoreMutation view source before after) : FrameStoreMetadata before after := by
  cases mutation with
  | unchanged => exact .refl _
  | memory issued mutation => exact mutation.frame_metadata
  | global live wellFormed mutation => exact mutation.frame_metadata

theorem CoreStoreMutation.externs {M : Type} {view source} {before after : runtime.store.Store M}
    (mutation : CoreStoreMutation view source before after) : after.externs = before.externs := by
  cases mutation with
  | unchanged => rfl
  | memory issued mutation => obtain ⟨buffer,rfl,_⟩ := mutation; rfl
  | global live wellFormed mutation => obtain ⟨index,old,lo,hi,_,_,_,_,_,rfl⟩ := mutation; rfl
theorem CoreStoreMutation.segments {M : Type} {view source} {before after : runtime.store.Store M}
    (mutation : CoreStoreMutation view source before after) :
    after.elems = before.elems ∧ after.datas = before.datas := by
  cases mutation with
  | unchanged => exact ⟨rfl,rfl⟩
  | memory issued mutation => obtain ⟨buffer,rfl,_⟩ := mutation; exact ⟨rfl,rfl⟩
  | global live wellFormed mutation => obtain ⟨index,old,lo,hi,_,_,_,_,_,rfl⟩ := mutation; exact ⟨rfl,rfl⟩
end Exec.Interp

import Exec.Interp.Memory.MemoryDescriptor
import Exec.Interp.Relations.FrameStoreMetadata

namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt
open Exec.Store

/-- A scalar memory instruction changes only the selected opaque buffer and
retains its byte length. This includes bounds failures whose writeback callback
chooses a different representation of the same bytes. -/
def MemoryMutation {M : Type} (view : M → Slice U8) (before after : runtime.store.Store M)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M) : Prop :=
  ∃ buffer, after = {before with memories := before.memories.set address.index {object with buf := buffer}} ∧
    (view buffer).length = (view object.buf).length

theorem MemoryMutation.frame_metadata {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} {address object}
    (mutation : MemoryMutation view before after address object) : FrameStoreMetadata before after := by
  obtain ⟨buffer,rfl,lengthEq⟩ := mutation
  exact ⟨rfl,rfl,rfl,rfl⟩

end Exec.Interp

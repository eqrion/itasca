import Exec.Interp.Relations.FrameStorePrefix
import Exec.Store.Invariant.Extension
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem FrameStorePrefix.of_staged {M : Type} {before after : runtime.store.Store M}
    (staged : Store.StagedPrefix before after) : FrameStorePrefix before after :=
  ⟨staged.identity,staged.funcs,staged.types,staged.instances⟩

theorem frame_type_bounds_of_shape {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} (shape : Store.Shape view store) : FrameTypeBounds store := by
  intro inst member index present
  exact (shape.instances inst member).2.2.2.2.2.2.2.1 index present

end Exec.Interp

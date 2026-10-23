import Exec.Interp.StructuredMachine.FrameStack
import Exec.Interp.Relations.FrameStorePrefix
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std

theorem SavedFrame.store_prefix_extension {M : Type} {before after : runtime.store.Store M}
    {oldSource newSource : _root_.store} (retained : FrameStorePrefix before after) (bounds : FrameTypeBounds before)
    (extension : Extend_store oldSource newSource) {exec raw source waiting childBase}
    (saved : SavedFrame before oldSource exec raw source waiting childBase) :
    SavedFrame after newSource exec raw source waiting childBase := by
  refine ⟨saved.binding.store_prefix retained bounds,saved.slots,saved.destination,?_⟩
  obtain ⟨compiled,C,targets,next,output,program,point⟩ := saved.continuation
  exact ⟨compiled,C,targets,next,output,program.store_prefix retained,point.extend extension⟩

theorem SavedFrames.store_prefix_extension {M : Type} {before after : runtime.store.Store M}
    {oldSource newSource : _root_.store} (retained : FrameStorePrefix before after) (bounds : FrameTypeBounds before)
    (extension : Extend_store oldSource newSource) {exec raws sources waiting base}
    (saved : SavedFrames before oldSource exec raws sources waiting base) :
    SavedFrames after newSource exec raws sources waiting base := by
  induction saved with
  | nil waiting => exact .nil waiting
  | cons head tail ih => exact .cons (head.store_prefix_extension retained bounds extension) ih

end Exec.Interp.StructuredMachine

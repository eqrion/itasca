import Exec.Interp.StructuredMachine.FrameStack
import Exec.Interp.Relations.FrameStorePrefix
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std
variable {emission : FunctionEmission}

theorem SavedFrame.store_prefix_extension {M : Type} {before after : runtime.store.Store M}
    {oldSource newSource : _root_.store} (retained : FrameStorePrefix before after) (bounds : FrameTypeBounds before)
    (extension : Extend_store oldSource newSource) {exec raw source waiting childBase}
    (saved : SavedFrame emission before oldSource exec raw source waiting childBase) :
    SavedFrame emission after newSource exec raw source waiting childBase := by
  refine ⟨saved.binding.store_prefix retained bounds,saved.slots,saved.destination,?_⟩
  obtain ⟨compiled,C,targets,next,output,program,point⟩ := saved.continuation
  exact ⟨compiled,C,targets,next,output,program.store_prefix retained,point.extend extension⟩

theorem SavedFrames.store_prefix_extension {M : Type} {before after : runtime.store.Store M}
    {oldSource newSource : _root_.store} (retained : FrameStorePrefix before after) (bounds : FrameTypeBounds before)
    (extension : Extend_store oldSource newSource) {exec raws sources waiting base}
    (saved : SavedFrames emission before oldSource exec raws sources waiting base) :
    SavedFrames emission after newSource exec raws sources waiting base := by
  induction saved with
  | nil waiting => exact .nil waiting
  | cons head tail ih => exact .cons (head.store_prefix_extension retained bounds extension) ih

theorem ActiveFrame.store_prefix_extension {M : Type} {before after : runtime.store.Store M}
    {oldSource newSource : _root_.store} (retained : FrameStorePrefix before after) (bounds : FrameTypeBounds before)
    (extension : Extend_store oldSource newSource) {exec raw source}
    (active : ActiveFrame emission before oldSource exec raw source) : ActiveFrame emission after newSource exec raw source := by
  refine ⟨active.binding.store_prefix retained bounds,active.slots,?_⟩
  obtain ⟨compiled,C,targets,next,output,pending,program,point⟩ := active.continuation
  exact ⟨compiled,C,targets,next,output,pending,program.store_prefix retained,point.extend extension⟩

theorem FrameStackRel.store_prefix_extension {M : Type} {before after : runtime.store.Store M}
    {oldSource newSource : _root_.store} (retained : FrameStorePrefix before after) (bounds : FrameTypeBounds before)
    (extension : Extend_store oldSource newSource) {exec sources}
    (stack : FrameStackRel emission before oldSource exec sources) : FrameStackRel emission after newSource exec sources := by
  cases stack with
  | empty frames => exact .empty frames
  | active frames top saved => exact .active frames (top.store_prefix_extension retained bounds extension) (saved.store_prefix_extension retained bounds extension)

theorem ReadyTop.store_prefix_extension {M : Type} {before after : runtime.store.Store M}
    {oldSource newSource : _root_.store} (retained : FrameStorePrefix before after)
    (extension : Extend_store oldSource newSource) {exec source}
    (ready : ReadyTop emission before oldSource exec source) : ReadyTop emission after newSource exec source := by
  obtain ⟨raw,compiled,C,targets,next,output,top,program,point⟩ := ready
  exact ⟨raw,compiled,C,targets,next,output,top,program.store_prefix retained,point.extend extension⟩

end Exec.Interp.StructuredMachine

import Exec.Interp.Host.HostReturnFrames
import Exec.Interp.StructuredMachine.FrameStorePrefix

namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std

theorem SavedFrame.resume_host {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {base : Nat} {raw : runtime.interp.Frame}
    {source : Abs.AFrame} {waiting : List valtype} {results : List val}
    (saved : SavedFrame store sourceStore before raw source waiting base)
    (effect : HostReturnEffect before after base results)
    (types : results.map Code.valueType = waiting) (heights : Abs.FrameHeights source) :
    ActiveFrame store sourceStore after raw {source with vals := source.vals ++ results} := by
  refine ⟨effect.preserve_binding saved.binding,effect.resume saved.slots saved.destination,?_⟩
  obtain ⟨compiled,functions,targets,next,output,program,point⟩ := saved.continuation
  exact ⟨compiled,functions,targets,next,output,false,program,.ready (point.resume results types heights)⟩

theorem SavedFrames.host_preserved {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {base : Nat} {results : List val}
    {raws sources waiting boundary}
    (saved : SavedFrames store sourceStore before raws sources waiting boundary)
    (effect : HostReturnEffect before after base results) (below : boundary ≤ base) :
    SavedFrames store sourceStore after raws sources waiting boundary := by
  apply saved.transport
  · intro raw source binding member
    exact effect.preserve_binding binding
  · intro position bits represented bound
    exact effect.preserve_prefix represented (bound.trans below)

/-- A synchronous host call does not push a concrete Wasm frame. Its waiting
caller becomes active again after the checked result write, while every older
caller keeps its own saved continuation. -/
theorem host_return_stack {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {base : Nat} {results : List val}
    {raw : runtime.interp.Frame} {raws : List runtime.interp.Frame}
    {caller : Abs.AFrame} {rest : List Abs.AFrame} {waiting : List valtype}
    (frames : before.frames.val = raws.reverse ++ [raw])
    (saved : SavedFrame store sourceStore before raw caller waiting base)
    (older : SavedFrames store sourceStore before raws rest caller.resultTypes raw.base.val)
    (effect : HostReturnEffect before after base results)
    (types : results.map Code.valueType = waiting) (heights : Abs.FrameHeights caller) :
    FrameStackRel store sourceStore after ({caller with vals := caller.vals ++ results} :: rest) ∧
      ReadyTop store sourceStore after {caller with vals := caller.vals ++ results} := by
  refine ⟨.active (by simpa only [effect.frames] using frames)
    (saved.resume_host effect types heights) (older.host_preserved effect saved.base_le),?_⟩
  obtain ⟨compiled,functions,targets,next,output,program,point⟩ := saved.continuation
  refine ⟨raw,compiled,functions,targets,next,output,?_,program,point.resume results types heights⟩
  simp only [effect.frames,frames,List.getLast?_concat]

end Exec.Interp.StructuredMachine

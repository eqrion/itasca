import Exec.Interp.StructuredMachine.HostReturnFrames
namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std

/-- Consume exactly the suspended stack produced by prepare_call. A host
callee contributes no concrete frame, so the saved head resumes directly. -/
theorem SavedFrames.resume_host {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {base : Nat} {results : List val}
    {raws : List runtime.interp.Frame} {caller : Abs.AFrame} {rest : List Abs.AFrame}
    {waiting : List valtype}
    (saved : SavedFrames store sourceStore before raws (caller :: rest) waiting base)
    (frames : before.frames.val = raws.reverse)
    (effect : HostReturnEffect before after base results)
    (types : results.map Code.valueType = waiting) (heights : Abs.FrameHeights caller) :
    FrameStackRel store sourceStore after ({caller with vals := caller.vals ++ results} :: rest) ∧
      ReadyTop store sourceStore after {caller with vals := caller.vals ++ results} := by
  cases saved with
  | cons head tail =>
    exact host_return_stack (by simpa only [List.reverse_cons] using frames) head tail effect types heights

theorem SavedFrames.resume_host_extended {M : Type} {beforeStore afterStore : runtime.store.Store M}
    {oldSource newSource : _root_.store}
    (retained : FrameStorePrefix beforeStore afterStore) (bounds : FrameTypeBounds beforeStore)
    (extension : Extend_store oldSource newSource)
    {before after : runtime.interp.Execution} {base : Nat} {results : List val}
    {raws : List runtime.interp.Frame} {caller : Abs.AFrame} {rest : List Abs.AFrame}
    {waiting : List valtype}
    (saved : SavedFrames beforeStore oldSource before raws (caller :: rest) waiting base)
    (frames : before.frames.val = raws.reverse)
    (effect : HostReturnEffect before after base results)
    (types : results.map Code.valueType = waiting) (heights : Abs.FrameHeights caller) :
    FrameStackRel afterStore newSource after ({caller with vals := caller.vals ++ results} :: rest) ∧
      ReadyTop afterStore newSource after {caller with vals := caller.vals ++ results} :=
  (saved.store_prefix_extension retained bounds extension).resume_host frames effect types heights
end Itasca.Runtime.Interp.StructuredMachine

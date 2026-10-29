import Itasca.Runtime.Interp.Machine.Calls.HostReturnFrames
import Itasca.Runtime.Interp.Machine.Calls.PrepareCallStack

/-!
Resuming saved frames after a host call. Saved-frame transport and extended code/store facts reconstruct the suspended frame-stack relation.
-/

/-! ## Host Saved Frames Resume -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- Consume exactly the suspended stack produced by prepare_call. A host
callee contributes no concrete frame, so the saved head resumes directly. -/
theorem SavedFrames.resume_host {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {before after : runtime.interp.Execution} {base : Nat} {results : List val}
    {raws : List runtime.interp.Frame} {caller : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    {waiting : List valtype}
    (saved : SavedFrames store sourceStore before raws (caller :: rest) waiting base)
    (frames : before.frames.val = raws.reverse)
    (effect : HostReturnEffect before after base results)
    (types : results.map Compiler.valueType = waiting) (heights : SourceMachine.FrameHeights caller) :
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
    {raws : List runtime.interp.Frame} {caller : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    {waiting : List valtype}
    (saved : SavedFrames beforeStore oldSource before raws (caller :: rest) waiting base)
    (frames : before.frames.val = raws.reverse)
    (effect : HostReturnEffect before after base results)
    (types : results.map Compiler.valueType = waiting) (heights : SourceMachine.FrameHeights caller) :
    FrameStackRel afterStore newSource after ({caller with vals := caller.vals ++ results} :: rest) ∧
      ReadyTop afterStore newSource after {caller with vals := caller.vals ++ results} :=
  (saved.store_prefix_extension retained bounds extension).resume_host frames effect types heights
end Itasca.Runtime.Interp.Machine

end

/-! ## Host Call Stack -/

section

namespace Itasca.Runtime.Interp.Machine
open Aeneas Aeneas.Std

/-- Actual caller PC advancement and checked host result writes compose into
the full resumed concrete stack under retained raw metadata and source extension. -/
theorem FrameStackRel.host_call_return {M : Type} {store : runtime.store.Store M} {s : _root_.store}
    {exec : runtime.interp.Execution} {source : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    (relation : FrameStackRel store s exec (source :: rest))
    (raw : runtime.interp.Frame) (index : Usize) (pc : U32)
    (last : index.val + 1 = exec.frames.length)
    (lookup : exec.frames.val[index.val]? = some raw)
    (binding : FrameBinding store exec raw source)
    (slots : FrameSlots exec raw source)
    {compiled C targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Compiler.valueType) source.resultTypes C.FUNCS)
    (point : FramePoint s raw source compiled C targets next output)
    (front args : List val) (after : List instr) (returns : List valtype) (base : Nat)
    (split : source.vals = front ++ args)
    (destination : base = raw.base.val + Compiler.slots ((source.locals ++ front).map Compiler.valueType))
    (heights : ∀ label ∈ source.labels, label.height ≤ front.length)
    (continuation : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS source.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
      (front.map Compiler.valueType ++ returns) after pc.val next output)
    (afterStore : runtime.store.Store M) (sourceAfter : _root_.store)
    (retained : FrameStorePrefix store afterStore) (bounds : FrameTypeBounds store)
    (extension : Extend_store s sourceAfter)
    (finished : runtime.interp.Execution) (values : List val)
    (effect : HostReturnEffect {exec with frames := exec.frames.set index {raw with pc := pc}} finished base values)
    (typed : values.map Compiler.valueType = returns) :
    FrameStackRel afterStore sourceAfter finished
      ({source with code := after,vals := front ++ values} :: rest) ∧
      ReadyTop afterStore sourceAfter finished {source with code := after,vals := front ++ values} := by
  obtain ⟨raws,frames,saved⟩ := relation.prepare_call raw index pc last lookup binding slots program point
    front args after returns base split destination heights continuation
  exact saved.resume_host_extended retained bounds extension frames effect typed heights

end Itasca.Runtime.Interp.Machine

end

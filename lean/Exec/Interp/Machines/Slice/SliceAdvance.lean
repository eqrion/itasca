import Exec.Interp.Machines.Slice.SliceExecution
import Exec.Interp.Control.NormalizeCompose

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- One concrete dispatch advances a complete source/concrete invariant and
has either positive counted source reductions or a strict administrative decrease. -/
def SliceAdvance {M : Type} (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (expected : List valtype) (codeLength pc : Nat) (pending : Bool) (before : Abs.AState) : Prop :=
  ∃ after nextPC nextPending, SliceExecution store exec after expected nextPC nextPending ∧
    after.store = before.store ∧ after.ambient = before.ambient ∧
    ConcreteSim codeLength pc nextPC pending nextPending before after ∧
    (∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound after) ∧
    (∀ bound, Abs.StateReferencesBound bound before → Abs.StateReferencesBound bound after)

theorem SliceAdvance.ordinary {M : Type} {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {raw : runtime.interp.Frame} {pc : U32} {pending beforePending : Bool}
    {compiled : runtime.bytecode.CompiledFunction} {functions : List functype}
    {s : _root_.store} {ambient : frame} {before after : Abs.AFrame} {rest : List Abs.AFrame}
    (program : FrameProgram store raw compiled (before.locals.map Code.valueType) before.resultTypes functions)
    (result : Abs.InvocationResult expected ⟨s, ambient, before :: rest, []⟩)
    (top : exec.frames.val.getLast? = some { raw with pc := pc })
    (point : ∃ targets next output, ControlPoint { raw with pc := pc } after compiled functions targets next output pending)
    (stack : FrameStackRel store exec (after :: rest))
    (typed : Abs.ATyped ⟨s, ambient, after :: rest, []⟩)
    (slice : Abs.SliceState ⟨s, ambient, after :: rest, []⟩)
    (metadata : FrameMetadata before after)
    (simulation : ConcreteSim compiled.code.length raw.pc.val pc.val beforePending pending
      ⟨s, ambient, before :: rest, []⟩ ⟨s, ambient, after :: rest, []⟩)
    (bounded : ∀ bound, Abs.CodeBound bound ⟨s, ambient, before :: rest, []⟩ →
      Abs.CodeBound bound ⟨s, ambient, after :: rest, []⟩)
    (references : ∀ bound, Abs.StateReferencesBound bound ⟨s, ambient, before :: rest, []⟩ →
      Abs.StateReferencesBound bound ⟨s, ambient, after :: rest, []⟩) :
    SliceAdvance store exec expected compiled.code.length raw.pc.val beforePending
      ⟨s, ambient, before :: rest, []⟩ := by
  exact ⟨⟨s, ambient, after :: rest, []⟩, pc.val, pending,
    ⟨typed, slice, metadata.result s ambient rest expected result, stack,
      ControlTop.updated top program metadata point⟩, rfl, rfl, simulation, bounded, references⟩

theorem SliceAdvance.ready {M : Type} {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {expected : List valtype} {codeLength pc : Nat} {pending : Bool} {before after : Abs.AState}
    (typed : Abs.ATyped after) (slice : Abs.SliceState after)
    (result : Abs.InvocationResult expected after) (stack : FrameStackRel store exec after.frames)
    (ready : ReadyState store exec after)
    (sameStore : after.store = before.store) (sameAmbient : after.ambient = before.ambient)
    (simulation : Abs.NextSim before after)
    (bounded : ∀ bound, Abs.CodeBound bound before → Abs.CodeBound bound after)
    (references : ∀ bound, Abs.StateReferencesBound bound before → Abs.StateReferencesBound bound after) :
    SliceAdvance store exec expected codeLength pc pending before := by
  obtain ⟨nextPC, cursor⟩ := ready.cursor
  exact ⟨after, nextPC, false, ⟨typed, slice, result, stack, cursor⟩, sameStore, sameAmbient,
    ConcreteSim.of_source codeLength pc nextPC pending false simulation, bounded, references⟩

theorem SliceAdvance.prepend_normalization {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {expected : List valtype} {codeLength pc : Nat}
    {count : Nat} {before middle : Abs.AFrame} {s : _root_.store} {ambient : frame} {rest : List Abs.AFrame}
    (chain : ErasedSteps count before middle)
    (typed : Abs.ATyped ⟨s, ambient, before :: rest, []⟩)
    (advance : SliceAdvance store exec expected codeLength pc false ⟨s, ambient, middle :: rest, []⟩) :
    SliceAdvance store exec expected codeLength pc false ⟨s, ambient, before :: rest, []⟩ := by
  obtain ⟨after, nextPC, nextPending, invariant, sameStore, sameAmbient, simulation, bounded, references⟩ := advance
  exact ⟨after, nextPC, nextPending, invariant, sameStore, sameAmbient, simulation.prepend_normalization chain s ambient rest typed,
    (fun bound initial => bounded bound (chain.closure.codeBound initial)),
    fun bound initial => references bound (chain.closure.referenceBound initial)⟩

end Exec.Interp

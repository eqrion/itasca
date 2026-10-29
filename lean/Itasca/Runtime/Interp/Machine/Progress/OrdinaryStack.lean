import Itasca.Runtime.Interp.Machine.Frames.StackPreservation
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.Interp.Control.SkipStack
import Itasca.Runtime.Interp.Relations.PrefixDispatch

/-!
Ordinary bytecode changes only the active source's live values and code. Its observed prefix law preserves all suspended frames at once.

Main declarations: `FrameStackRel.ordinary`. A direct consumer is `Interp.Machine.Emission.Unreachable`.
-/

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std

/-- Ordinary bytecode changes only the active source's live values and code.
Its observed prefix law preserves all suspended frames at once. -/
theorem FrameStackRel.ordinary {M : Type} {store nextStore : runtime.store.Store M}
    {sourceStore nextSourceStore : _root_.store}
    {exec after : runtime.interp.Execution} {source updatedSource : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : FrameStackRel store sourceStore exec (source :: rest))
    (stores : FrameStoreMetadata store nextStore) (extension : Extend_store sourceStore nextSourceStore)
    (raw : runtime.interp.Frame) (index : Usize) (pc : U32)
    (last : index.val + 1 = exec.frames.length)
    (lookup : exec.frames.val[index.val]? = some raw)
    (binding : FrameBinding store exec raw source)
    {compiled C targets next output pending}
    (program : FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes C.FUNCS)
    (point : ControlPoint nextSourceStore { raw with pc := pc } updatedSource compiled C targets next output pending)
    (slots : FrameSlots after { raw with pc := pc } updatedSource)
    (metadata : FrameMetadata source updatedSource)
    (effect : { after with slots := exec.slots } =
      { exec with frames := exec.frames.set index { raw with pc := pc } })
    (preserved : SlotPrefix raw.base.val exec.slots.val after.slots.val) :
    FrameStackRel nextStore nextSourceStore after (updatedSource :: rest) := by
  have frames : after.frames = exec.frames.set index { raw with pc := pc } :=
    congrArg runtime.interp.Execution.frames effect
  have identity : after.store = exec.store := by
    have h := congrArg runtime.interp.Execution.store effect
    exact h
  have capacity : exec.slots.length ≤ after.slots.length := by
    change exec.slots.val.length ≤ after.slots.val.length
    rw [preserved.length]
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length - 1 = index.val := by change exec.frames.length - 1 = index.val; omega
    rw [position]
    exact lookup
  have framesVal : after.frames.val = exec.frames.val.dropLast ++ [{ raw with pc := pc }] := by
    rw [frames]
    exact frames_set_last exec index _ last
  refine relation.step_active stores extension raw { raw with pc := pc } top framesVal rfl metadata.results identity capacity
    (fun position bits represented below => preserved.region position bits represented below) ?_
  refine ⟨?_, slots, compiled, C, targets, next, output, pending, ?_, point⟩
  · obtain ⟨inst, fn, code, signature, oldIdentity, oldMember, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩ := binding.store_metadata stores
    refine ⟨inst, fn, code, signature, identity.trans oldIdentity, ?_, hi, ?_, hw, hc, hs, ?_, ?_, ?_, bound.trans capacity⟩
    · rw [framesVal]
      simp
    · simpa only [metadata.address] using hf
    · exact metadata.module.trans hm
    · exact metadata.results.trans hr
    · exact metadata.locals.trans hl
  · exact ⟨(program.store_metadata stores).lookup, program.checked, program.fetchBound,
      program.localSlots.trans (congrArg Code.slots metadata.locals).symm,
      by simpa only [metadata.results] using program.epilogue⟩

end Itasca.Runtime.Interp.StructuredMachine

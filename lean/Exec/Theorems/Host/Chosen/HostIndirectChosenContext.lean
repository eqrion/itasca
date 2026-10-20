import Exec.Theorems.Host.HostCallContext
import Exec.Abs.Indirect.ChosenHostSimulation
import Exec.Theorems.Host.Chosen.HostCallChosenRetained
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- The checked atomic host event composes with source call resolution and
all surrounding contexts. This retains a positive source step count. -/
theorem ChosenHostCallSourceOutcome.indirect_frame_events {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat) {M P : Type}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before : runtime.store.Store M) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (table type position : Nat)
    (address : runtime.FuncAddr) (front args : List val) (base : Usize)
    (exec : runtime.interp.Execution)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P)
    (observed : ChosenHostCallSourceOutcome choices (occurrence+1) view code before f.toFrame address args base exec out)
    (storeWf : wf_store (Store.decodeStore view code before))
    (freshWf : wf_store (Store.decodeStore view code out.2.2.1))
    (ambientWf : wf_frame ambient) (frameWf : wf_frame f.toFrame)
    (labels : Abs.LabelsWf f.labels) (values : Forall wf_val front)
    (tail : Forall wf_instr after) (callers : Forall Abs.FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (resolve : Spec.IndirectTarget (Store.decodeStore view code before) f.toFrame table type position address.index.val)
    (tableBound : table < 2^32) (typeBound : type < 2^32) (positionBound : position < 2^32)
    (argsWf : Forall wf_val args) :
    ∃ n, 2 ≤ n ∧ Spec.ChosenStepsN choices occurrence n
      (Abs.decode ⟨Store.decodeStore view code before,ambient,
        {f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type) :: after,vals := front ++ args ++ [Abs.integerVal .I32 position]} :: rest,[]⟩)
      (hostCallEvents address out) (hostCallFrameResult view code ambient f rest after front out) := by
  obtain ⟨arguments,_,_,_,outcome⟩ := observed
  rcases outcome with ⟨success,_,source,_⟩ | ⟨failure,source,_⟩
  · refine ⟨2,by omega,?_⟩
    simpa only [hostCallEvents,hostCallFrameResult,success,arguments] using
      Abs.Indirect.host_return_chosen_simulation admissible vector occurrence _ _ ambient f rest after table type position address.index.val front args
        (out.2.1.host_results.val.map sourceValue) _ storeWf ambientWf frameWf labels values tail callers
        heights resolve tableBound typeBound positionBound argsWf source
  · obtain ⟨n,bound,trace⟩ := Abs.Indirect.host_trap_chosen_simulation admissible vector occurrence _ _ ambient f rest after table type position address.index.val
      front args _ storeWf freshWf ambientWf frameWf labels values tail callers heights resolve tableBound typeBound positionBound argsWf source
    refine ⟨n,bound,?_⟩
    rcases failure with trapped | exhausted
    · simpa only [hostCallEvents,hostCallFrameResult,trapped,arguments] using trace
    · simpa only [hostCallEvents,hostCallFrameResult,exhausted,arguments] using trace
end Exec.Theorems

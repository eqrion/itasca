import Exec.Theorems.Host.HostCallRecording
import Exec.Abs.Sim.Host
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Source endpoint after a host call in an active Wasm frame. Traps unwind
all callers; successful calls resume the source continuation with actual results. -/
def hostCallFrameResult {M P : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front : List val)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : config :=
  match out.1 with
  | .Ok _ => Abs.decode ⟨Store.decodeStore view code out.2.2.1,ambient,
      {f with code := after,vals := front ++ out.2.1.host_results.val.map sourceValue} :: rest,[]⟩
  | _ => ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,[.TRAP]⟩

/-- The checked atomic host event composes with source call resolution and
all surrounding contexts. This retains a positive source step count. -/
theorem HostCallSourceOutcome.frame_events {M P : Type}
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before : runtime.store.Store M) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (index : Nat)
    (address : runtime.FuncAddr) (front args : List val) (base : Usize)
    (exec : runtime.interp.Execution)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P)
    (observed : HostCallSourceOutcome view code before f.toFrame address args base exec out)
    (storeWf : wf_store (Store.decodeStore view code before))
    (freshWf : wf_store (Store.decodeStore view code out.2.2.1))
    (ambientWf : wf_frame ambient) (frameWf : wf_frame f.toFrame)
    (labels : Abs.LabelsWf f.labels) (values : Forall wf_val front)
    (tail : Forall wf_instr after) (callers : Forall Abs.FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (resolve : f.module.FUNCS[index]? = some address.index.val) (indexBound : index < 2^32)
    (argsWf : Forall wf_val args) :
    ∃ n, 2 ≤ n ∧ Spec.StepsHN n
      (Abs.decode ⟨Store.decodeStore view code before,ambient,
        {f with code := .CALL (.mk_uN index) :: after,vals := front ++ args} :: rest,[]⟩)
      (hostCallEvents address out) (hostCallFrameResult view code ambient f rest after front out) := by
  obtain ⟨arguments,_,_,_,outcome⟩ := observed
  rcases outcome with ⟨success,_,source,_⟩ | ⟨failure,source,_⟩
  · refine ⟨2,by omega,?_⟩
    simpa only [hostCallEvents,hostCallFrameResult,success,arguments] using
      Abs.host_return_simulation _ _ ambient f rest after index address.index.val front args
        (out.2.1.host_results.val.map sourceValue) _ storeWf ambientWf frameWf labels values tail callers
        heights resolve indexBound argsWf source
  · obtain ⟨n,bound,trace⟩ := Abs.host_trap_simulation _ _ ambient f rest after index address.index.val
      front args _ storeWf freshWf ambientWf frameWf labels values tail callers heights resolve indexBound argsWf source
    refine ⟨n,bound,?_⟩
    rcases failure with trapped | exhausted
    · simpa only [hostCallEvents,hostCallFrameResult,trapped,arguments] using trace
    · simpa only [hostCallEvents,hostCallFrameResult,exhausted,arguments] using trace
end Exec.Theorems

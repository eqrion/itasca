import Exec.Theorems.Host.Open.Source.State.Observations
import Exec.Spec.Open.ExecutionCounted
import Exec.Interp.Relations.EventfulControl
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- The existing native administrative measure supplies the zero-step rank
case; a positive Wasm reduction retains its exact count in the combined model. -/
theorem concrete_source_trace {H : Type} (model : Spec.OpenExecution.HostModel H)
    {beforePC afterPC : Nat} {beforePending afterPending : Bool} {before after : Abs.AState}
    (simulation : ConcreteSim U32.max beforePC afterPC beforePending afterPending before after)
    (expected : resulttype) (stack : List (Spec.OpenExecution.Continuation H))
    (typed : Config_ok (Abs.decode before) expected) :
    Config_ok (Abs.decode after) expected ∧ ∃count events,
      Spec.OpenExecution.Trace model count
        ⟨(Abs.decode before).1.1,.wasm (Abs.decode before).1.2 (Abs.decode before).2 expected,stack⟩ events
        ⟨(Abs.decode after).1.1,.wasm (Abs.decode after).1.2 (Abs.decode after).2 expected,stack⟩ ∧
      (count=0 → dispatchMeasure afterPending U32.max afterPC after<dispatchMeasure beforePending U32.max beforePC before) ∧ visibleSourceHistory events=[] := by
  rcases simulation with ⟨same,decrease⟩|⟨count,positive,steps⟩
  · refine ⟨by simpa only [same] using typed,0,[],?_,(fun _=>decrease),rfl⟩
    rw [same]
    exact .nil _
  · exact ⟨Spec.stepsH_config_preserved steps.erase typed,count,List.replicate count .wasm,
      Spec.OpenExecution.Trace.wasmCounted model steps expected stack,(fun zero=>by omega),visibleSourceHistory_wasm count⟩
end Exec.Theorems.OpenReentrantControl

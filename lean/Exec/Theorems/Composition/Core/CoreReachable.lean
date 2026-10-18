import Exec.Theorems.Composition.Core.CoreErrors
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp SpecExt

/-- Reachability retaining the actual source store, including writes before a
resource rejection or interruption. -/
def StoreReachable (initial : config) (store : _root_.store) : Prop :=
  ∃ ambient body, StepsH initial [] ⟨⟨store,ambient⟩,body⟩

theorem StoreReachable.prepend {initial next : config} {store : _root_.store}
    (reachable : StoreReachable next store) (step : StepH initial [] next) : StoreReachable initial store := by
  obtain ⟨ambient,body,steps⟩ := reachable
  exact ⟨ambient,body,by simpa using StepsH.cons step steps⟩

theorem CoreLoopOutcome.reachable {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : CoreMachine M P view code expected} {result : ExecutionResult M P}
    (outcome : CoreLoopOutcome memory hooks floats allocator initial result) :
    StoreReachable (Abs.decode initial.source) (Store.decodeStore view code result.2.2.2.2.2.1) := by
  rcases outcome with success | failure
  · obtain ⟨final,dispatches,count,history,empty,sourceEmpty,typed,represented,reductions,extension,metadata,returned⟩ := success
    rw [←returned]
    exact ⟨initial.source.ambient,vals final.source.results,reductions.erase⟩
  · obtain ⟨previous,dispatches,count,actual,finalExec,finalStore,finalPlatform,history,reductions,step,cause,decoded,certified,extension,metadata,segments,returned⟩ := failure
    rw [←returned]
    refine ⟨previous.source.ambient,Abs.decodeFrames previous.source.frames (vals previous.source.results),?_⟩
    simpa only [finishExecution,decoded,Abs.decode] using reductions.erase
end Exec.Theorems

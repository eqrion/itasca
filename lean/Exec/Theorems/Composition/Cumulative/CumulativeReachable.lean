import Exec.Theorems.Composition.Core.CoreReachable
import Exec.Theorems.Composition.Cumulative.CumulativeErrors
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp SpecExt

theorem CumulativeLoopOutcome.reachable {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : CumulativeMachine M P view code expected} {result : ExecutionResult M P}
    (outcome : CumulativeLoopOutcome memory hooks floats allocator initial result) :
    StoreReachable (Abs.decode initial.source) (Store.decodeStore view code result.2.2.2.2.2.1) := by
  rcases outcome with success | failure
  · obtain ⟨final,dispatches,count,history,empty,sourceEmpty,typed,represented,reductions,extension,metadata,returned⟩ := success
    rw [←returned]
    exact ⟨initial.source.ambient,vals final.source.results,reductions.erase⟩
  · obtain ⟨previous,dispatches,count,actual,finalExec,finalStore,finalPlatform,history,reductions,step,cause,decoded,certified,extension,metadata,returned⟩ := failure
    rw [←returned]
    refine ⟨previous.source.ambient,Abs.decodeFrames previous.source.frames (vals previous.source.results),?_⟩
    simpa only [finishExecution,decoded,Abs.decode] using reductions.erase
end Exec.Theorems

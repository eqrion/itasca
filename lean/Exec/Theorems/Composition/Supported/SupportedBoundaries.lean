import Exec.Theorems.Composition.Supported.SupportedErrors
import Exec.Theorems.Composition.Supported.SupportedBoundaryCauses
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp SpecExt
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem SupportedLoopOutcome.limits {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : SupportedMachine emission allowed M P view code expected} {result : ExecutionResult M P}
    (outcome : SupportedLoopOutcome memory hooks floats allocator initial result) :
    result.2.2.2.2.2.1.limits = initial.store.limits := by
  rcases outcome with success | failure
  · obtain ⟨final,dispatches,count,history,empty,sourceEmpty,typed,represented,reductions,extension,metadata,segments,limits,rfl⟩ := success
    exact limits
  · obtain ⟨previous,dispatches,count,error,finalExec,finalStore,finalPlatform,history,reductions,step,cause,decoded,certified,extension,metadata,segments,limits,rfl⟩ := failure
    exact limits

/-- Frame exhaustion reaches the original invocation's configured limit in
source FRAME_ depth, even after content updates and indirect calls. -/
theorem SupportedLoopOutcome.frame_depth {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : SupportedMachine emission allowed M P view code expected} {result : ExecutionResult M P}
    (outcome : SupportedLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2 = .Err (.Exhausted .CallStack)) :
    ∃ final, StepsH (Abs.decode initial.source) [] final ∧
      initial.store.limits.max_frames.val ≤ Spec.frameDepth final := by
  obtain ⟨previous,dispatches,count,finalExec,finalStore,finalPlatform,history,reductions,step,cause,decoded,ambient,returned⟩ := outcome.error_reachable failed
  have depth := cause.frame_depth previous.invariant.stack
  have limits := SupportedMachine.history_limits memory hooks floats allocator history
  rw [limits] at depth
  exact ⟨Abs.decode previous.source,reductions.erase,depth⟩

/-- Termination names an actual hook refusal along the retained execution. -/
theorem SupportedLoopOutcome.interrupted {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : SupportedMachine emission allowed M P view code expected} {result : ExecutionResult M P}
    (outcome : SupportedLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2 = .Err .Terminated) :
    ∃ before after, hooks.interrupt before = .ok (.Terminate,after) := by
  obtain ⟨previous,dispatches,count,finalExec,finalStore,finalPlatform,history,reductions,step,cause,decoded,ambient,returned⟩ := outcome.error_reachable failed
  obtain ⟨after,decision⟩ := cause.interrupted
  exact ⟨previous.platform,after,decision⟩
end Exec.Theorems

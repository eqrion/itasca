import Exec.Interp.Relations.FrameDepth

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A defined call reports termination only for an actual interrupt decision. -/
theorem DirectCallCause.terminated {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {index : Usize}
    {raw : runtime.interp.Frame} {inst : runtime.store.ModuleInst}
    {compiled : runtime.bytecode.CompiledFunction}
    (cause : DirectCallCause allocator hooks exec store platform index raw inst compiled .Terminated) :
    ∃ after, hooks.interrupt platform = .ok (.Terminate, after) := by
  obtain ⟨target, offset, pc, address, base, function, instanceIndex, functionIndex,
    callee, code, fetch, resolved, lookup, wasm, instanceLookup, codeLookup, baseEq, pcEq, rejection⟩ := cause
  exact rejection

theorem SliceFailure.terminated {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : Abs.AState}
    (failure : SliceFailure allocator hooks exec store platform source .Terminated) :
    ∃ after, hooks.interrupt platform = .ok (.Terminate, after) := by
  rcases failure with ⟨⟨trap, kind, _⟩, _⟩ | ⟨_, interrupted⟩ | rejected
  · cases kind
  · exact interrupted
  · obtain ⟨index, raw, inst, compiled, _, _, _, _, cause⟩ := rejected
    exact cause.concrete.terminated

/-- Loop call-stack exhaustion occurs at a reachable source configuration
whose actual FRAME_ nesting has reached the configured limit. -/
theorem SliceLoopOutcome.frame_depth {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    {initial : SliceMachine P store sourceStore ambient expected bound}
    {result : ExecutionResult M P}
    (outcome : SliceLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2 = .Err (.Exhausted .CallStack)) :
    ∃ previous count, Spec.StepsHN count (Abs.decode initial.source) [] (Abs.decode previous) ∧
      previous.store = sourceStore ∧ previous.ambient = ambient ∧
      store.limits.max_frames.val ≤ Spec.frameDepth (Abs.decode previous) := by
  obtain ⟨previous, dispatches, count, finalExec, finalPlatform, run, steps, cost, actual, failure, returned⟩ :=
    outcome.error_reachable failed
  exact ⟨previous.source, count, steps, previous.decoded, previous.ambient_eq,
    failure.frame_depth previous.invariant.stack⟩

/-- Loop termination retains the actual callback decision at a reachable,
certified machine state. -/
theorem SliceLoopOutcome.terminated {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    {initial : SliceMachine P store sourceStore ambient expected bound}
    {result : ExecutionResult M P}
    (outcome : SliceLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2 = .Err .Terminated) :
    ∃ previous dispatches count after,
      Spec.Iterations (SliceTransition memory hooks floats allocator) dispatches initial [] previous ∧
      Spec.StepsHN count (Abs.decode initial.source) [] (Abs.decode previous.source) ∧
      hooks.interrupt previous.platform = .ok (.Terminate, after) := by
  obtain ⟨previous, dispatches, count, finalExec, finalPlatform, run, steps, cost, actual, failure, returned⟩ :=
    outcome.error_reachable failed
  obtain ⟨after, decision⟩ := failure.terminated
  exact ⟨previous, dispatches, count, after, run, steps, decision⟩

end Exec.Interp

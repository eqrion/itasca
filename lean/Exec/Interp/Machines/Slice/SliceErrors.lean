import Exec.Interp.Machines.Slice.SliceLoop

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Prefixing a checked source run preserves the precise instruction failure.
Concrete resource and interrupt witnesses remain attached to the failing state. -/
theorem SliceFailure.prepend {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {error : runtime.ExecError}
    {before after : Abs.AState} {count : Nat}
    (steps : Spec.StepsHN count (Abs.decode before) [] (Abs.decode after))
    (sameStore : after.store = before.store) (sameAmbient : after.ambient = before.ambient)
    (failure : SliceFailure allocator hooks exec store platform after error) :
    SliceFailure allocator hooks exec store platform before error := by
  rcases failure with ⟨kind, n, positive, reductions⟩ | interrupted | rejected
  · exact Or.inl ⟨kind, count + n, by omega,
      by simpa only [List.nil_append, sameStore, sameAmbient] using steps.trans reductions⟩
  · exact Or.inr (Or.inl interrupted)
  · obtain ⟨index, raw, inst, compiled, last, frameFound, instanceFound, codeFound, cause⟩ := rejected
    exact Or.inr (Or.inr ⟨index, raw, inst, compiled, last, frameFound, instanceFound, codeFound,
      cause.prepend steps sameStore sameAmbient⟩)

/-- A defined call can reject only for interruption or one of its three
resource classes; the stronger `CallCause` retains the exact witnesses. -/
theorem CallCause.kind {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {base : Usize}
    {compiled : runtime.bytecode.CompiledFunction} {error : runtime.ExecError}
    (cause : CallCause allocator hooks exec store platform base compiled error) :
    error = .Terminated ∨ error = .Exhausted .CallStack ∨
      error = .Exhausted .Values ∨ error = .Exhausted .Allocation := by
  cases error <;> simp only [CallCause] at cause <;> simp_all
  rename_i resource
  cases resource <;> simp_all

theorem DirectCallCause.kind {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {index : Usize}
    {raw : runtime.interp.Frame} {inst : runtime.store.ModuleInst}
    {compiled : runtime.bytecode.CompiledFunction} {error : runtime.ExecError}
    (cause : DirectCallCause allocator hooks exec store platform index raw inst compiled error) :
    error = .Terminated ∨ error = .Exhausted .CallStack ∨
      error = .Exhausted .Values ∨ error = .Exhausted .Allocation := by
  obtain ⟨target, offset, pc, address, base, function, instanceIndex, functionIndex,
    callee, code, fetch, resolved, lookup, wasm, instanceLookup, codeLookup, baseEq, pcEq, rejection⟩ := cause
  exact rejection.kind

/-- Every integer/control trap has a positive checked source execution to
`TRAP`; boundary and resource failures cannot masquerade as traps. -/
theorem SliceFailure.trap {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : Abs.AState} {trap : runtime.Trap}
    (failure : SliceFailure allocator hooks exec store platform source (.Trap trap)) :
    SliceTrap trap ∧ ∃ count, 0 < count ∧
      Spec.StepsHN count (Abs.decode source) [] ⟨⟨source.store, source.ambient⟩, [.TRAP]⟩ := by
  rcases failure with ⟨kind, reductions⟩ | ⟨kind, interrupted⟩ | rejected
  · obtain ⟨actual, same, allowed⟩ := kind
    cases same
    exact ⟨allowed, reductions⟩
  · cases kind
  · obtain ⟨index, raw, inst, compiled, _, _, _, _, cause⟩ := rejected
    simpa using cause.concrete.kind

/-- No other runtime error class is reachable in the verified slice. -/
theorem SliceFailure.kind {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : Abs.AState} {error : runtime.ExecError}
    (failure : SliceFailure allocator hooks exec store platform source error) :
    (∃ trap, error = .Trap trap ∧ SliceTrap trap) ∨ error = .Terminated ∨ error = .Exhausted .CallStack ∨
      error = .Exhausted .Values ∨ error = .Exhausted .Allocation := by
  rcases failure with ⟨kind, _⟩ | ⟨kind, _⟩ | rejected
  · exact Or.inl kind
  · exact Or.inr (Or.inl kind)
  · obtain ⟨index, raw, inst, compiled, _, _, _, _, cause⟩ := rejected
    exact Or.inr cause.concrete.kind

/-- Every error returned by the actual loop retains its exact failing dispatch
and a source justification composed from the initial source configuration. -/
theorem SliceLoopOutcome.error {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    {initial : SliceMachine P store sourceStore ambient expected bound}
    {result : ExecutionResult M P} {error : runtime.ExecError}
    (outcome : SliceLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2 = .Err error) :
    ∃ previous dispatches finalExec finalPlatform,
      Spec.Iterations (SliceTransition memory hooks floats allocator) dispatches initial [] previous ∧
      runtime.interp.step memory hooks floats allocator previous.exec store previous.platform =
        .ok (.Err error, finalExec, store, finalPlatform) ∧
      SliceFailure allocator hooks previous.exec store previous.platform initial.source error ∧
      finishExecution (finalExec, store, finalPlatform, .Err error) = result := by
  rcases outcome with success | rejected
  · obtain ⟨final, dispatches, count, _, _, _, _, _, _, _, returned⟩ := success
    rw [← returned] at failed
    cases failed
  · obtain ⟨previous, dispatches, actualError, finalExec, finalPlatform, run, step, failure, returned⟩ := rejected
    have same : actualError = error := by
      rw [← returned] at failed
      exact core.result.Result.Err.inj failed
    subst actualError
    obtain ⟨count, reductions, cost⟩ := SliceMachine.history_progress memory hooks floats allocator run
    exact ⟨previous, dispatches, finalExec, finalPlatform, run, step,
      failure.prepend reductions (previous.decoded.trans initial.decoded.symm)
        (previous.ambient_eq.trans initial.ambient_eq.symm), returned⟩

/-- Every rejected loop has a reachable source configuration at the failing
instruction, including resource and interrupt failures that do not trap. -/
theorem SliceLoopOutcome.error_reachable {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    {initial : SliceMachine P store sourceStore ambient expected bound}
    {result : ExecutionResult M P} {error : runtime.ExecError}
    (outcome : SliceLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2 = .Err error) :
    ∃ previous dispatches count finalExec finalPlatform,
      Spec.Iterations (SliceTransition memory hooks floats allocator) dispatches initial [] previous ∧
      Spec.StepsHN count (Abs.decode initial.source) [] (Abs.decode previous.source) ∧
      dispatches / (slicePotentialBound bound + 1) ≤ count ∧
      runtime.interp.step memory hooks floats allocator previous.exec store previous.platform =
        .ok (.Err error, finalExec, store, finalPlatform) ∧
      SliceFailure allocator hooks previous.exec store previous.platform previous.source error ∧
      finishExecution (finalExec, store, finalPlatform, .Err error) = result := by
  rcases outcome with success | rejected
  · obtain ⟨final, dispatches, count, _, _, _, _, _, _, _, returned⟩ := success
    rw [← returned] at failed
    cases failed
  · obtain ⟨previous, dispatches, actualError, finalExec, finalPlatform, run, step, failure, returned⟩ := rejected
    have same : actualError = error := by
      rw [← returned] at failed
      exact core.result.Result.Err.inj failed
    subst actualError
    obtain ⟨count, reductions, cost⟩ := SliceMachine.history_progress memory hooks floats allocator run
    exact ⟨previous, dispatches, count, finalExec, finalPlatform, run, reductions, cost,
      step, failure, returned⟩

/-- Trap soundness from the initial source configuration for the actual loop. -/
theorem SliceLoopOutcome.trap {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    {initial : SliceMachine P store sourceStore ambient expected bound}
    {result : ExecutionResult M P} {trap : runtime.Trap}
    (outcome : SliceLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2 = .Err (.Trap trap)) :
    SliceTrap trap ∧ ∃ count, 0 < count ∧
      Spec.StepsHN count (Abs.decode initial.source) [] ⟨⟨sourceStore, ambient⟩, [.TRAP]⟩ := by
  obtain ⟨previous, dispatches, finalExec, finalPlatform, _, _, cause, _⟩ := outcome.error failed
  simpa only [initial.decoded, initial.ambient_eq] using cause.trap

theorem SliceLoopOutcome.error_kind {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    {initial : SliceMachine P store sourceStore ambient expected bound}
    {result : ExecutionResult M P} {error : runtime.ExecError}
    (outcome : SliceLoopOutcome memory hooks floats allocator initial result)
    (failed : result.2.2.2.2.2.2.2 = .Err error) :
    (∃ trap, error = .Trap trap ∧ SliceTrap trap) ∨ error = .Terminated ∨ error = .Exhausted .CallStack ∨
      error = .Exhausted .Values ∨ error = .Exhausted .Allocation := by
  obtain ⟨previous, dispatches, finalExec, finalPlatform, _, _, cause, _⟩ := outcome.error failed
  exact cause.kind

end Exec.Interp

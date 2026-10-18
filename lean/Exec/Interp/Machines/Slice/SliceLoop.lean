import Exec.Interp.Machines.Slice.SliceHistory

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- A running loop retains an exact successful history; a failed loop retains
that history and the one actual failing instruction with its cause. -/
def SliceLoopInvariant {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    (initial : SliceMachine P store sourceStore ambient expected bound) (state : ExecutionState M P) : Prop :=
  state.2.1 = store ∧ match state.2.2.2 with
  | .Ok _ => ∃ machine count,
      Spec.Iterations (SliceTransition memory hooks floats allocator) count initial [] machine ∧
      machine.exec = state.1 ∧ machine.platform = state.2.2.1
  | .Err error => ∃ machine count,
      Spec.Iterations (SliceTransition memory hooks floats allocator) count initial [] machine ∧
      runtime.interp.step memory hooks floats allocator machine.exec store machine.platform =
        .ok (.Err error, state.1, store, state.2.2.1) ∧
      SliceFailure allocator hooks machine.exec store machine.platform machine.source error

theorem slice_loop_invariant_step {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    (decoded : sourceStore = Store.decodeStore view code store) (compiled : CompiledFunctions code store)
    (initial : SliceMachine P store sourceStore ambient expected bound)
    (exec : runtime.interp.Execution) (currentStore : runtime.store.Store M) (platform : P)
    (invariant : SliceLoopInvariant memory hooks floats allocator initial (exec, currentStore, platform, .Ok ()))
    (active : 0 < exec.frames.length) :
    runtime.interp.step memory hooks floats allocator exec currentStore platform
      ⦃ (status, nextExec, nextStore, nextPlatform) =>
        SliceLoopInvariant memory hooks floats allocator initial (nextExec, nextStore, nextPlatform, status) ⦄ := by
  obtain ⟨sameStore, machine, count, run, sameExec, samePlatform⟩ := invariant
  change currentStore = store at sameStore
  subst currentStore
  dsimp only at sameExec samePlatform
  subst exec
  subst platform
  obtain ⟨⟨status, nextExec, nextStore, nextPlatform⟩, returned, unchanged, outcome⟩ :=
    WP.spec_imp_exists (step_slice memory hooks floats allocator allocation interrupts view code machine.exec store machine.platform
      machine.source expected machine.pc machine.pending (machine.decoded.trans decoded) compiled machine.invariant active)
  change nextStore = store at unchanged
  subst nextStore
  rw [returned]
  apply WP.spec.ret
  refine ⟨rfl, ?_⟩
  cases status with
  | Ok u =>
    cases u
    obtain ⟨source, pc, pending, nextInvariant, sourceStoreEq, ambientEq, simulation, bounded, references⟩ := outcome
    let next : SliceMachine P store sourceStore ambient expected bound :=
      ⟨nextExec, nextPlatform, source, pc, pending, nextInvariant, bounded bound machine.bounded,
        sourceStoreEq.trans machine.decoded, ambientEq.trans machine.ambient_eq⟩
    exact ⟨next, count + 1, history_snoc run ⟨rfl, returned, simulation, references⟩, rfl, rfl⟩
  | Err error => exact ⟨machine, count, run, returned, outcome⟩

/-- Safety of the actual extracted execution loop, with no externally supplied
instruction or loop refinement contract. Divergence remains possible. -/
theorem slice_loop_stops {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    (decoded : sourceStore = Store.decodeStore view code store) (compiled : CompiledFunctions code store)
    (initial : SliceMachine P store sourceStore ambient expected bound) :
    runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.exec store initial.platform (.Ok ())
      ⦃ result => ∃ state, SliceLoopInvariant memory hooks floats allocator initial state ∧
        ¬ActiveExecution state ∧ finishExecution state = result ⦄div := by
  apply execution_loop_stops memory hooks floats allocator
    (SliceLoopInvariant memory hooks floats allocator initial)
    (slice_loop_invariant_step memory hooks floats allocator allocation interrupts view code decoded compiled initial)
    initial.exec store initial.platform (.Ok ())
  exact ⟨rfl, initial, 0, Spec.Iterations.refl initial, rfl, rfl⟩

/-- A normal loop result retains its exact concrete history and either typed
represented results with a counted source execution, or one justified failure. -/
def SliceLoopOutcome {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    (initial : SliceMachine P store sourceStore ambient expected bound) (result : ExecutionResult M P) : Prop :=
  (∃ final dispatches count,
    Spec.Iterations (SliceTransition memory hooks floats allocator) dispatches initial [] final ∧
    final.exec.frames.val = [] ∧ final.source.frames = [] ∧
    SpecExt.ResultsTyped sourceStore expected final.source.results ∧
    ValuesAt final.exec.slots.val 0 final.source.results ∧
    Spec.StepsHN count (Abs.decode initial.source) [] ⟨⟨sourceStore, ambient⟩, SpecExt.vals final.source.results⟩ ∧
    dispatches / (slicePotentialBound bound + 1) ≤ count ∧
    finishExecution (final.exec, store, final.platform, .Ok ()) = result) ∨
  (∃ previous dispatches error finalExec finalPlatform,
    Spec.Iterations (SliceTransition memory hooks floats allocator) dispatches initial [] previous ∧
    runtime.interp.step memory hooks floats allocator previous.exec store previous.platform =
      .ok (.Err error, finalExec, store, finalPlatform) ∧
    SliceFailure allocator hooks previous.exec store previous.platform previous.source error ∧
    finishExecution (finalExec, store, finalPlatform, .Err error) = result)

theorem slice_loop_finished {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    (initial : SliceMachine P store sourceStore ambient expected bound) (state : ExecutionState M P)
    (invariant : SliceLoopInvariant memory hooks floats allocator initial state)
    (stopped : ¬ActiveExecution state) :
    SliceLoopOutcome memory hooks floats allocator initial (finishExecution state) := by
  rcases state with ⟨exec, currentStore, platform, status⟩
  obtain ⟨sameStore, invariant⟩ := invariant
  change currentStore = store at sameStore
  subst currentStore
  cases status with
  | Ok u =>
    cases u
    obtain ⟨machine, dispatches, run, sameExec, samePlatform⟩ := invariant
    dsimp only at sameExec samePlatform
    subst exec
    subst platform
    have empty : machine.exec.frames.val = [] := by
      have length : machine.exec.frames.length = 0 := by
        simp only [ActiveExecution, true_and, and_true, not_lt] at stopped
        omega
      exact List.length_eq_zero_iff.mp length
    obtain ⟨sourceEmpty, typedResults, represented⟩ := machine.invariant.finished empty
    obtain ⟨count, reductions, cost⟩ := SliceMachine.history_progress memory hooks floats allocator run
    refine Or.inl ⟨machine, dispatches, count, run, empty, sourceEmpty, ?_, represented, ?_, cost, rfl⟩
    · simpa only [machine.decoded] using typedResults
    · simpa only [Abs.decode, sourceEmpty, Abs.decodeFrames_nil, machine.decoded, machine.ambient_eq] using reductions
  | Err error =>
    obtain ⟨machine, dispatches, run, failed, cause⟩ := invariant
    exact Or.inr ⟨machine, dispatches, error, exec, platform, run, failed, cause, rfl⟩

/-- The actual interpreter loop has a divergence-permitting specification
with complete slice error causes and quantitative finite-run simulation. -/
theorem slice_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    (decoded : sourceStore = Store.decodeStore view code store) (compiled : CompiledFunctions code store)
    (initial : SliceMachine P store sourceStore ambient expected bound) :
    runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.exec store initial.platform (.Ok ())
      ⦃ result => SliceLoopOutcome memory hooks floats allocator initial result ⦄div := by
  apply WP.dspec_mono (slice_loop_stops memory hooks floats allocator allocation interrupts view code decoded compiled initial)
  rintro result ⟨state, invariant, stopped, same⟩
  rw [← same]
  exact slice_loop_finished memory hooks floats allocator initial state invariant stopped

end Exec.Interp

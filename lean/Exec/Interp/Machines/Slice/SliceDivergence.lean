import Exec.Interp.Machines.Slice.SliceLoop
import Exec.Interp.Control.LoopPrefix

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem execution_loop_error {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (error : runtime.ExecError) :
    loop (executionBody memory hooks floats allocator) (exec, store, platform, .Err error) =
      .ok (finishExecution (exec, store, platform, .Err error)) := by
  rw [loop.eq_def]
  simp [executionBody, runtime.interp.invoke_with_loop1.body, core.result.Result.is_ok, finishExecution]

theorem execution_loop_divergent_active {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (divergent : loop (executionBody memory hooks floats allocator) (exec, store, platform, .Ok ()) = .div) :
    0 < exec.frames.length := by
  by_contra inactive
  have empty : ¬exec.frames.len > 0#usize := by scalar_tac
  rw [loop.eq_def] at divergent
  simp [executionBody, runtime.interp.invoke_with_loop1.body, empty] at divergent

theorem slice_divergent_next {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    (decoded : sourceStore = Store.decodeStore view code store) (compiled : CompiledFunctions code store)
    (machine : SliceMachine P store sourceStore ambient expected bound)
    (divergent : loop (executionBody memory hooks floats allocator) (machine.exec, store, machine.platform, .Ok ()) = .div) :
    ∃ next, SliceTransition memory hooks floats allocator machine [] next ∧
      loop (executionBody memory hooks floats allocator) (next.exec, store, next.platform, .Ok ()) = .div := by
  have active := execution_loop_divergent_active memory hooks floats allocator machine.exec store machine.platform divergent
  obtain ⟨⟨status, nextExec, nextStore, nextPlatform⟩, returned, unchanged, outcome⟩ :=
    WP.spec_imp_exists (step_slice memory hooks floats allocator allocation interrupts view code machine.exec store machine.platform
      machine.source expected machine.pc machine.pending (machine.decoded.trans decoded) compiled machine.invariant active)
  change nextStore = store at unchanged
  subst nextStore
  rw [loop.eq_def, executionBody_active memory hooks floats allocator _ ⟨active, rfl⟩, returned] at divergent
  simp [bind_ok] at divergent
  cases status with
  | Err error => rw [execution_loop_error memory hooks floats allocator] at divergent; simp at divergent
  | Ok u =>
    cases u
    obtain ⟨source, pc, pending, invariant, sameStore, sameAmbient, simulation, bounded, references⟩ := outcome
    let next : SliceMachine P store sourceStore ambient expected bound :=
      ⟨nextExec, nextPlatform, source, pc, pending, invariant, bounded bound machine.bounded,
        sameStore.trans machine.decoded, sameAmbient.trans machine.ambient_eq⟩
    exact ⟨next, ⟨rfl, returned, simulation, references⟩, divergent⟩

/-- Actual divergence supplies an exact successful dispatch prefix of every
finite length. Its remaining execution still diverges. -/
theorem slice_divergent_history {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    (decoded : sourceStore = Store.decodeStore view code store) (compiled : CompiledFunctions code store)
    (dispatches : Nat) (initial : SliceMachine P store sourceStore ambient expected bound)
    (divergent : runtime.interp.invoke_with_loop1 memory hooks floats allocator
      initial.exec store initial.platform (.Ok ()) = .div) :
    ∃ final, Spec.Iterations (SliceTransition memory hooks floats allocator) dispatches initial [] final ∧
      runtime.interp.invoke_with_loop1 memory hooks floats allocator final.exec store final.platform (.Ok ()) = .div := by
  induction dispatches generalizing initial with
  | zero => exact ⟨initial, .refl initial, divergent⟩
  | succ count ih =>
    obtain ⟨next, step, nextDivergent⟩ := slice_divergent_next memory hooks floats allocator allocation interrupts
      view code decoded compiled initial divergent
    obtain ⟨final, history, finalDivergent⟩ := ih next nextDivergent
    exact ⟨final, Spec.Iterations.cons step history, finalDivergent⟩

/-- A diverging slice invocation cannot perform only administrative stutters:
for every requested number of specification reductions there is a checked
actual execution prefix whose source simulation contains at least that many. -/
theorem slice_no_silent_divergence {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    (decoded : sourceStore = Store.decodeStore view code store) (compiled : CompiledFunctions code store)
    (initial : SliceMachine P store sourceStore ambient expected bound)
    (divergent : runtime.interp.invoke_with_loop1 memory hooks floats allocator
      initial.exec store initial.platform (.Ok ()) = .div) (requested : Nat) :
    ∃ final count,
      Spec.Iterations (SliceTransition memory hooks floats allocator)
        (requested * (slicePotentialBound bound + 1)) initial [] final ∧
      Spec.StepsHN count (Abs.decode initial.source) [] (Abs.decode final.source) ∧ requested ≤ count := by
  obtain ⟨final, history, _⟩ := slice_divergent_history memory hooks floats allocator allocation interrupts view code
    decoded compiled (requested * (slicePotentialBound bound + 1)) initial divergent
  obtain ⟨count, reductions, cost⟩ := SliceMachine.history_progress memory hooks floats allocator history
  exact ⟨final, count, history, reductions, by simpa using cost⟩

end Exec.Interp

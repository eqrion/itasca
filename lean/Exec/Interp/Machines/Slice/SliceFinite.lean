import Exec.Interp.Machines.Slice.SliceDivergence

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- An exact continuing prefix contains successful dispatches and at most one
final rejection. A rejected state cannot execute another loop iteration. -/
def SlicePrefix {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    (initial : SliceMachine P store sourceStore ambient expected bound)
    (dispatches : Nat) (last : ExecutionState M P) : Prop :=
  ∃ previous successes,
    Spec.Iterations (SliceTransition memory hooks floats allocator) successes initial [] previous ∧
    ((successes = dispatches ∧ last = (previous.exec, store, previous.platform, .Ok ())) ∨
      (successes + 1 = dispatches ∧ ∃ error finalExec finalPlatform,
        runtime.interp.step memory hooks floats allocator previous.exec store previous.platform =
          .ok (.Err error, finalExec, store, finalPlatform) ∧
        SliceFailure allocator hooks previous.exec store previous.platform previous.source error ∧
        last = (finalExec, store, finalPlatform, .Err error)))

theorem slice_continuing_history {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    (decoded : sourceStore = Store.decodeStore view code store) (compiled : CompiledFunctions code store)
    (dispatches : Nat) (initial : SliceMachine P store sourceStore ambient expected bound)
    (last : ExecutionState M P)
    (trace : ContinuingTrace (executionBody memory hooks floats allocator) dispatches
      (initial.exec, store, initial.platform, .Ok ()) last) :
    SlicePrefix memory hooks floats allocator initial dispatches last := by
  induction dispatches generalizing initial last with
  | zero =>
    cases trace
    exact ⟨initial, 0, .refl initial, Or.inl ⟨rfl, rfl⟩⟩
  | succ count ih =>
    cases trace with
    | @next _ _ next _ bodyStep tail =>
      have active : 0 < initial.exec.frames.length := by
        by_contra inactive
        have empty : ¬initial.exec.frames.len > 0#usize := by scalar_tac
        simp [executionBody, runtime.interp.invoke_with_loop2.body, empty] at bodyStep
      obtain ⟨⟨status, nextExec, nextStore, nextPlatform⟩, returned, unchanged, outcome⟩ :=
        WP.spec_imp_exists (step_slice memory hooks floats allocator allocation interrupts view code
          initial.exec store initial.platform initial.source expected initial.pc initial.pending
          (initial.decoded.trans decoded) compiled initial.invariant active)
      change nextStore = store at unchanged
      subst nextStore
      rw [executionBody_active memory hooks floats allocator _ ⟨active, rfl⟩, returned] at bodyStep
      have nextEq : (nextExec, store, nextPlatform, status) = next := by simpa [bind_ok] using bodyStep
      subst next
      cases status with
      | Err error =>
        cases tail with
        | nil => exact ⟨initial, 0, .refl initial, Or.inr ⟨rfl, error, nextExec, nextPlatform, returned, outcome, rfl⟩⟩
        | next stopped _ =>
          simp [executionBody, runtime.interp.invoke_with_loop2.body, core.result.Result.is_ok] at stopped
      | Ok u =>
        cases u
        obtain ⟨source, pc, pending, invariant, sameStore, sameAmbient, simulation, bounded, references⟩ := outcome
        let next : SliceMachine P store sourceStore ambient expected bound :=
          ⟨nextExec, nextPlatform, source, pc, pending, invariant, bounded bound initial.bounded,
            sameStore.trans initial.decoded, sameAmbient.trans initial.ambient_eq⟩
        obtain ⟨previous, successes, run, final⟩ := ih next last tail
        refine ⟨previous, successes + 1, ?_, ?_⟩
        · exact Spec.Iterations.cons ⟨rfl, returned, simulation, references⟩ run
        · rcases final with ⟨same, finished⟩ | ⟨same, error, finalExec, finalPlatform, failed, cause, finished⟩
          · exact Or.inl ⟨by omega, finished⟩
          · exact Or.inr ⟨by omega, error, finalExec, finalPlatform, failed, cause, finished⟩

/-- One extra unit in the potential bound pays for a final failing dispatch. -/
theorem finite_prefix_div_bound (bound successes dispatches : Nat) (counted : dispatches ≤ successes + 1) :
    dispatches / (bound + 2) ≤ successes / (bound + 1) := by
  have remainder := Nat.mod_lt successes (by omega : 0 < bound + 1)
  have division := Nat.mod_add_div successes (bound + 1)
  have positive : 0 < successes / (bound + 1) + 1 := Nat.succ_pos _
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < bound + 2)).2
  simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.mul_comm] at *
  omega

/-- Literal finite T7 statement for continuing iterations of the actual loop,
including a possible final failed dispatch. K is fixed by the source bound. -/
theorem slice_finite_progress {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    (decoded : sourceStore = Store.decodeStore view code store) (compiled : CompiledFunctions code store)
    (dispatches : Nat) (initial : SliceMachine P store sourceStore ambient expected bound)
    (last : ExecutionState M P)
    (trace : ContinuingTrace (executionBody memory hooks floats allocator) dispatches
      (initial.exec, store, initial.platform, .Ok ()) last) :
    ∃ previous count, Spec.StepsHN count (Abs.decode initial.source) [] (Abs.decode previous) ∧
      dispatches / (slicePotentialBound bound + 2) ≤ count := by
  obtain ⟨previous, successes, history, endpoint⟩ := slice_continuing_history memory hooks floats allocator
    allocation interrupts view code decoded compiled dispatches initial last trace
  obtain ⟨count, steps, cost⟩ := SliceMachine.history_progress memory hooks floats allocator history
  have counted : dispatches ≤ successes + 1 := by rcases endpoint with ⟨same, _⟩ | ⟨same, _⟩ <;> omega
  exact ⟨previous.source, count, steps, (finite_prefix_div_bound _ _ _ counted).trans cost⟩

end Exec.Interp

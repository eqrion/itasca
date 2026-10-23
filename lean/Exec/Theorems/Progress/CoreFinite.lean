import Exec.Theorems.Progress.CoreDivergence
import Exec.Interp.Machines.Slice.SliceFinite
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

def CorePrefix {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (initial : CoreMachine M P view code expected) (dispatches : Nat) (last : ExecutionState M P) : Prop :=
  ∃ previous successes,
    Spec.Iterations (CoreTransition memory hooks floats allocator) successes initial [] previous ∧
    ((successes = dispatches ∧ last = (previous.exec,previous.store,previous.platform,.Ok ())) ∨
     (successes+1 = dispatches ∧ ∃ error finalExec finalStore finalPlatform,
       runtime.interp.step memory hooks floats allocator previous.exec previous.store previous.platform =
         .ok (.Err error,finalExec,finalStore,finalPlatform) ∧
       CoreFailure allocator hooks previous.exec previous.store previous.platform previous.source error ∧
       last = (finalExec,finalStore,finalPlatform,.Err error)))

theorem core_continuing_history {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    {expected : List valtype} (dispatches : Nat) (initial : CoreMachine M P view code expected)
    (last : ExecutionState M P)
    (trace : ContinuingTrace (executionBody memory hooks floats allocator) dispatches
      (initial.exec,initial.store,initial.platform,.Ok ()) last) :
    CorePrefix memory hooks floats allocator initial dispatches last := by
  induction dispatches generalizing initial last with
  | zero =>
    cases trace
    exact ⟨initial,0,.refl initial,Or.inl ⟨rfl,rfl⟩⟩
  | succ count ih =>
    cases trace with
    | @next _ _ next _ bodyStep tail =>
      have active : 0 < initial.exec.frames.length := by
        by_contra inactive
        have empty : ¬initial.exec.frames.len > 0#usize := by scalar_tac
        simp [executionBody,runtime.interp.invoke_with_loop1.body,empty] at bodyStep
      obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,returned,fresh,extension,bounds,hostFree,mutation,outcome⟩ :=
        WP.spec_imp_exists (step_core_host_free memory hooks floats allocator allocation interrupts view laws code
          initial.exec initial.store initial.platform initial.source expected initial.pc initial.pending
          initial.certified initial.hostFree initial.owned initial.invariant active)
      rw [executionBody_active memory hooks floats allocator _ ⟨active,rfl⟩,returned] at bodyStep
      have nextEq : (nextExec,nextStore,nextPlatform,status) = next := by simpa [bind_ok] using bodyStep
      subst next
      cases status with
      | Err error =>
        cases tail with
        | nil => exact ⟨initial,0,.refl initial,Or.inr ⟨rfl,error,nextExec,nextStore,nextPlatform,returned,outcome.1,rfl⟩⟩
        | next stopped _ => simp [executionBody,runtime.interp.invoke_with_loop1.body,core.result.Result.is_ok] at stopped
      | Ok unit =>
        cases unit
        obtain ⟨pc,pending,source,invariant,simulation,ownership,ambient,bounded⟩ := outcome
        have owned : Abs.Ownership.CoreOwned (Store.ownershipBounds nextStore) source := by
          rw [bounds]
          exact ownership _ initial.owned
        let next : CoreMachine M P view code expected :=
          ⟨nextStore,nextExec,nextPlatform,source,pc,pending,invariant,fresh,owned,hostFree⟩
        obtain ⟨previous,successes,run,final⟩ := ih next last tail
        refine ⟨previous,successes+1,?_,?_⟩
        · exact Spec.Iterations.cons ⟨rfl,returned,simulation,extension,mutation.metadata,ambient,bounded,mutation.segments⟩ run
        · rcases final with ⟨same,finished⟩ | ⟨same,error,finalExec,finalStore,finalPlatform,failed,cause,finished⟩
          · exact Or.inl ⟨by omega,finished⟩
          · exact Or.inr ⟨by omega,error,finalExec,finalStore,finalPlatform,failed,cause,finished⟩

/-- Literal finite progress for actual continuing dispatches, including a
possible final rejection. The bound depends only on the initial source state. -/
theorem core_finite_progress {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    {expected : List valtype} (dispatches : Nat) (initial : CoreMachine M P view code expected)
    (last : ExecutionState M P)
    (trace : ContinuingTrace (executionBody memory hooks floats allocator) dispatches
      (initial.exec,initial.store,initial.platform,.Ok ()) last) :
    ∃ previous count, Spec.StepsHN count (Abs.decode initial.source) [] (Abs.decode previous) ∧
      dispatches / (corePotentialBound (sizeOf initial.source)+2) ≤ count := by
  obtain ⟨previous,successes,history,endpoint⟩ := core_continuing_history memory hooks floats allocator
    allocation interrupts view laws code dispatches initial last trace
  obtain ⟨count,steps,cost⟩ := CoreMachine.history_progress memory hooks floats allocator history (Abs.codeBound_initial initial.source)
  have counted : dispatches ≤ successes+1 := by rcases endpoint with ⟨same,_⟩ | ⟨same,_⟩ <;> omega
  exact ⟨previous.source,count,steps,(finite_prefix_div_bound _ _ _ counted).trans cost⟩
end Exec.Theorems

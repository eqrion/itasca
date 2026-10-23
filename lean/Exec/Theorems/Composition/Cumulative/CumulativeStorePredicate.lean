import Exec.Theorems.Composition.Cumulative.CumulativeLoop
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- Any concrete store predicate preserved by each issued mutation survives
an entire interpreter loop, including a final error. -/
theorem cumulative_loop_store_predicate {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    {expected : List valtype} (initial : CumulativeMachine M P view code expected)
    (predicate : runtime.store.Store M → Prop) (initialPredicate : predicate initial.store)
    (preserved : ∀ before after, CumulativeStoreMutation view code before after → predicate before → predicate after) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ out => predicate out.2.2.2.2.2.1 ⦄div := by
  let invariant (state : ExecutionState M P) :=
    CumulativeLoopInvariant memory hooks floats allocator initial state ∧ predicate state.2.1
  apply WP.dspec_mono (execution_loop_stops memory hooks floats allocator invariant ?_
    initial.exec initial.store initial.platform (.Ok ())
    ⟨⟨initial.certified,initial,0,.refl initial,rfl,rfl,rfl⟩,initialPredicate⟩)
  · rintro out ⟨state,retained,stopped,rfl⟩
    exact retained.2
  · intro exec store platform old active
    obtain ⟨certified,machine,count,run,sameExec,sameStore,samePlatform⟩ := old.1
    dsimp only at sameExec sameStore samePlatform
    subst exec
    subst store
    subst platform
    obtain ⟨out,returned,fresh,extension,bounds,hostFree,mutation,outcome⟩ := WP.spec_imp_exists
      (step_cumulative_host_free memory hooks floats allocator correct allocation interrupts view laws code
        machine.exec machine.store machine.platform machine.source expected machine.pc machine.pending
        machine.certified machine.hostFree machine.owned machine.invariant active)
    have retained := cumulative_loop_invariant_step memory hooks floats allocator correct allocation interrupts
      view laws code initial machine.exec machine.store machine.platform old.1 active
    rw [returned,WP.spec_ok] at retained ⊢
    exact ⟨retained,preserved _ _ mutation old.2⟩

end Exec.Theorems

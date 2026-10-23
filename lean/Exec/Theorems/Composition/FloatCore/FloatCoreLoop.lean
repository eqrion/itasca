import Exec.Theorems.Composition.FloatCore.FloatCoreHistory
import Exec.Theorems.Composition.FloatCore.FloatCoreStepCertified
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

def FloatCoreLoopInvariant {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (initial : FloatCoreMachine M P view code expected) (state : ExecutionState M P) : Prop :=
  CertifiedFloatCoreStore view code state.2.1 ∧ match state.2.2.2 with
  | .Ok _ => ∃ machine count,
      Spec.Iterations (FloatCoreTransition memory hooks floats allocator) count initial [] machine ∧
      machine.exec = state.1 ∧ machine.store = state.2.1 ∧ machine.platform = state.2.2.1
  | .Err error => ∃ machine count,
      Spec.Iterations (FloatCoreTransition memory hooks floats allocator) count initial [] machine ∧
      runtime.interp.step memory hooks floats allocator machine.exec machine.store machine.platform =
        .ok (.Err error,state.1,state.2.1,state.2.2.1) ∧
      FloatCoreFailure allocator hooks machine.exec machine.store machine.platform machine.source error ∧
      Store.decodeStore view code state.2.1 = machine.source.store ∧
      Extend_store (Store.decodeStore view code machine.store) (Store.decodeStore view code state.2.1) ∧ FrameStoreMetadata machine.store state.2.1 ∧
      state.2.1.elems = machine.store.elems ∧ state.2.1.datas = machine.store.datas

theorem float_core_loop_invariant_step {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    {expected : List valtype} (initial : FloatCoreMachine M P view code expected)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (invariant : FloatCoreLoopInvariant memory hooks floats allocator initial (exec,store,platform,.Ok ()))
    (active : 0 < exec.frames.length) :
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ (status,nextExec,nextStore,nextPlatform) =>
        FloatCoreLoopInvariant memory hooks floats allocator initial (nextExec,nextStore,nextPlatform,status) ⦄ := by
  obtain ⟨certified,machine,count,run,sameExec,sameStore,samePlatform⟩ := invariant
  dsimp only at sameExec sameStore samePlatform
  subst exec
  subst store
  subst platform
  obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,returned,fresh,extension,bounds,hostFree,mutation,outcome⟩ :=
    WP.spec_imp_exists (step_float_core_host_free memory hooks floats allocator correct allocation interrupts view laws code machine.exec machine.store machine.platform
      machine.source expected machine.pc machine.pending machine.certified machine.hostFree machine.owned machine.invariant active)
  rw [returned]
  apply WP.spec.ret
  refine ⟨fresh,?_⟩
  cases status with
  | Ok unit =>
    cases unit
    obtain ⟨pc,pending,source,retained,simulation,ownership,ambientEq,bounded⟩ := outcome
    have owned : Abs.Ownership.CoreOwned (Store.ownershipBounds nextStore) source := by
      rw [bounds]
      exact ownership _ machine.owned
    let next : FloatCoreMachine M P view code expected :=
      ⟨nextStore,nextExec,nextPlatform,source,pc,pending,retained,fresh,owned,hostFree⟩
    exact ⟨next,count+1,history_snoc run ⟨rfl,returned,simulation,extension,mutation.metadata,ambientEq,bounded,mutation.segments⟩,rfl,rfl,rfl⟩
  | Err error => exact ⟨machine,count,run,returned,outcome.1,outcome.2,extension,mutation.metadata,mutation.segments⟩

/-- Actual defined-only mutable execution is safe and may diverge. Every
normal exit retains its exact dispatch history and current store certificate. -/
theorem float_core_loop_stops {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    {expected : List valtype} (initial : FloatCoreMachine M P view code expected) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ result => ∃ state, FloatCoreLoopInvariant memory hooks floats allocator initial state ∧
        ¬ActiveExecution state ∧ finishExecution state = result ⦄div := by
  apply execution_loop_stops memory hooks floats allocator
    (FloatCoreLoopInvariant memory hooks floats allocator initial)
    (float_core_loop_invariant_step memory hooks floats allocator correct allocation interrupts view laws code initial)
    initial.exec initial.store initial.platform (.Ok ())
  exact ⟨initial.certified,initial,0,Spec.Iterations.refl initial,rfl,rfl,rfl⟩
end Exec.Theorems

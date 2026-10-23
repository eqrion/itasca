import Exec.Theorems.Composition.Uniform.UniformWorldHistory
import Exec.Interp.Machines.Slice.SliceFinite
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- The local contract for quantitative progress is normality and a checked
uniform source edge on each successful actual dispatch. -/
def UniformWorldStepTotal {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (expected : List valtype)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ machine : EventfulWorld M P view expected, Inv machine.code machine.machine.store → 0<machine.machine.exec.frames.length →
    runtime.interp.step memory hooks floats allocator machine.machine.exec machine.machine.store machine.machine.platform ⦃ out =>
      out.1=.Ok () → ∃events next, Inv next.code next.machine.store ∧ out=(.Ok (),next.machine.exec,next.machine.store,next.machine.platform) ∧
        UniformWorldTransition memory hooks floats allocator machine events next ⦄

/-- Exact actual continuing prefixes consist of successful uniform edges and
at most one final error. Errors never generate an additional loop iteration. -/
def UniformWorldPrefix {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (initial : EventfulWorld M P view expected) (dispatches : Nat) (last : ExecutionState M P) : Prop :=
  ∃previous successes events,
    Spec.Iterations (UniformWorldTransition memory hooks floats allocator) successes initial events previous ∧
    ((successes=dispatches ∧ last=(previous.machine.exec,previous.machine.store,previous.machine.platform,.Ok ())) ∨
     (successes+1=dispatches ∧ ∃error finalExec finalStore finalPlatform,
       runtime.interp.step memory hooks floats allocator previous.machine.exec previous.machine.store previous.machine.platform=
         .ok (.Err error,finalExec,finalStore,finalPlatform) ∧
       last=(finalExec,finalStore,finalPlatform,.Err error)))

theorem uniform_world_continuing_history {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : UniformWorldStepTotal memory hooks floats allocator view expected Inv)
    (dispatches : Nat) (initial : EventfulWorld M P view expected)
    (valid : Inv initial.code initial.machine.store) (last : ExecutionState M P)
    (trace : ContinuingTrace (executionBody memory hooks floats allocator) dispatches
      (initial.machine.exec,initial.machine.store,initial.machine.platform,.Ok ()) last) :
    UniformWorldPrefix memory hooks floats allocator initial dispatches last := by
  induction dispatches generalizing initial last with
  | zero =>
    cases trace
    exact ⟨initial,0,[],.refl initial,Or.inl ⟨rfl,rfl⟩⟩
  | succ count ih =>
    cases trace with
    | @next _ _ next _ bodyStep tail =>
      have active : 0 < initial.machine.exec.frames.length := by
        by_contra inactive
        have empty : ¬initial.machine.exec.frames.len > 0#usize := by scalar_tac
        simp [executionBody,runtime.interp.invoke_with_loop1.body,empty] at bodyStep
      obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,returned,outcome⟩ :=
        WP.spec_imp_exists (steps initial valid active)
      rw [executionBody_active memory hooks floats allocator _ ⟨active,rfl⟩,returned] at bodyStep
      have nextEq : (nextExec,nextStore,nextPlatform,status)=next := by simpa [bind_ok] using bodyStep
      subst next
      cases status with
      | Err error =>
        cases tail with
        | nil => exact ⟨initial,0,[],.refl initial,Or.inr ⟨rfl,error,nextExec,nextStore,nextPlatform,returned,rfl⟩⟩
        | next stopped _ => simp [executionBody,runtime.interp.invoke_with_loop1.body,core.result.Result.is_ok] at stopped
      | Ok value =>
        cases value
        obtain ⟨events,next,newValid,equal,edge⟩ := outcome rfl
        have components : nextExec=next.machine.exec ∧ nextStore=next.machine.store ∧ nextPlatform=next.machine.platform := by
          simpa only [Prod.mk.injEq,true_and] using equal
        obtain ⟨rfl,rfl,rfl⟩ := components
        obtain ⟨previous,successes,more,run,final⟩ := ih next newValid last tail
        refine ⟨previous,successes+1,events++more,Spec.Iterations.cons edge run,?_⟩
        rcases final with ⟨same,finished⟩ | ⟨same,error,finalExec,finalStore,finalPlatform,failed,finished⟩
        · exact Or.inl ⟨by omega,finished⟩
        · exact Or.inr ⟨by omega,error,finalExec,finalStore,finalPlatform,failed,finished⟩

/-- Actual finite progress with a uniform concrete bound, including a possible
final rejection and arbitrary host publication between successful dispatches. -/
theorem uniform_world_finite_progress {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : UniformWorldStepTotal memory hooks floats allocator view expected Inv)
    (dispatches : Nat) (initial : EventfulWorld M P view expected)
    (valid : Inv initial.code initial.machine.store) (last : ExecutionState M P)
    (trace : ContinuingTrace (executionBody memory hooks floats allocator) dispatches
      (initial.machine.exec,initial.machine.store,initial.machine.platform,.Ok ()) last) :
    ∃previous events count, Spec.StepsHN count (Abs.decode initial.machine.source) events (Abs.decode previous) ∧
      dispatches / (2 * U32.max + 3) ≤ count := by
  obtain ⟨previous,successes,events,history,endpoint⟩ := uniform_world_continuing_history memory hooks floats allocator Inv steps dispatches initial valid last trace
  obtain ⟨count,source,cost⟩ := uniform_world_history_progress history
  have counted : dispatches≤successes+1 := by rcases endpoint with ⟨same,_⟩ | ⟨same,_⟩ <;> omega
  refine ⟨previous.machine.source,events,count,source,?_⟩
  exact (finite_prefix_div_bound (2*U32.max+1) successes dispatches counted).trans cost
end Exec.Theorems

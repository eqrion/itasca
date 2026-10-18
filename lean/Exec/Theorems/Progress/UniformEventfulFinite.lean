import Exec.Theorems.Composition.Uniform.UniformEventfulHistory
import Exec.Interp.Machines.Slice.SliceFinite
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- The local contract for quantitative progress is normality and a checked
uniform source edge on each successful actual dispatch. -/
def UniformEventfulInvStepTotal {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (expected : List valtype)
    (Inv : runtime.store.Store M → Prop) : Prop :=
  ∀ machine : EventfulMachine emission allowed M P view code expected, Inv machine.store → 0<machine.exec.frames.length →
    runtime.interp.step memory hooks floats allocator machine.exec machine.store machine.platform ⦃ out =>
      Inv out.2.2.1 ∧ (out.1=.Ok () → ∃events next,out=(.Ok (),next.exec,next.store,next.platform) ∧
        UniformEventfulTransition memory hooks floats allocator machine events next) ⦄

/-- Exact actual continuing prefixes consist of successful uniform edges and
at most one final error. Errors never generate an additional loop iteration. -/
def UniformEventfulPrefix {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (initial : EventfulMachine emission allowed M P view code expected) (dispatches : Nat) (last : ExecutionState M P) : Prop :=
  ∃previous successes events,
    Spec.Iterations (UniformEventfulTransition memory hooks floats allocator) successes initial events previous ∧
    ((successes=dispatches ∧ last=(previous.exec,previous.store,previous.platform,.Ok ())) ∨
     (successes+1=dispatches ∧ ∃error finalExec finalStore finalPlatform,
       runtime.interp.step memory hooks floats allocator previous.exec previous.store previous.platform=
         .ok (.Err error,finalExec,finalStore,finalPlatform) ∧
       last=(finalExec,finalStore,finalPlatform,.Err error)))

theorem uniform_eventful_continuing_history {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (Inv : runtime.store.Store M → Prop)
    (steps : UniformEventfulInvStepTotal (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected Inv)
    (dispatches : Nat) (initial : EventfulMachine emission allowed M P view code expected)
    (valid : Inv initial.store) (last : ExecutionState M P)
    (trace : ContinuingTrace (executionBody memory hooks floats allocator) dispatches
      (initial.exec,initial.store,initial.platform,.Ok ()) last) :
    UniformEventfulPrefix memory hooks floats allocator initial dispatches last := by
  induction dispatches generalizing initial last with
  | zero =>
    cases trace
    exact ⟨initial,0,[],.refl initial,Or.inl ⟨rfl,rfl⟩⟩
  | succ count ih =>
    cases trace with
    | @next _ _ next _ bodyStep tail =>
      have active : 0 < initial.exec.frames.length := by
        by_contra inactive
        have empty : ¬initial.exec.frames.len > 0#usize := by scalar_tac
        simp [executionBody,runtime.interp.invoke_with_loop2.body,empty] at bodyStep
      obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,returned,newValid,outcome⟩ :=
        WP.spec_imp_exists (steps initial valid active)
      rw [executionBody_active memory hooks floats allocator _ ⟨active,rfl⟩,returned] at bodyStep
      have nextEq : (nextExec,nextStore,nextPlatform,status)=next := by simpa [bind_ok] using bodyStep
      subst next
      cases status with
      | Err error =>
        cases tail with
        | nil => exact ⟨initial,0,[],.refl initial,Or.inr ⟨rfl,error,nextExec,nextStore,nextPlatform,returned,rfl⟩⟩
        | next stopped _ => simp [executionBody,runtime.interp.invoke_with_loop2.body,core.result.Result.is_ok] at stopped
      | Ok value =>
        cases value
        obtain ⟨events,next,equal,edge⟩ := outcome rfl
        have components : nextExec=next.exec ∧ nextStore=next.store ∧ nextPlatform=next.platform := by
          simpa only [Prod.mk.injEq,true_and] using equal
        obtain ⟨rfl,rfl,rfl⟩ := components
        obtain ⟨previous,successes,more,run,final⟩ := ih next newValid last tail
        refine ⟨previous,successes+1,events++more,Spec.Iterations.cons edge run,?_⟩
        rcases final with ⟨same,finished⟩ | ⟨same,error,finalExec,finalStore,finalPlatform,failed,finished⟩
        · exact Or.inl ⟨by omega,finished⟩
        · exact Or.inr ⟨by omega,error,finalExec,finalStore,finalPlatform,failed,finished⟩

/-- Actual finite progress with a uniform concrete bound, including a possible
final rejection and arbitrary host publication between successful dispatches. -/
theorem uniform_eventful_finite_progress {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (Inv : runtime.store.Store M → Prop)
    (steps : UniformEventfulInvStepTotal (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected Inv)
    (dispatches : Nat) (initial : EventfulMachine emission allowed M P view code expected)
    (valid : Inv initial.store) (last : ExecutionState M P)
    (trace : ContinuingTrace (executionBody memory hooks floats allocator) dispatches
      (initial.exec,initial.store,initial.platform,.Ok ()) last) :
    ∃previous events count, Spec.StepsHN count (Abs.decode initial.source) events (Abs.decode previous) ∧
      dispatches / (2 * U32.max + 3) ≤ count := by
  obtain ⟨previous,successes,events,history,endpoint⟩ := uniform_eventful_continuing_history memory hooks floats allocator Inv steps dispatches initial valid last trace
  obtain ⟨count,source,cost⟩ := uniform_eventful_history_progress history
  have counted : dispatches≤successes+1 := by rcases endpoint with ⟨same,_⟩ | ⟨same,_⟩ <;> omega
  refine ⟨previous.source,events,count,source,?_⟩
  exact (finite_prefix_div_bound (2*U32.max+1) successes dispatches counted).trans cost
end Exec.Theorems

import Exec.Theorems.Composition.World.ChosenWorldHistory
import Exec.Theorems.Composition.Eventful.EventfulWorldLoop
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

def ChosenWorldLoopInvariant (choices : Spec.SourceChoices) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (initial : ChosenWorld emission allowed M P view expected) (state : ExecutionState M P) : Prop :=
  match state.2.2.2 with
  | .Ok _ => ∃ current : ChosenWorld emission allowed M P view expected,
      Inv current.code current.machine.store ∧ ∃ count events,
      Spec.Iterations (ChosenWorldTransition choices memory hooks floats allocator) count initial events current ∧
      state.1=current.machine.exec ∧ state.2.1=current.machine.store ∧ state.2.2.1=current.machine.platform
  | .Err error => ∃ current : ChosenWorld emission allowed M P view expected,
      Inv current.code current.machine.store ∧ ∃ count events,
      Spec.Iterations (ChosenWorldTransition choices memory hooks floats allocator) count initial events current ∧
      runtime.interp.step memory hooks floats allocator current.machine.exec current.machine.store current.machine.platform=
        .ok (.Err error,state.1,state.2.1,state.2.2.1) ∧
      ChosenWorldStepResult choices memory hooks floats allocator Inv current (.Err error,state.1,state.2.1,state.2.2.1)

theorem chosen_world_loop_invariant_step {choices : Spec.SourceChoices} {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : ChosenWorldStepOutcomes choices (emission:=emission) (allowed:=allowed) memory hooks floats allocator view expected Inv)
    (initial : ChosenWorld emission allowed M P view expected)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (invariant : ChosenWorldLoopInvariant choices memory hooks floats allocator Inv initial (exec,store,platform,.Ok ()))
    (active : 0<exec.frames.length) :
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ (status,nextExec,nextStore,nextPlatform) =>
        ChosenWorldLoopInvariant choices memory hooks floats allocator Inv initial (nextExec,nextStore,nextPlatform,status) ⦄ := by
  obtain ⟨current,valid,count,events,history,sameExec,sameStore,samePlatform⟩ := invariant
  dsimp only at sameExec sameStore samePlatform
  obtain ⟨rfl,rfl,rfl⟩ := And.intro sameExec (And.intro sameStore samePlatform)
  obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,actual,outcome⟩ := WP.spec_imp_exists (steps current valid active)
  rw [actual,WP.spec_ok]
  cases status with
  | Ok value =>
    cases value
    obtain ⟨next,fresh,equal,edge⟩ := outcome
    have components : nextExec=next.machine.exec ∧ nextStore=next.machine.store ∧ nextPlatform=next.machine.platform := by
      simpa only [Prod.mk.injEq,true_and] using equal
    let more := stepHostEvents current.machine.exec current.machine.store (.Ok (),nextExec,nextStore,nextPlatform)
    have recorded : ChosenWorldTransition choices memory hooks floats allocator current more next := edge
    refine ⟨next,fresh,count+1,events++more,?_,components⟩
    simpa only [List.append_nil] using history_append history (Spec.Iterations.cons recorded (Spec.Iterations.refl next))
  | Err error => exact ⟨current,valid,count,events,history,actual,outcome⟩

/-- The actual loop preserves a changing ghost interpretation. Its finite
history uses the raw recorder's events and retains actual failing dispatches. -/
theorem chosen_world_loop_stops {choices : Spec.SourceChoices} {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : ChosenWorldStepOutcomes choices (emission:=emission) (allowed:=allowed) memory hooks floats allocator view expected Inv)
    (initial : ChosenWorld emission allowed M P view expected) (valid : Inv initial.code initial.machine.store) :
    runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())
      ⦃ result => ∃state,ChosenWorldLoopInvariant choices memory hooks floats allocator Inv initial state ∧
        ¬ActiveExecution state ∧ finishExecution state=result ⦄div := by
  apply execution_loop_stops memory hooks floats allocator
    (ChosenWorldLoopInvariant choices memory hooks floats allocator Inv initial)
    (chosen_world_loop_invariant_step memory hooks floats allocator Inv steps initial)
    initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())
  exact ⟨initial,valid,0,[],Spec.Iterations.refl initial,rfl,rfl,rfl⟩


end Exec.Theorems

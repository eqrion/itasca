import Exec.Theorems.Composition.Supported.ChosenMachine
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- A finite native prefix retains its chosen source ledger and its actual
history, including the last dispatch when an error stops the loop. -/
def ChosenSupportedLoopInvariant {choices : SourceChoices} {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (initial : ChosenSupportedMachine emission allowed M P view code expected) (state : ExecutionState M P) : Prop :=
  match state.2.2.2 with
  | .Ok _ => ∃ machine count,
      Iterations (ChosenSupportedTransition choices memory hooks floats allocator) count initial [] machine ∧
      machine.exec=state.1 ∧ machine.store=state.2.1 ∧ machine.platform=state.2.2.1
  | .Err error => ∃ machine count,
      Iterations (ChosenSupportedTransition choices memory hooks floats allocator) count initial [] machine ∧
      runtime.interp.step memory hooks floats allocator machine.exec machine.store machine.platform=
        .ok (.Err error,state.1,state.2.1,state.2.2.1) ∧
      ChosenCumulativeFailure choices machine.occurrence allocator hooks machine.exec machine.store machine.platform machine.source error ∧
      Store.decodeStore view code state.2.1=machine.source.store ∧
      CumulativeStoreMutation view code machine.store state.2.1

theorem chosen_supported_loop_invariant_step {choices : SourceChoices} {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (steps : ChosenSupportedStepOutcomes (emission:=emission) (allowed:=allowed) choices memory hooks floats allocator view code expected)
    (initial : ChosenSupportedMachine emission allowed M P view code expected)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (invariant : ChosenSupportedLoopInvariant (choices:=choices) memory hooks floats allocator initial (exec,store,platform,.Ok ()))
    (active : 0<exec.frames.length) :
    runtime.interp.step memory hooks floats allocator exec store platform
      ⦃ (status,nextExec,nextStore,nextPlatform) => ChosenSupportedLoopInvariant (choices:=choices) memory hooks floats allocator initial
        (nextExec,nextStore,nextPlatform,status) ⦄ := by
  obtain ⟨machine,count,history,sameExec,sameStore,samePlatform⟩ := invariant
  dsimp only at sameExec sameStore samePlatform
  subst exec
  subst store
  subst platform
  obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,actual,mutation,outcome⟩ := WP.spec_imp_exists (steps machine active)
  rw [actual,WP.spec_ok]
  cases status with
  | Err error => exact ⟨machine,count,history,actual,outcome.1,outcome.2,mutation⟩
  | Ok unit =>
    cases unit
    obtain ⟨after,same,edge⟩ := outcome
    have components : nextExec=after.exec ∧ nextStore=after.store ∧ nextPlatform=after.platform := by
      simpa only [Prod.mk.injEq,true_and] using same
    exact ⟨after,count+1,history_snoc history edge,components.1.symm,components.2.1.symm,components.2.2.symm⟩

/-- The actual loop is safe, and every finite return exposes a fixed-policy
source prefix. Divergence is handled separately by chosen reflection. -/
theorem chosen_supported_loop_stops {choices : SourceChoices} {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (steps : ChosenSupportedStepOutcomes (emission:=emission) (allowed:=allowed) choices memory hooks floats allocator view code expected)
    (initial : ChosenSupportedMachine emission allowed M P view code expected) :
    runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ result => ∃ state, ChosenSupportedLoopInvariant (choices:=choices) memory hooks floats allocator initial state ∧
        ¬ActiveExecution state ∧ finishExecution state=result ⦄div := by
  apply execution_loop_stops memory hooks floats allocator
    (ChosenSupportedLoopInvariant (choices:=choices) memory hooks floats allocator initial)
    (chosen_supported_loop_invariant_step memory hooks floats allocator steps initial)
    initial.exec initial.store initial.platform (.Ok ())
  exact ⟨initial,0,Iterations.refl initial,rfl,rfl,rfl⟩
end Exec.Theorems

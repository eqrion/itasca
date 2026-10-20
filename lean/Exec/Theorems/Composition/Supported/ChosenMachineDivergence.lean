import Exec.Theorems.Composition.Supported.ChosenMachine
import Exec.Interp.Invocation.InvokeDivergence
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem chosen_supported_divergent_next {choices : SourceChoices} {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (steps : ChosenSupportedStepOutcomes (emission:=emission) (allowed:=allowed) choices memory hooks floats allocator view code expected)
    (before : ChosenSupportedMachine emission allowed M P view code expected)
    (divergent : loop (executionBody memory hooks floats allocator) (before.exec,before.store,before.platform,.Ok ())=.div) :
    ∃ after, ChosenSupportedTransition choices memory hooks floats allocator before [] after ∧
      loop (executionBody memory hooks floats allocator) (after.exec,after.store,after.platform,.Ok ())=.div := by
  have active := execution_loop_divergent_active memory hooks floats allocator before.exec before.store before.platform divergent
  obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,actual,mutation,outcome⟩ := WP.spec_imp_exists (steps before active)
  rw [loop.eq_def,executionBody_active memory hooks floats allocator _ ⟨active,rfl⟩,actual] at divergent
  simp [bind_ok] at divergent
  cases status with
  | Err error => rw [execution_loop_error memory hooks floats allocator] at divergent; simp at divergent
  | Ok unit =>
    cases unit
    obtain ⟨after,same,edge⟩ := outcome
    have components : nextExec=after.exec ∧ nextStore=after.store ∧ nextPlatform=after.platform := by
      simpa only [Prod.mk.injEq,true_and] using same
    exact ⟨after,edge,by simpa only [components.1,components.2.1,components.2.2] using divergent⟩

/-- Divergence of the actual native loop reflects an infinite source execution
under the same preselected policy, with its original occurrence ledger. -/
theorem chosen_supported_loop_infinite {choices : SourceChoices} {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (steps : ChosenSupportedStepOutcomes (emission:=emission) (allowed:=allowed) choices memory hooks floats allocator view code expected)
    (initial : ChosenSupportedMachine emission allowed M P view code expected)
    (divergent : runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())=.div) :
    InfiniteChosenSource choices initial.occurrence (Abs.decode initial.source) := by
  let Running := {before : ChosenSupportedMachine emission allowed M P view code expected //
    runtime.interp.invoke_with_loop2 memory hooks floats allocator before.exec before.store before.platform (.Ok ())=.div}
  let edge := fun (before : Running) (events : List HostEvent) (after : Running) =>
    ChosenSupportedTransition choices memory hooks floats allocator before.val events after.val
  apply infinite_chosen_of_decreasing_stutter choices edge (fun p=>Abs.decode p.val.source)
    (fun p=>p.val.occurrence) (fun p=>p.val.potential) ?_ ?_ ⟨initial,divergent⟩
  · intro before
    obtain ⟨after,step,divergent⟩ := chosen_supported_divergent_next memory hooks floats allocator steps before.val before.property
    exact ⟨[],⟨after,divergent⟩,step⟩
  · intro before events after step
    exact step.selected
end Exec.Theorems

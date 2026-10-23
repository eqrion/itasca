import Exec.Theorems.Composition.World.ChosenWorld
import Exec.Interp.Invocation.InvokeDivergence
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem chosen_world_divergent_next {choices : SourceChoices} {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : ChosenWorldStepOutcomes (emission:=emission) (allowed:=allowed) choices memory hooks floats allocator view expected Inv)
    (before : ChosenWorld emission allowed M P view expected)
    (valid : Inv before.code before.machine.store)
    (divergent : loop (executionBody memory hooks floats allocator) (before.machine.exec,before.machine.store,before.machine.platform,.Ok ())=.div) :
    ∃ after, Inv after.code after.machine.store ∧ ChosenWorldTransition choices memory hooks floats allocator before (stepHostEvents before.machine.exec before.machine.store (.Ok (),after.machine.exec,after.machine.store,after.machine.platform)) after ∧
      loop (executionBody memory hooks floats allocator) (after.machine.exec,after.machine.store,after.machine.platform,.Ok ())=.div := by
  have active := execution_loop_divergent_active memory hooks floats allocator before.machine.exec before.machine.store before.machine.platform divergent
  obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,actual,outcome⟩ := WP.spec_imp_exists (steps before valid active)
  rw [loop.eq_def,executionBody_active memory hooks floats allocator _ ⟨active,rfl⟩,actual] at divergent
  simp [bind_ok] at divergent
  cases status with
  | Err error => rw [execution_loop_error memory hooks floats allocator] at divergent; simp at divergent
  | Ok unit =>
    cases unit
    obtain ⟨after,fresh,same,edge⟩ := outcome
    have components : nextExec=after.machine.exec ∧ nextStore=after.machine.store ∧ nextPlatform=after.machine.platform := by
      simpa only [Prod.mk.injEq,true_and] using same
    exact ⟨after,fresh,by simpa only [components.1,components.2.1,components.2.2] using edge,by simpa only [components.1,components.2.1,components.2.2] using divergent⟩

/-- Divergence of the actual native loop reflects an infinite source execution
under the same preselected policy, with its original occurrence ledger. -/
theorem chosen_world_loop_infinite {choices : SourceChoices} {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : ChosenWorldStepOutcomes (emission:=emission) (allowed:=allowed) choices memory hooks floats allocator view expected Inv)
    (initial : ChosenWorld emission allowed M P view expected)
    (valid : Inv initial.code initial.machine.store)
    (divergent : runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())=.div) :
    InfiniteChosenSource choices initial.occurrence (Abs.decode initial.machine.source) := by
  let Running := {before : ChosenWorld emission allowed M P view expected //
    Inv before.code before.machine.store ∧ runtime.interp.invoke_with_loop1 memory hooks floats allocator before.machine.exec before.machine.store before.machine.platform (.Ok ())=.div}
  let edge := fun (before : Running) (events : List HostEvent) (after : Running) =>
    ChosenWorldTransition choices memory hooks floats allocator before.val events after.val
  apply infinite_chosen_of_decreasing_stutter choices edge (fun p=>Abs.decode p.val.machine.source)
    (fun p=>p.val.occurrence) (fun p=>p.val.potential) ?_ ?_ ⟨initial,valid,divergent⟩
  · intro before
    obtain ⟨after,fresh,step,divergent⟩ := chosen_world_divergent_next memory hooks floats allocator Inv steps before.val before.property.1 before.property.2
    exact ⟨_,⟨after,fresh,divergent⟩,step⟩
  · intro before events after step
    exact step.selected
end Exec.Theorems

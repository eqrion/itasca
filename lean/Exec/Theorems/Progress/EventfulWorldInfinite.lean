import Exec.Theorems.Composition.Eventful.EventfulWorldLoop
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- An actual divergent loop retains its current interpretation and invariant
through the next recorded dispatch, including a host publication. -/
theorem world_divergent_next {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : WorldStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view expected Inv)
    (before : EventfulWorld emission allowed M P view expected) (valid : Inv before.code before.machine.store)
    (divergent : runtime.interp.invoke_with_loop1 memory hooks floats allocator before.machine.exec before.machine.store before.machine.platform (.Ok ())=.div) :
    ∃events next,WorldRecordedTransition memory hooks floats allocator before events next ∧ Inv next.code next.machine.store ∧
      runtime.interp.invoke_with_loop1 memory hooks floats allocator next.machine.exec next.machine.store next.machine.platform (.Ok ())=.div := by
  have active := execution_loop_divergent_active memory hooks floats allocator before.machine.exec before.machine.store before.machine.platform divergent
  obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,returned,outcome⟩ := WP.spec_imp_exists (steps before valid active)
  change loop (executionBody memory hooks floats allocator) (before.machine.exec,before.machine.store,before.machine.platform,.Ok ())=.div at divergent
  rw [loop.eq_def,executionBody_active memory hooks floats allocator _ ⟨active,rfl⟩,returned] at divergent
  simp [bind_ok] at divergent
  cases status with
  | Err error => rw [execution_loop_error memory hooks floats allocator] at divergent; simp at divergent
  | Ok value =>
    cases value
    obtain ⟨next,fresh,equal,edge⟩ := outcome
    have components : nextExec=next.machine.exec ∧ nextStore=next.machine.store ∧ nextPlatform=next.machine.platform := by
      simpa only [Prod.mk.injEq,true_and] using equal
    refine ⟨_,next,⟨edge,?_⟩,fresh,?_⟩
    · simp only [components.1,components.2.1,components.2.2]
    · change loop (executionBody memory hooks floats allocator) (next.machine.exec,next.machine.store,next.machine.platform,.Ok ())=.div
      simpa only [components.1,components.2.1,components.2.2] using divergent

/-- Source progress composes across evolving interpretations without a fixed
initial or future set of compiled functions. -/
theorem world_loop_infinite {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : WorldStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view expected Inv)
    (initial : EventfulWorld emission allowed M P view expected) (valid : Inv initial.code initial.machine.store)
    (divergent : runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())=.div) :
    Spec.InfiniteSourceWithEvents (Abs.decode initial.machine.source) := by
  let running := fun state : EventfulWorld emission allowed M P view expected => Inv state.code state.machine.store ∧
    runtime.interp.invoke_with_loop1 memory hooks floats allocator state.machine.exec state.machine.store state.machine.platform (.Ok ())=.div
  let next := fun (before : {s // running s}) events (after : {s // running s}) =>
    WorldRecordedTransition memory hooks floats allocator before.val events after.val
  apply Spec.infinite_source_of_decreasing_stutter next
    (fun s=>Abs.decode s.val.machine.source) (fun s=>s.val.machine.potential) ?_ ?_ ⟨initial,valid,divergent⟩
  · intro current
    obtain ⟨events,after,edge,fresh,divergent⟩ := world_divergent_next memory hooks floats allocator Inv steps current.val current.property.1 current.property.2
    exact ⟨events,⟨after,fresh,divergent⟩,edge⟩
  · intro before events after edge
    exact edge.edge.simulation
end Exec.Theorems

import Exec.Theorems.Api.EventfulInvLoop
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- The next actual divergent dispatch retains the same auxiliary invariant. -/
theorem eventful_inv_divergent_next {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (Inv : runtime.store.Store M → Prop)
    (steps : EventfulInvStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected Inv)
    (machine : EventfulMachine emission allowed M P view code expected) (valid : Inv machine.store)
    (divergent : runtime.interp.invoke_with_loop2 memory hooks floats allocator machine.exec machine.store machine.platform (.Ok ())=.div) :
    ∃events next,EventfulTransition memory hooks floats allocator machine events next ∧ Inv next.store ∧
      runtime.interp.invoke_with_loop2 memory hooks floats allocator next.exec next.store next.platform (.Ok ())=.div := by
  have active := execution_loop_divergent_active memory hooks floats allocator machine.exec machine.store machine.platform divergent
  obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,returned,fresh,outcome⟩ := WP.spec_imp_exists (steps machine valid active)
  change loop (executionBody memory hooks floats allocator) (machine.exec,machine.store,machine.platform,.Ok ())=.div at divergent
  rw [loop.eq_def,executionBody_active memory hooks floats allocator _ ⟨active,rfl⟩,returned] at divergent
  simp [bind_ok] at divergent
  cases status with
  | Err error => rw [execution_loop_error memory hooks floats allocator] at divergent; simp at divergent
  | Ok unit =>
    cases unit
    obtain ⟨events,next,equal,edge⟩ := outcome.1 rfl
    have components : nextExec=next.exec ∧ nextStore=next.store ∧ nextPlatform=next.platform := by
      simpa only [Prod.mk.injEq,true_and] using equal
    refine ⟨events,next,edge,?_,?_⟩
    · simpa only [components.2.1] using fresh
    · change loop (executionBody memory hooks floats allocator) (next.exec,next.store,next.platform,.Ok ())=.div
      simpa only [components.1,components.2.1,components.2.2] using divergent

/-- Divergence under an invariant-indexed host law yields a coherent infinite
source execution, carrying that invariant through every concrete successor. -/
theorem eventful_inv_loop_infinite {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (Inv : runtime.store.Store M → Prop)
    (steps : EventfulInvStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected Inv)
    (initial : EventfulMachine emission allowed M P view code expected) (valid : Inv initial.store)
    (divergent : runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())=.div) :
    Spec.InfiniteSourceWithEvents (Abs.decode initial.source) := by
  apply EventfulMachine.infinite_source
    (fun machine=>Inv machine.store ∧ runtime.interp.invoke_with_loop2 memory hooks floats allocator machine.exec machine.store machine.platform (.Ok ())=.div)
    (fun machine running=>eventful_inv_divergent_next memory hooks floats allocator Inv steps machine running.1 running.2) initial ⟨valid,divergent⟩
end Exec.Theorems

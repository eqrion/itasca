import Exec.Theorems.Composition.Eventful.EventfulHistory
import Exec.Interp.Machines.Slice.SliceDivergence
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- The per-dispatch obligation used by the eventful loop composition. This
requires actual normal return and constructs an exact successful edge; it is
not assumed as a platform law. Common dispatch must prove it. -/
def EventfulStepTotal {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (expected : List valtype) : Prop :=
  ∀ machine : EventfulMachine emission allowed M P view code expected, 0 < machine.exec.frames.length →
    runtime.interp.step memory hooks floats allocator machine.exec machine.store machine.platform ⦃ out =>
      out.1=.Ok () → ∃ events next,
        out=(.Ok (),next.exec,next.store,next.platform) ∧
        EventfulTransition memory hooks floats allocator machine events next ⦄

theorem eventful_divergent_next {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (steps : EventfulStepTotal (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected)
    (machine : EventfulMachine emission allowed M P view code expected)
    (divergent : runtime.interp.invoke_with_loop1 memory hooks floats allocator machine.exec machine.store machine.platform (.Ok ())=.div) :
    ∃ events next, EventfulTransition memory hooks floats allocator machine events next ∧
      runtime.interp.invoke_with_loop1 memory hooks floats allocator next.exec next.store next.platform (.Ok ())=.div := by
  have active := execution_loop_divergent_active memory hooks floats allocator machine.exec machine.store machine.platform divergent
  obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,returned,outcome⟩ := WP.spec_imp_exists (steps machine active)
  change loop (executionBody memory hooks floats allocator) (machine.exec,machine.store,machine.platform,.Ok ())=.div at divergent
  rw [loop.eq_def,executionBody_active memory hooks floats allocator _ ⟨active,rfl⟩,returned] at divergent
  simp [bind_ok] at divergent
  cases status with
  | Err error => rw [execution_loop_error memory hooks floats allocator] at divergent; simp at divergent
  | Ok unit =>
    cases unit
    obtain ⟨events,next,equal,edge⟩ := outcome rfl
    have components : nextExec=next.exec ∧ nextStore=next.store ∧ nextPlatform=next.platform := by
      simpa only [Prod.mk.injEq,true_and] using equal
    refine ⟨events,next,edge,?_⟩
    change loop (executionBody memory hooks floats allocator) (next.exec,next.store,next.platform,.Ok ())=.div
    simpa only [components.1,components.2.1,components.2.2] using divergent

/-- Actual loop divergence implies a coherent infinite eventful source run,
once the checked common dispatch has discharged `EventfulStepTotal`. -/
theorem eventful_loop_infinite {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (steps : EventfulStepTotal (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected)
    (initial : EventfulMachine emission allowed M P view code expected)
    (divergent : runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())=.div) :
    Spec.InfiniteSourceWithEvents (Abs.decode initial.source) := by
  apply EventfulMachine.infinite_source
    (fun machine => runtime.interp.invoke_with_loop1 memory hooks floats allocator machine.exec machine.store machine.platform (.Ok ())=.div)
    (fun machine divergent => eventful_divergent_next memory hooks floats allocator steps machine divergent) initial divergent
/-- Normal per-dispatch execution rules out panic throughout the actual loop,
including executions that eventually return an error or run forever. -/
theorem eventful_loop_safe {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (steps : EventfulStepTotal (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected)
    (initial : EventfulMachine emission allowed M P view code expected) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ _ => True ⦄div := by
  let invariant (state : ExecutionState M P) : Prop :=
    (∃ error,state.2.2.2=.Err error) ∨
    ∃ machine : EventfulMachine emission allowed M P view code expected,
      state=(machine.exec,machine.store,machine.platform,.Ok ())
  apply WP.dspec_mono (execution_loop_trace_safe memory hooks floats allocator invariant (fun _=>True)
    ?_ (fun _ _ _=>True.intro) initial.exec initial.store initial.platform (.Ok ()) (Or.inr ⟨initial,rfl⟩))
  · intro result post
    trivial
  · intro exec store platform valid active
    rcases valid with ⟨error,impossible⟩ | ⟨machine,equal⟩
    · cases impossible
    · have components : exec=machine.exec ∧ store=machine.store ∧ platform=machine.platform := by
        simpa only [Prod.mk.injEq,and_true] using equal
      obtain ⟨rfl,rfl,rfl⟩ := components
      apply WP.spec_mono (steps machine active)
      rintro ⟨status,nextExec,nextStore,nextPlatform⟩ result
      cases status with
      | Err error => exact Or.inl ⟨error,rfl⟩
      | Ok value =>
        cases value
        obtain ⟨events,next,equal,edge⟩ := result rfl
        have components : nextExec=next.exec ∧ nextStore=next.store ∧ nextPlatform=next.platform := by
          simpa only [Prod.mk.injEq,true_and] using equal
        exact Or.inr ⟨next,by simp only [components.1,components.2.1,components.2.2]⟩

end Exec.Theorems

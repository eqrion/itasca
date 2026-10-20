import Exec.Theorems.Composition.World.ChosenWorldLoopResult
import Exec.Theorems.Composition.World.ChosenWorldResourceBounds
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

theorem ChosenWorldLoopInvariant.only_trap_error {choices : SourceChoices} {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A} {view : M → Slice U8} {expected : List valtype}
    {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop}
    {initial : ChosenWorld emission allowed M P view expected} {state : ExecutionState M P} {error : runtime.ExecError}
    (capacities : ∀ code store,Inv code store → Store.FunctionCapacities code store)
    {valueLimit frameLimit : Nat}
    (floors : ∀ code store,Inv code store → valueLimit≤store.limits.max_values.val ∧ frameLimit≤store.limits.max_frames.val)
    (resources : ChosenWorldResources choices initial.occurrence (Abs.decode initial.machine.source) valueLimit frameLimit)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after)) (noOverflow : NoHostStackOverflow hooks Inv)
    (held : ChosenWorldLoopInvariant choices memory hooks floats allocator Inv initial state)
    (failed : state.2.2.2=.Err error) : ∃ trap,error=.Trap trap := by
  rcases state with ⟨exec,store,platform,status⟩
  dsimp only at failed
  subst status
  obtain ⟨previous,valid,count,events,history,actual,afterCode,fresh,certified,retained,agrees,extension,outcome,cause⟩ := held
  obtain ⟨sourceCount,clock,sourceSteps⟩ := ChosenWorld.history_source history
  have adequate := resources sourceCount events previous.machine.source sourceSteps
  have limits := floors previous.code previous.machine.store valid
  have classified : EventfulSourceResourceCause hooks allocator previous.machine (.Err error,exec,store,platform) error :=
    EventfulDispatchCause.source_resources (capacities previous.code previous.machine.store valid) cause
  have excludes := classified.excludes_boundary adequate limits.1 limits.2 available continuing
    (noOverflow previous.code previous.machine.store valid)
  cases error with
  | Trap trap => exact ⟨trap,rfl⟩
  | Terminated => exact False.elim (excludes (Or.inl rfl))
  | Exhausted resource =>
    cases resource with
    | CallStack => exact False.elim (excludes (Or.inr (Or.inl rfl)))
    | Values => exact False.elim (excludes (Or.inr (Or.inr (Or.inl rfl))))
    | Allocation => exact False.elim (excludes (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | Objects => exact False.elim (excludes (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  | BadArguments => exact False.elim outcome
  | WrongStore => exact False.elim outcome
  | Link reason => exact False.elim outcome

/-- Every returned loop error is a source trap under independent source
capacities, primitive allocation availability, limit floors and host laws. -/
theorem chosen_world_loop_no_boundary {choices : SourceChoices} {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : ChosenWorldStepOutcomes (emission:=emission) (allowed:=allowed) choices memory hooks floats allocator view expected Inv)
    (initial : ChosenWorld emission allowed M P view expected) (valid : Inv initial.code initial.machine.store)
    (capacities : ∀ code store,Inv code store → Store.FunctionCapacities code store) {valueLimit frameLimit : Nat}
    (floors : ∀ code store,Inv code store → valueLimit≤store.limits.max_values.val ∧ frameLimit≤store.limits.max_frames.val)
    (resources : ChosenWorldResources choices initial.occurrence (Abs.decode initial.machine.source) valueLimit frameLimit)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after)) (noOverflow : NoHostStackOverflow hooks Inv) :
    runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())
      ⦃ result => ChosenWorldLoopResult choices Inv initial result ∧
        ∀ error,result.2.2.2.2.2.2.2=.Err error → ∃ trap,error=.Trap trap ⦄div := by
  apply WP.dspec_mono (chosen_world_loop_stops memory hooks floats allocator Inv steps initial valid)
  rintro result ⟨state,held,stopped,rfl⟩
  refine ⟨chosen_world_loop_finished memory hooks floats allocator Inv initial state held stopped,?_⟩
  intro error failed
  exact held.only_trap_error capacities floors resources available continuing noOverflow failed
end Exec.Theorems

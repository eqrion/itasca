import Exec.Theorems.Composition.Supported.ChosenLoopAgreement
import Exec.Theorems.Composition.Supported.ChosenResourceFailure
import Exec.Theorems.Composition.Supported.ChosenLoopCompletion
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Storage adequacy is checked on source prefixes under the selected policy.
Neither native execution success nor absence of exhaustion occurs here. -/
def ChosenSourceResources (choices : SourceChoices) (occurrence : Nat)
    (limits : runtime.store.StoreLimits) (initial : Abs.AState) : Prop :=
  ∀ count source, ChosenStepsN choices occurrence count (Abs.decode initial) [] (Abs.decode source) →
    SourceDispatchResources limits source

theorem ChosenSupportedLoopOutcome.agrees_of_resources {choices : SourceChoices} (admissible : choices.Admissible) {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {initial : ChosenSupportedMachine emission allowed M P view code expected} {result : ExecutionResult M P}
    (outcome : ChosenSupportedLoopOutcome choices memory hooks floats allocator initial result)
    (capacities : Store.FunctionCapacities code initial.store)
    (resources : ChosenSourceResources choices initial.occurrence initial.store.limits initial.source)
    {bound : Nat} (available : Platform.AllocationAvailable allocator bound)
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (frameBound : initial.store.limits.max_frames.val≤bound) (valueBound : initial.store.limits.max_values.val≤bound)
    {events : List HostEvent} {target : config}
    (run : ChoiceSteps choices initial.occurrence (Abs.decode initial.source) events target)
    (terminal : SourceTerminal target) :
    ChosenLoopAgreement view code initial.source.ambient events target result := by
  rcases outcome.agrees_or_boundary admissible run terminal with agreement | boundary
  · exact agreement
  · obtain ⟨previous,dispatches,count,error,finalExec,finalStore,finalPlatform,history,source,cause,kind,decoded,mutation,actual,returned⟩ := boundary
    have erased := ChosenSupportedMachine.history_erases history
    have limits := SupportedMachine.history_limits memory hooks floats allocator erased
    have metadata := (SupportedMachine.history_metadata memory hooks floats allocator erased).2.1
    have retained := capacities.metadata metadata.functions metadata.instances metadata.types metadata.identity
    have adequate : SourceDispatchResources previous.store.limits previous.source := by
      rw [limits]
      exact resources count previous.source source
    obtain ⟨trap,same,allowed⟩ := cause.resources_trap previous.invariant retained previous.certified.typed adequate available continuing
      (by simpa only [limits] using frameBound) (by simpa only [limits] using valueBound)
    rcases kind with rfl | rfl | rfl | rfl <;> cases same

/-- One terminating chosen source run, sufficient source storage and primitive
allocation availability give the corresponding native loop values or trap,
with the exact decoded final store and direct event list. -/
theorem chosen_supported_loop_matches {choices : SourceChoices} (admissible : choices.Admissible) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (steps : ChosenSupportedStepOutcomes (emission:=emission) (allowed:=allowed) choices memory hooks floats allocator view code expected)
    (initial : ChosenSupportedMachine emission allowed M P view code expected)
    (capacities : Store.FunctionCapacities code initial.store)
    (resources : ChosenSourceResources choices initial.occurrence initial.store.limits initial.source)
    {bound : Nat} (available : Platform.AllocationAvailable allocator bound)
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (frameBound : initial.store.limits.max_frames.val≤bound) (valueBound : initial.store.limits.max_values.val≤bound)
    {events : List HostEvent} {target : config}
    (run : ChoiceSteps choices initial.occurrence (Abs.decode initial.source) events target)
    (terminal : SourceTerminal target) :
    runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ result => ChosenSupportedLoopOutcome choices memory hooks floats allocator initial result ∧
        ChosenLoopAgreement view code initial.source.ambient events target result ⦄ := by
  apply WP.spec_mono (chosen_supported_loop_terminates admissible memory hooks floats allocator steps initial run terminal)
  rintro result ⟨state,invariant,stopped,rfl⟩
  have outcome := chosen_supported_loop_finished memory hooks floats allocator initial state invariant stopped
  exact ⟨outcome,outcome.agrees_of_resources admissible capacities resources available continuing frameBound valueBound run terminal⟩
end Exec.Theorems

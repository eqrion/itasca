import Exec.Theorems.Invocation.PublicWorldChosenDivergence

/-! Normal return from one terminating compatible selected source run.
Resource sufficiency is a separate obligation of selected-run completeness. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
/-- One terminating selected source run yields ordinary public invocation
return with the actual recorder graph and full invariant. Resource errors
remain possible without independent capacity and allocation sufficiency. -/
theorem invoke_executable_world_chosen_terminates {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (sound : HostWorldChosenSound memory hooks view (ExecutableInv view) choices)
    (preserve : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    {events : List HostEvent} {target : config}
    (run : Spec.ChoiceSteps choices 0 initial events target) (terminal : Spec.SourceTerminal target) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∃ events,
        recordedInvokeWith memory hooks floats allocator exec store platform address args results [] = .ok (out, events) ∧
        ExecutableWorldRecordedOutcome view code store exec platform results initial out events ⦄ := by
  have notdiv : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results ≠ .div := by
    intro divergent
    exact Spec.chosen_terminating_no_infinite admissible run terminal (invoke_executable_world_infinite_chosen admissible numericChoice vector memory hooks floats allocator correct allocation
      interrupts view laws code compatible sound preserve externs issuedResults exec store platform valid address args results
      issued argumentIssued initial invoked divergent)
  have safe := invoke_executable_world_source_resources memory hooks floats allocator correct allocation
    interrupts view laws code sound.erases preserve externs issuedResults exec store platform valid address args results
    issued argumentIssued initial invoked
  generalize answerEq : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results = answer at safe notdiv ⊢
  cases safe with
  | ret post =>
    obtain ⟨events,recorded,outcome,causes⟩ := post
    exact .ret ⟨events,recorded,outcome⟩
  | div => exact False.elim (notdiv rfl)
end Exec.Theorems

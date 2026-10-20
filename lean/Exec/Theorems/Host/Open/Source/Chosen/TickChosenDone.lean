import Exec.Theorems.Host.Open.Source.State.TickDone
import Exec.Theorems.Host.Open.Source.Chosen.TickChosenCont
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem source_tick_chosen_done {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (occurrence : Nat)
    (code : Store.CodeInterpretation) (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (shape : native.Shape .invocation) (outcome : Outcome M)
    (actual : tick memory floats allocator select native=.ok (.done outcome)) :
    ∃completed,Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence 1 source
      [Spec.OpenExecution.Observation.invokeExit (match outcome with
        | .invocation answer _=>sourceInvocationResult answer.1 answer.2.2.2.2 | .host _ _=>.trapped)] completed ∧
      completed.Typed ∧ SourceOutcome view code outcome completed ∧
      sourceHistory outcome.history=sourceHistory native.history++
        [Spec.OpenExecution.Observation.invokeExit (match outcome with
          | .invocation answer _=>sourceInvocationResult answer.1 answer.2.2.2.2 | .host _ _=>.trapped)] := by
  have boundary:=tick_done_boundary memory floats allocator select native .invocation shape outcome actual
  rcases native with ⟨store,mode,stack,history⟩
  rcases source with ⟨sourceStore,sourceMode,sourceStack⟩
  rcases guard with ⟨held,related,stackGuard,storeEq⟩
  have guard:=SourceStateGuard.mk held related stackGuard storeEq
  cases related with
  | host raw hostSource represented | preparing exec address signature args results phase metadata ready | wasm signature world root results metadata typed | finishing exec error root results signature metadata=>
    cases stack <;> simp [Erased.Nonterminal,Erased.state] at boundary
  | draft status values owned=>
    simp only [State.Shape,Mode.kind] at shape
    cases shape with
    | wasm ready address base root results under=>simp [Erased.Nonterminal,Erased.state] at boundary
  | returned answer sameStore issued=>
    cases stackGuard with
    | nil=>
      obtain ⟨computed,step,typed,storeSame,projected⟩:=source_invoke_exit memory floats allocator view select owner stop code _ _ guard
        answer rfl rfl rfl rfl
      have equal : outcome=.invocation answer (history++[Observation.invokeExit answer.1 answer.2.2.2.2]):=by
        simpa only [Result.ok.injEq,ControlFlow.done.injEq] using actual.symm.trans computed
      subst outcome
      have chosenStep:=choose_control_transition choices occurrence step
        (by intro f body expected impossible;cases impossible) (by simp)
      exact ⟨_,.next chosenStep (.nil _ _),typed,⟨rfl,rfl,storeSame⟩,projected⟩
    | cons head tail=>simp [Erased.Nonterminal,Erased.state] at boundary
end Exec.Theorems.OpenReentrantControl

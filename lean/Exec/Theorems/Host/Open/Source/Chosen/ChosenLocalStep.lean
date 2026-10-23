import Exec.Theorems.Host.Open.Source.Control.LocalStep
import Exec.Theorems.Host.Open.Source.State.Single
import Exec.Theorems.Host.Open.Source.Chosen.ChosenLocalTick
import Exec.Theorems.Host.Open.Driver.DriverTick
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp
/-- One actual local host tick advances the independent source control once.
The whole suspended stack is transported through its committed effect. -/
theorem source_local_chosen_single {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (compatible : SourceAPIChoicesCompatible memory allocator view choices) (occurrence : Nat)
    (code : Store.CodeInterpretation) (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (host : HostState) (hostSource : SourceHostState) (mode : native.mode=.host host)
    (sourceMode : source.mode=.host (.active hostSource))
    (represented : HostStateRepresents native.store.id hostSource host)
    (localInstruction : ∀instruction,host.code[host.pc]?=some instruction →
      match instruction with | .invoke _ _ _ | .publish _ _ _ _=>False | _=>True) :
    tick memory floats allocator select native ⦃out=>∃next,out=.cont next ∧
      ChosenSourceSingle memory allocator view select owner stop choices occurrence code native source rank next⦄ := by
  obtain ⟨out,actual,next,control,same,stackEq,historyEq,effect,action,chosen,controlRep⟩ := WP.spec_imp_exists
    (source_local_chosen_tick memory floats allocator allocation view laws code (sourcePublication allocator view) choices compatible occurrence select native
      guard.invariant host mode hostSource represented localInstruction)
  subst out
  rw [actual]
  have nativeSafe := tick_guard memory floats allocator correct allocation view laws select code native guard.native
  rw [actual,WP.spec_ok] at nativeSafe
  obtain ⟨otherCode,otherEffect,afterGuard⟩ := nativeSafe
  let nextSource : Spec.OpenExecution.State SourceControl:=⟨Store.decodeStore view code next.store,.host control,source.stack⟩
  have worldEffect:=local_effect_world effect
  have sameOwner : next.store.id=native.store.id:=effect.metadata.identity
  have representedAfter : SourceControlRepresents next.store.id control next.mode := by
    rw [sameOwner]
    exact controlRep
  have sourceGuard : SourceStateGuard memory allocator view code next nextSource 0 :=
    ⟨effect.invariant,SourceMode.of_control representedAfter afterGuard.2.1,
      by simpa only [nextSource,stackEq] using guard.stack.extend worldEffect,rfl⟩
  have step : Spec.OpenExecution.ChoiceTransition (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence source [.hostAction] nextSource := by
    rcases source with ⟨s,sourceControl,stack⟩
    dsimp only at sourceMode
    subst sourceControl
    have sameStore : s=Store.decodeStore view code native.store:=guard.storeEq
    subst s
    exact .action chosen
  exact WP.spec.ret ⟨next,rfl,.of_transition worldEffect sourceGuard step (by
    simp only [visibleSourceHistory,List.flatMap_cons,visibleSourceObservation,List.flatMap_nil,List.nil_append,List.append_nil]
    exact congrArg sourceHistory historyEq)⟩
end Exec.Theorems.OpenReentrantControl

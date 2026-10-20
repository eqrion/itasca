import Exec.Theorems.Host.Open.Source.Chosen.HostChosenTick
import Exec.Theorems.Host.Open.Completeness.ControlChoiceDeterminism
import Exec.Theorems.Host.Open.Source.State.TickLimits
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- An actual host instruction consumes the exact first transition of an
independently supplied terminating chosen source run. -/
theorem reference_host_prefix {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (occurrence : Nat)
    (code : Store.CodeInterpretation) (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (host : HostState) (hostSource : SourceHostState) (mode : native.mode=.host host)
    (sourceMode : source.mode=.host (.active hostSource))
    (represented : HostStateRepresents native.store.id hostSource host)
    (apiCompatible : SourceAPIChoicesCompatible memory allocator view choices)
    (publicationCompatible : SourcePublicationChoicesCompatible memory floats allocator view choices)
    {count events target}
    (reference : Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence count source events target)
    (completed : ∃result,target.mode=.completed result) :
    ∃nativeTicks reached afterCode afterSource afterRank consumed remaining beforeEvents moreEvents,
      ContinuingTrace (tick memory floats allocator select) nativeTicks native reached ∧
      ReentrantCallbacks.Effect view code native.store afterCode reached.store ∧
      SourceStateGuard memory allocator view afterCode reached afterSource afterRank ∧
      Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
        (sourceControlChoices choices) occurrence consumed source beforeEvents afterSource ∧
      Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
        (sourceControlChoices choices) (occurrence+consumed) remaining afterSource moreEvents target ∧
      count=consumed+remaining ∧ 0<consumed ∧ events=beforeEvents++moreEvents ∧
      sourceHistory reached.history=sourceHistory native.history++visibleSourceHistory beforeEvents ∧
      reached.store.limits=native.store.limits := by
  obtain ⟨out,actual,next,equal,single⟩:=WP.spec_imp_exists
    (source_host_chosen_single memory floats allocator correct allocation view laws select owner stop choices apiCompatible publicationCompatible occurrence
      code native source rank guard host hostSource mode sourceMode represented)
  subst out
  obtain ⟨afterCode,afterSource,afterRank,actualEvents,effect,fresh,step,observed⟩:=single
  cases reference with
  | nil =>
    obtain ⟨result,impossible⟩:=completed
    rw [sourceMode] at impossible
    cases impossible
  | @next position more first middle last headEvents tailEvents edge tail =>
    have outside : ∀f body expected,source.mode≠.wasm f body expected := by
      intro f body expected
      rw [sourceMode]
      simp
    obtain ⟨eventsEq,stateEq⟩:=control_choice_deterministic view (sourcePublication allocator view) select owner stop choices step edge outside
    cases stateEq
    cases eventsEq
    have front:=Spec.OpenExecution.ChoiceTrace.next step (.nil _ _)
    refine ⟨1,next,afterCode,afterSource,afterRank,1,more,actualEvents,tailEvents,
      .next actual (.nil _),effect,fresh,?_,tail,by omega,by omega,rfl,observed,?_⟩
    · simpa only [List.append_nil] using front
    · exact source_tick_limits memory floats allocator correct allocation view laws select code native source rank guard next actual
end Exec.Theorems.OpenReentrantControl

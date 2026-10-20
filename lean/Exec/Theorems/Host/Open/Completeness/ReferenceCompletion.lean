import Exec.Theorems.Host.Open.Completeness.ReferenceWasmPrefix
import Exec.Theorems.Host.Open.Source.State.TickControlCont
import Exec.Theorems.Host.Open.Source.Chosen.TickChosenDone
import Exec.Theorems.Host.Open.Completeness.ChosenSourceResources
import Exec.Theorems.Host.Open.Driver.StackTraces
import Exec.Theorems.Host.Open.Source.State.Finite
import Exec.Interp.Control.LoopTraceCompose
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

private theorem source_mode_zero_outside {M A : Type} {memory : runtime.platform.MemoryBuffer M}
    {allocator : runtime.platform.Alloc A} {view : M → Slice U8} {code store native source rank}
    (related : SourceMode memory allocator view code store native source rank) (zero : rank=0) :
    ∀f body expected,source≠.wasm f body expected := by
  cases related with
  | wasm signature world root results metadata typed => omega
  | finishing exec error root results signature metadata => cases zero
  | host | draft | preparing | returned => intros f body expected same;cases same

private theorem completed_trace {H : Type} {model : Spec.OpenExecution.HostModel H}
    {choices : Spec.OpenExecution.Choices H} {occurrence count first events last}
    (trace : Spec.OpenExecution.ChoiceTrace model choices occurrence count first events last)
    (completed : ∃result,first.mode=.completed result) : count=0 ∧ events=[] ∧ last=first := by
  cases trace with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | next step tail => obtain ⟨result,same⟩:=completed;cases step <;> cases same

private theorem completed_step_matches {M : Type} (view : M → Slice U8) (publication : SourcePublication)
    (select : Selector) (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) {occurrence source actualEvents actualCompleted count events target}
    (actual : Spec.OpenExecution.ChoiceTrace (sourceModel view publication select owner stop)
      (sourceControlChoices choices) occurrence 1 source actualEvents actualCompleted)
    (actualFinal : ∃result,actualCompleted.mode=.completed result)
    (outside : ∀f body expected,source.mode≠.wasm f body expected)
    (reference : Spec.OpenExecution.ChoiceTrace (sourceModel view publication select owner stop)
      (sourceControlChoices choices) occurrence count source events target)
    (completed : ∃result,target.mode=.completed result) : events=actualEvents ∧ target=actualCompleted := by
  cases actual with
  | next actualStep rest =>
    cases rest
    cases reference with
    | nil => obtain ⟨result,same⟩:=completed;cases actualStep <;> cases same
    | next step tail =>
      obtain ⟨eventsEq,stateEq⟩:=control_choice_deterministic view publication select owner stop choices actualStep step outside
      cases stateEq
      obtain ⟨zero,empty,lastEq⟩:=completed_trace tail actualFinal
      simp only [empty,List.append_nil,eventsEq,lastEq,and_self]

/-- A terminating independent chosen combined source run supplies a finite
actual native return with the same source outcome, decoded store and expanded
history. Capacities range over source prefixes at the original configured
limits; allocation and primitive/API/publication choices are separate leaves. -/
theorem chosen_source_complete {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (admissible : choices.Admissible view (sourcePublication allocator view))
    (numericChoice : choices.wasm.numeric=Spec.firstNumericChoice)
    (vectorChoice : choices.wasm.vector=Spec.firstVectorChoice)
    (growthCompatible : GrowthChoicesCompatible memory allocator view choices.wasm)
    (apiCompatible : SourceAPIChoicesCompatible memory allocator view choices)
    (publicationCompatible : SourcePublicationChoicesCompatible memory floats allocator view choices)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (occurrence : Nat) (code : Store.CodeInterpretation) (native : State M)
    (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (shape : native.Shape .invocation) (noOverflow : NoOverflowMode native.mode)
    (ownerEq : owner=native.store.id)
    (resources : ChosenSourceResources (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence native.store.limits source)
    {count events target}
    (reference : Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence count source events target)
    (completed : ∃result,target.mode=.completed result) :
    ∃ticks outcome afterCode,NormalTrace (tick memory floats allocator select) ticks native outcome ∧
      ReentrantCallbacks.Effect view code native.store afterCode outcome.store ∧
      SourceOutcome view afterCode outcome target ∧
      sourceHistory outcome.history=sourceHistory native.history++visibleSourceHistory events := by
  induction count using Nat.strong_induction_on generalizing rank occurrence code native source events target with
  | h count smaller =>
    induction rank using Nat.strong_induction_on generalizing occurrence code native source events target with
    | h rank stutter =>
      have advance {ticks reached afterCode afterSource afterRank consumed remaining beforeEvents moreEvents}
          (actual : ContinuingTrace (tick memory floats allocator select) ticks native reached)
          (effect : ReentrantCallbacks.Effect view code native.store afterCode reached.store)
          (fresh : SourceStateGuard memory allocator view afterCode reached afterSource afterRank)
          (front : Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
            (sourceControlChoices choices) occurrence consumed source beforeEvents afterSource)
          (tail : Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
            (sourceControlChoices choices) (occurrence+consumed) remaining afterSource moreEvents target)
          (total : count=consumed+remaining) (positive : 0<consumed)
          (eventEq : events=beforeEvents++moreEvents)
          (observed : sourceHistory reached.history=sourceHistory native.history++visibleSourceHistory beforeEvents)
          (limitsEq : reached.store.limits=native.store.limits) :
          ∃ticks outcome afterCode,NormalTrace (tick memory floats allocator select) ticks native outcome ∧
            ReentrantCallbacks.Effect view code native.store afterCode outcome.store ∧
            SourceOutcome view afterCode outcome target ∧
            sourceHistory outcome.history=sourceHistory native.history++visibleSourceHistory events := by
        have nextResources : ChosenSourceResources (sourceModel view (sourcePublication allocator view) select owner stop)
            (sourceControlChoices choices) (occurrence+consumed) reached.store.limits afterSource := by
          simpa only [limitsEq] using resources.future front
        have nextShape:=continuing_shape memory floats allocator select actual shape
        have nextSafe:=continuing_no_overflow memory floats allocator correct allocation view laws select actual code guard.native noOverflow
        have nextOwner : owner=reached.store.id:=ownerEq.trans effect.metadata.identity.symm
        obtain ⟨more,outcome,finalCode,returned,cumulative,matching,history⟩:=smaller remaining (by omega)
          (occurrence+consumed) afterCode reached afterSource afterRank fresh nextShape nextSafe nextOwner nextResources tail completed
        refine ⟨ticks+more,outcome,finalCode,actual.followed_by returned,effect.trans cumulative,matching,?_⟩
        rw [history,observed,eventEq,visibleSourceHistory_append,List.append_assoc]
      have control (zero : rank=0) :
          ∃ticks outcome afterCode,NormalTrace (tick memory floats allocator select) ticks native outcome ∧
            ReentrantCallbacks.Effect view code native.store afterCode outcome.store ∧
            SourceOutcome view afterCode outcome target ∧
            sourceHistory outcome.history=sourceHistory native.history++visibleSourceHistory events := by
        obtain ⟨out,actual,safe⟩:=WP.spec_imp_exists (tick_guard memory floats allocator correct allocation view laws select code native guard.native)
        cases out with
        | cont next =>
          obtain ⟨afterCode,nextSource,nextRank,actualEvents,effect,fresh,segment,observed⟩:=source_tick_control_cont
            memory floats allocator correct allocation view laws select owner stop choices admissible.wasm numericChoice vectorChoice
            growthCompatible apiCompatible publicationCompatible occurrence code native source rank zero guard shape noOverflow ownerEq
            resources.initial available next actual
          obtain ⟨consumed,remaining,beforeEvents,afterSource,moreEvents,represented,front,tail,total,positive,eventEq,visible⟩:=
            segment.match_reference memory allocator view select owner stop choices admissible reference guard.typed completed fresh
          exact advance (.next actual (.nil _)) effect represented front tail total positive eventEq
            (by rw [visible];exact observed)
            (source_tick_limits memory floats allocator correct allocation view laws select code native source rank guard next actual)
        | done outcome =>
          obtain ⟨actualCompleted,path,typed,matching,observed⟩:=source_tick_chosen_done memory floats allocator view select owner stop choices
            occurrence code native source rank guard shape outcome actual
          have actualFinal : ∃result,actualCompleted.mode=.completed result := by
            cases outcome with
            | host answer history => cases matching
            | invocation answer history => exact ⟨_,matching.1⟩
          obtain ⟨eventEq,stateEq⟩:=completed_step_matches view (sourcePublication allocator view) select owner stop choices path actualFinal
            (source_mode_zero_outside guard.mode zero) reference completed
          cases stateEq
          have storeEq:=guarded_done_store memory floats allocator select view code native guard.native shape outcome actual
          have effect : ReentrantCallbacks.Effect view code native.store code outcome.store := by
            rw [storeEq]
            exact .refl guard.invariant
          refine ⟨0,outcome,code,.done actual,effect,matching,?_⟩
          rw [eventEq]
          cases outcome <;> exact sourceHistory_visible_append observed
      rcases native with ⟨store,mode,stack,history⟩
      rcases source with ⟨sourceStore,sourceMode,sourceStack⟩
      rcases guard with ⟨held,related,stackGuard,storeEq⟩
      have guard:=SourceStateGuard.mk held related stackGuard storeEq
      cases related with
      | host | draft | preparing | returned => exact control rfl
      | wasm signature world root results metadata typed =>
        obtain ⟨nativeTicks,reached,afterCode,afterSource,afterRank,consumed,remaining,beforeEvents,moreEvents,
          actual,effect,fresh,front,tail,total,positive,eventEq,observed,limitsEq⟩:=reference_wasm_prefix memory floats allocator correct allocation view laws
            select owner stop choices admissible numericChoice vectorChoice growthCompatible occurrence world.code _ _ _ guard
              (Abs.decode world.machine.source).1.2 (Abs.decode world.machine.source).2 (.mk_list (signature.results.val.map sourceType))
              rfl ownerEq resources available reference completed
        exact advance actual effect fresh front tail total positive eventEq observed limitsEq
      | finishing exec error root results signature metadata =>
        obtain ⟨actual,fresh,observed⟩:=source_error_finish memory floats allocator view select code _ _ guard exec error root results rfl rfl
        have nextShape:=tick_shape memory floats allocator select _ .invocation shape _ actual
        have nextSafe:=tick_no_overflow memory floats allocator correct allocation view laws select code _ held noOverflow _ actual
        obtain ⟨ticks,outcome,afterCode,returned,effect,matching,historyEq⟩:=stutter 0 (by omega)
          occurrence code _ _ fresh nextShape nextSafe ownerEq resources reference completed
        exact ⟨ticks+1,outcome,afterCode,.next actual returned,effect,matching,by simpa only [observed] using historyEq⟩
end Exec.Theorems.OpenReentrantControl

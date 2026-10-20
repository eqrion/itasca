import Exec.Theorems.Host.Open.Source.Chosen.TickChosenCont
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall
theorem source_tick_control_cont {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (admissible : choices.wasm.Admissible)
    (numericChoice : choices.wasm.numeric=Spec.firstNumericChoice)
    (vectorChoice : choices.wasm.vector=Spec.firstVectorChoice)
    (growthCompatible : GrowthChoicesCompatible memory allocator view choices.wasm)
    (apiCompatible : SourceAPIChoicesCompatible memory allocator view choices)
    (publicationCompatible : SourcePublicationChoicesCompatible memory floats allocator view choices) (occurrence : Nat)
    (code : Store.CodeInterpretation) (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat) (zero : rank=0)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (shape : native.Shape .invocation) (noOverflow : NoOverflowMode native.mode)
    (ownerEq : owner=native.store.id) (resources : SourceTickResources native.store.limits source)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (next : State M) (actual : tick memory floats allocator select native=.ok (.cont next)) :
    SourceControlAdvance memory allocator view select owner stop choices occurrence code native source next := by
  rcases native with ⟨store,mode,stack,history⟩
  rcases source with ⟨sourceStore,sourceMode,sourceStack⟩
  rcases guard with ⟨held,related,stackGuard,storeEq⟩
  dsimp only at storeEq
  have guard:=SourceStateGuard.mk held related stackGuard storeEq
  cases related with
  | host raw hostSource represented=>
    have post:=source_host_chosen_single memory floats allocator correct allocation view laws select owner stop choices apiCompatible publicationCompatible occurrence code _ _ _ guard
      raw hostSource rfl rfl represented
    rw [actual,WP.spec_ok] at post
    obtain ⟨rawNext,equal,afterCode,nextSource,nextRank,events,effect,fresh,step,history⟩:=post
    cases equal
    exact ⟨afterCode,nextSource,nextRank,events,effect,fresh,.single (by intros; simp) step,history⟩
  | draft status values owned=>
    simp only [State.Shape,Mode.kind] at shape
    cases shape with
    | wasm ready address base root results under=>
      cases stackGuard with
      | cons frame tail=>
        cases frame with
        | wasm ready address base root results suspended saved=>
          have post:=source_draft_control_tick memory floats allocator view select owner stop code choices occurrence _ _ guard
            status values owned noOverflow rfl rfl ready address base root results suspended _ _ rfl rfl saved tail
          rw [actual,WP.spec_ok] at post
          obtain ⟨rawNext,equal,advance⟩:=post
          cases equal
          exact advance
  | preparing exec address signature args results phase metadata ready=>
    obtain ⟨rawNext,nextSource,nextRank,count,events,computed,fresh,positive,path,observed,segment⟩:=source_preparing_chosen memory floats allocator view
      select owner stop code choices admissible vectorChoice occurrence _ _ guard exec address signature args results phase metadata ready rfl rfl ownerEq available
        (by simpa only [SourceTickResources,signatureWords,Store.decodeFuncType] using resources.1)
        resources.2.1 (by simpa only [storeEq] using resources.2.2)
    have storeSame:=ready.tick_store memory floats rfl computed
    have effect : ReentrantCallbacks.Effect view code store code rawNext.store:=by
      rw [storeSame]
      exact .refl held
    have equal : rawNext=next:=by simpa only [Result.ok.injEq,ControlFlow.cont.injEq] using computed.symm.trans actual
    subst next
    exact ⟨code,nextSource,nextRank,events,effect,fresh,segment,observed⟩
  | wasm signature world root results metadata typed=>omega
  | finishing exec error root results signature metadata=>cases zero
  | returned answer sameStore issued=>
    simp only [State.Shape,Mode.kind] at shape
    cases shape with
    | nil=>
      simp only [tick,Result.ok.injEq] at actual
      cases actual
    | host host nextPC under=>
      cases stackGuard with
      | cons frame tail=>
        cases frame with
        | host host nextPC caller represented=>
          obtain ⟨rawNext,nextSource,computed,fresh,step,historyEq⟩:=source_invoke_return memory floats allocator view select owner stop code
            _ _ guard answer rfl rfl host caller nextPC _ _ rfl rfl represented tail
          have same:=computed
          simp only [tick,bind_ok,Result.ok.injEq,ControlFlow.cont.injEq] at same
          have storeSame : rawNext.store=store:=by
            cases result : answer.1 <;> simp only [result,Result.ok.injEq,ControlFlow.cont.injEq] at same
            all_goals exact (congrArg State.store same).symm
          have effect : ReentrantCallbacks.Effect view code store code rawNext.store:=by
            rw [storeSame]
            exact .refl held
          have equal : rawNext=next:=by simpa only [Result.ok.injEq,ControlFlow.cont.injEq] using computed.symm.trans actual
          subst next
          have chosenStep:=choose_control_transition choices occurrence step
            (by intro f body expected impossible;cases impossible) (by simp)
          exact ⟨code,nextSource,0,_,effect,fresh,.single (by intros; simp) chosenStep,sourceHistory_visible_append historyEq⟩
end Exec.Theorems.OpenReentrantControl

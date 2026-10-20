import Exec.Theorems.Host.Open.Source.Chosen.HostChosenTick
import Exec.Theorems.Host.Open.Source.Chosen.WasmChosenTick
import Exec.Theorems.Host.Open.Source.Chosen.DraftChosenTick
import Exec.Theorems.Host.Open.Source.Chosen.PreparingChosen
import Exec.Theorems.Host.Open.Source.Wasm.Preparing
import Exec.Theorems.Host.Open.Source.Chosen.ControlChoiceLifting
import Exec.Theorems.Host.Open.Source.State.ErrorFinish
import Exec.Theorems.Host.Open.Source.Wasm.InvokeReturn
import Exec.Theorems.Host.Open.Source.Wasm.InvokeExit
import Exec.Theorems.Host.Open.Driver.DriverStackSafety
import Exec.Theorems.Host.Open.Driver.ReentrantStack
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Independent source storage requirements at one combined state. The Wasm
condition ranges over source machine representations of this configuration;
root requirements use canonical source function capacities, not bytecode slots. -/
def SourceTickResources (limits : runtime.store.StoreLimits) (source : Spec.OpenExecution.State SourceControl) : Prop :=
  match source.mode with
  | .wasm f body _ => ∀candidate : Abs.AState,Abs.decode candidate=⟨⟨source.store,f⟩,body⟩ →
      SourceWorldResources limits.max_values.val limits.max_frames.val candidate
  | .invokeRequest address _ params results =>
      max (Code.slots params) (Code.slots results)≤limits.max_values.val ∧ 0<limits.max_frames.val ∧
      ∀words,SourceCanonicalFunctionCapacity source.store address words → words≤limits.max_values.val
  | _ => True

theorem source_tick_chosen_cont {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
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
    (code : Store.CodeInterpretation) (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (shape : native.Shape .invocation) (noOverflow : NoOverflowMode native.mode)
    (ownerEq : owner=native.store.id) (resources : SourceTickResources native.store.limits source)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (next : State M) (actual : tick memory floats allocator select native=.ok (.cont next)) :
    ChosenSourceAdvance memory allocator view select owner stop choices occurrence code native source rank next := by
  rcases native with ⟨store,mode,stack,history⟩
  rcases source with ⟨sourceStore,sourceMode,sourceStack⟩
  rcases guard with ⟨held,related,stackGuard,storeEq⟩
  dsimp only at storeEq
  have guard:=SourceStateGuard.mk held related stackGuard storeEq
  cases related with
  | host raw hostSource represented=>
    have post:=source_host_chosen_tick memory floats allocator correct allocation view laws select owner stop choices apiCompatible publicationCompatible occurrence code _ _ _ guard
      raw hostSource rfl rfl represented
    rw [actual,WP.spec_ok] at post
    obtain ⟨rawNext,equal,advance⟩:=post
    cases equal
    exact advance
  | draft status values owned=>
    simp only [State.Shape,Mode.kind] at shape
    cases shape with
    | wasm ready address base root results under=>
      cases stackGuard with
      | cons frame tail=>
        cases frame with
        | wasm ready address base root results suspended saved=>
          have post:=source_draft_chosen_tick memory floats allocator view select owner stop code choices occurrence _ _ guard
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
    exact ⟨code,nextSource,nextRank,count,events,effect,fresh,path,(fun zero=>by omega),observed⟩
  | wasm signature world root results metadata typed=>
    have decodedStore : (Abs.decode world.machine.source).1.1=sourceStore :=
      world.machine.invariant.storeEq.trans storeEq.symm
    have decodedEq : Abs.decode world.machine.source=⟨⟨sourceStore,(Abs.decode world.machine.source).1.2⟩,(Abs.decode world.machine.source).2⟩ := by
      generalize same : Abs.decode world.machine.source=configuration at decodedStore ⊢
      rcases configuration with ⟨⟨s,f⟩,body⟩
      dsimp only at decodedStore
      rw [decodedStore]
    have adequate:=resources world.machine.source decodedEq
    have post:=source_wasm_chosen_tick memory floats allocator correct allocation view laws select owner stop
      choices admissible numericChoice vectorChoice growthCompatible occurrence signature world _ _ guard rfl
      root results rfl rfl metadata typed ownerEq adequate available
    rw [actual,WP.spec_ok] at post
    obtain ⟨rawNext,equal,advance⟩:=post
    cases equal
    exact advance
  | finishing exec error root results signature metadata=>
    obtain ⟨computed,fresh,historyEq⟩:=source_error_finish memory floats allocator view select code _ _ guard exec error root results rfl rfl
    have equal := computed.symm.trans actual
    simp only [Result.ok.injEq,ControlFlow.cont.injEq] at equal
    subst next
    exact ⟨code,_,0,0,[],.refl held,fresh,.nil _ _,(by omega),by simp only [sourceHistory,visibleSourceHistory,List.flatMap_nil,List.append_nil]⟩
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
          exact .of_transition effect fresh chosenStep (sourceHistory_visible_append historyEq)
end Exec.Theorems.OpenReentrantControl

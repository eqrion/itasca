import Exec.Theorems.Host.Open.Source.Wasm.WasmStepGuarded
import Exec.Theorems.Host.Open.Driver.ActiveWasmTrace
import Exec.Theorems.Host.Open.Completeness.ChosenSourceResources
import Exec.Theorems.Host.Open.Source.State.TickLimits
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- A finite actual active-Wasm segment reaches the exact next source boundary.
Completed values include their real readback tick. All earlier dispatches retain
one silent chosen source prefix, the reached world and committed effects. -/
theorem active_wasm_source_arrival {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (admissible : choices.wasm.Admissible)
    (numericChoice : choices.wasm.numeric=Spec.firstNumericChoice) (vectorChoice : choices.wasm.vector=Spec.firstVectorChoice)
    (compatible : GrowthChoicesCompatible memory allocator view choices.wasm)
    {ticks first last} (trace : ActiveWasmTrace memory floats allocator select ticks first last)
    (occurrence : Nat) (code : Store.CodeInterpretation) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code first source rank)
    (f : frame) (body : List admininstr) (expected : resulttype) (sourceMode : source.mode=.wasm f body expected)
    (ownerEq : owner=first.store.id)
    (resources : ChosenSourceResources (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence first.store.limits source)
    (available : Platform.AllocationAvailable allocator (2*Usize.max)) (boundary : NativeWasmBoundary last) :
    ∃nativeTicks reached afterCode afterSource afterRank quietCount endpoint events,
      ContinuingTrace (tick memory floats allocator select) nativeTicks first reached ∧
      ReentrantCallbacks.Effect view code first.store afterCode reached.store ∧
      SourceStateGuard memory allocator view afterCode reached afterSource afterRank ∧
      Spec.ChosenStepsN choices.wasm occurrence quietCount ⟨⟨source.store,f⟩,body⟩ [] endpoint ∧
      WasmBoundaryArrival select owner expected source.stack endpoint events afterSource ∧
      sourceHistory reached.history=sourceHistory first.history++visibleSourceHistory events ∧ reached.store.limits=first.store.limits := by
  induction trace generalizing occurrence code source rank f body expected with
  | nil current =>
    rcases current with ⟨store,mode,stack,history⟩
    rcases source with ⟨sourceStore,sourceModeRaw,sourceStack⟩
    rcases guard with ⟨held,related,stackGuard,storeEq⟩
    dsimp only at sourceMode storeEq
    have guard:=SourceStateGuard.mk held related stackGuard storeEq
    cases related with
    | host raw hostSource represented => cases sourceMode
    | draft status values owned => cases sourceMode
    | preparing exec address signature args results phase metadata ready => cases sourceMode
    | finishing exec error root results signature metadata => cases sourceMode
    | returned answer sameStore issued => cases sourceMode
    | wasm signature world root results metadata typed =>
      cases sourceMode
      have notActive : ¬0<world.machine.exec.frames.length := fun positive=>boundary ⟨positive,rfl⟩
      have empty : world.machine.exec.frames.val=[] := by
        apply List.length_eq_zero_iff.mp
        change world.machine.exec.frames.length=0
        omega
      obtain ⟨out,computed,next,nextSource,same,fresh,path,historyEq,sourceEq,storeSame⟩:=WP.spec_imp_exists
        (source_wasm_chosen_finished memory floats allocator allocation view select owner stop choices occurrence signature world
          _ _ _ guard rfl root results rfl rfl metadata empty available)
      subst out
      have effect : ReentrantCallbacks.Effect view world.code world.machine.store world.code next.store := by
        rw [storeSame]
        exact .refl held
      have cfgTyped : Config_ok ⟨⟨sourceStore,(Abs.decode world.machine.source).1.2⟩,(Abs.decode world.machine.source).2⟩
          (.mk_list (signature.results.val.map sourceType)) := guard.typed.2.1
      have wf : wf_config ⟨⟨sourceStore,(Abs.decode world.machine.source).1.2⟩,(Abs.decode world.machine.source).2⟩ := by
        cases cfgTyped
        assumption
      obtain ⟨sourceEmpty,typedValues,words⟩:=world.machine.invariant.finished empty
      have cfgEq : (⟨⟨sourceStore,(Abs.decode world.machine.source).1.2⟩,(Abs.decode world.machine.source).2⟩ : config)=
          ⟨⟨sourceStore,world.machine.source.ambient⟩,vals world.machine.source.results⟩ := by
        simp only [Abs.decode,sourceEmpty,Abs.decodeFrames]
      have arrival : WasmBoundaryArrival select owner (.mk_list (signature.results.val.map sourceType)) sourceStack
          ⟨⟨sourceStore,(Abs.decode world.machine.source).1.2⟩,(Abs.decode world.machine.source).2⟩ [] nextSource := by
        rw [cfgEq,sourceEq]
        exact .values _ _ _
      exact ⟨1,next,world.code,nextSource,0,0,_,[],.next computed (.nil _),effect,fresh,.refl occurrence wf,arrival,
        by simp only [historyEq,visibleSourceHistory,List.flatMap_nil,List.append_nil],congrArg runtime.store.Store.limits storeSame⟩
  | @next ticks current after last exec root results nativeMode active actual tail ih =>
    obtain ⟨out,computed,rawNext,afterCode,nextSource,nextRank,same,effect,fresh,step⟩:=WP.spec_imp_exists
      (source_wasm_step_guarded memory floats allocator correct allocation view laws select owner stop choices admissible
        numericChoice vectorChoice compatible occurrence code current source rank guard f body expected sourceMode ownerEq resources.initial available)
    subst out
    have equal : rawNext=after := by simpa only [Result.ok.injEq,ControlFlow.cont.injEq] using computed.symm.trans actual
    subst rawNext
    have sameLimits:=source_tick_limits memory floats allocator correct allocation view laws select code current source rank guard after actual
    cases step with
    | @wasm quietCount afterConfig afterSource afterHistory quietSteps sourceEq historyEq =>
      rcases afterConfig with ⟨⟨s,g⟩,moreBody⟩
      subst nextSource
      have canonical:=Spec.OpenExecution.State.wasm_eq source (config.mk_config (state.mk_state source.store f) body) expected rfl sourceMode
      have sourcePath : Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
          (sourceControlChoices choices) occurrence quietCount source (List.replicate quietCount .wasm)
          ⟨s,.wasm g moreBody expected,source.stack⟩ := by
        rw [canonical]
        exact Spec.OpenExecution.ChoiceTrace.wasmCounted (sourceModel view (sourcePublication allocator view) select owner stop)
          (sourceControlChoices choices) quietSteps expected source.stack
      have nextResources : ChosenSourceResources (sourceModel view (sourcePublication allocator view) select owner stop)
          (sourceControlChoices choices) (occurrence+quietCount) after.store.limits ⟨s,.wasm g moreBody expected,source.stack⟩ := by
        simpa only [sameLimits] using resources.future sourcePath
      have nextOwner : owner=after.store.id := ownerEq.trans effect.metadata.identity.symm
      obtain ⟨nativeTicks,reached,finalCode,finalSource,finalRank,more,endpoint,events,nativePath,cumulative,finalGuard,sourceTail,arrival,observed,limitsAtEnd⟩:=
        ih (occurrence+quietCount) afterCode _ nextRank fresh g moreBody expected rfl nextOwner nextResources boundary
      refine ⟨nativeTicks+1,reached,finalCode,finalSource,finalRank,quietCount+more,endpoint,events,
        .next actual nativePath,effect.trans cumulative,finalGuard,?_,arrival,?_,limitsAtEnd.trans sameLimits⟩
      · simpa only [List.nil_append] using quietSteps.trans sourceTail
      · simpa only [historyEq] using observed
    | @arrive quietCount afterConfig events afterSource afterHistory quietSteps arrival observed =>
      cases tail with
      | nil => exact ⟨1,after,afterCode,nextSource,nextRank,quietCount,afterConfig,events,
          .next actual (.nil _),effect,fresh,quietSteps,arrival,observed,sameLimits⟩
      | next nextMode nextActive nextActual rest =>
        obtain ⟨nextFrame,nextBody,nextExpected,sourceAfterMode⟩:=fresh.mode.ok_wasm_source _ _ _ nextMode
        exact False.elim (arrival.not_wasm nextFrame nextBody nextExpected sourceAfterMode)
end Exec.Theorems.OpenReentrantControl

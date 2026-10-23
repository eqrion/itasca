import Exec.Spec.Open.ExecutionCounted
import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Completeness.ChosenQuietWorld
import Exec.Theorems.Host.Open.Source.Chosen.ChosenConcreteStep
import Exec.Theorems.Host.Open.Source.Control.Publication
import Exec.Theorems.Host.Open.Source.Chosen.ControlChoices
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- An ordinary successful native Wasm dispatch advances its particular source
machine, preserving the whole saved stack and decreasing rank on zero steps. -/
theorem source_wasm_chosen_success {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (admissible : choices.wasm.Admissible)
    (numericChoice : choices.wasm.numeric=Spec.firstNumericChoice)
    (vectorChoice : choices.wasm.vector=Spec.firstVectorChoice)
    (compatible : GrowthChoicesCompatible memory allocator view choices.wasm) (occurrence : Nat)
    (signature : Itasca.types.FuncType)
    (world : EventfulWorld M Unit view (signature.results.val.map sourceType))
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (guard : SourceStateGuard memory allocator view world.code native source
      (2+dispatchMeasure world.machine.pending U32.max world.machine.pc world.machine.source))
    (nativeStore : native.store=world.machine.store) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (mode : native.mode=.wasm world.machine.exec (.Ok ()) root results)
    (sourceMode : source.mode=.wasm (Abs.decode world.machine.source).1.2 (Abs.decode world.machine.source).2
      (.mk_list (signature.results.val.map sourceType)))
    (metadata : RootMetadata world.machine.store root signature)
    (typed : Config_ok (Abs.decode world.machine.source) (.mk_list (signature.results.val.map sourceType)))
    (active : 0<world.machine.exec.frames.length) (out : Answer M Unit)
    (prepared : prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform=.ok (.done out))
    (successful : out.1=.Ok ()) :
    ∃next afterCode nextSource afterRank count events,tick memory floats allocator select native=.ok (.cont next) ∧
      ReentrantCallbacks.Effect view world.code native.store afterCode next.store ∧
      SourceStateGuard memory allocator view afterCode next nextSource afterRank ∧
      Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence count source events nextSource ∧
      (count=0 → afterRank<2+dispatchMeasure world.machine.pending U32.max world.machine.pc world.machine.source) ∧
      next.history=native.history ∧ visibleSourceHistory events=[] ∧
      ∃quietCount afterConfig,
        Spec.ChosenStepsN choices.wasm occurrence quietCount (Abs.decode world.machine.source) [] afterConfig ∧
        nextSource=⟨afterConfig.1.1,.wasm afterConfig.1.2 afterConfig.2
          (.mk_list (signature.results.val.map sourceType)),source.stack⟩ := by
  have held : ExecutableInv view world.code world.machine.store:=by simpa only [nativeStore] using guard.invariant
  have post:=chosen_quiet_world admissible numericChoice vectorChoice occurrence memory floats allocator correct allocation view laws compatible world held active typed out prepared
  simp only [ChosenQuietWorldResult,successful] at post
  obtain ⟨nextWorld,fresh,same,simulation,effect,ambient⟩ := post
  obtain ⟨nextTyped,count,events,trace,decrease,visible⟩ := concrete_chosen_source_trace
    (sourceModel view (sourcePublication allocator view) select owner stop) (sourceControlChoices choices) admissible occurrence simulation
    (.mk_list (signature.results.val.map sourceType)) source.stack typed
  let next : State M:=⟨nextWorld.machine.store,.wasm nextWorld.machine.exec (.Ok ()) root results,native.stack,native.history⟩
  let nextSource : Spec.OpenExecution.State SourceControl:=⟨Store.decodeStore view nextWorld.code nextWorld.machine.store,
    .wasm (Abs.decode nextWorld.machine.source).1.2 (Abs.decode nextWorld.machine.source).2
      (.mk_list (signature.results.val.map sourceType)),source.stack⟩
  have effectActual : ReentrantCallbacks.Effect view world.code native.store nextWorld.code next.store := by
    simpa only [nativeStore,next] using effect
  have nextGuard : SourceStateGuard memory allocator view nextWorld.code next nextSource
      (2+dispatchMeasure nextWorld.machine.pending U32.max nextWorld.machine.pc nextWorld.machine.source) :=
    ⟨fresh,.wasm signature nextWorld root results (metadata.prefix effect.metadata) nextTyped,
      guard.stack.extend effectActual,rfl⟩
  have oldStore : source.store=(Abs.decode world.machine.source).1.1 := by
    change source.store=world.machine.source.store
    exact guard.storeEq.trans ((congrArg (Store.decodeStore view world.code) nativeStore).trans world.machine.invariant.storeEq.symm)
  have oldEq:=Spec.OpenExecution.State.wasm_eq source (Abs.decode world.machine.source) (.mk_list (signature.results.val.map sourceType)) oldStore sourceMode
  have nextEq : nextSource=⟨(Abs.decode nextWorld.machine.source).1.1,
      .wasm (Abs.decode nextWorld.machine.source).1.2 (Abs.decode nextWorld.machine.source).2
        (.mk_list (signature.results.val.map sourceType)),source.stack⟩ := by
    change nextSource={nextSource with store:=nextWorld.machine.source.store}
    rw [nextWorld.machine.invariant.storeEq]
  have projected : Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence count source events nextSource := by
    rw [oldEq,nextEq]
    simpa only [] using trace
  have quiet : ∃quietCount,Spec.ChosenStepsN choices.wasm occurrence quietCount
      (Abs.decode world.machine.source) [] (Abs.decode nextWorld.machine.source) := by
    rcases simulation with ⟨same,smaller⟩ | ⟨quietCount,positive,counted⟩
    · refine ⟨0,?_⟩
      rw [←same]
      have wf : wf_config (Abs.decode world.machine.source) := by cases typed;assumption
      exact .refl occurrence wf
    · exact ⟨quietCount,counted⟩
  obtain ⟨quietCount,counted⟩:=quiet
  clear oldEq
  have token : world.machine.platform=():=Subsingleton.elim _ _
  have preparedUnit:=prepared
  rw [token] at preparedUnit
  have frames : world.machine.exec.frames.len>0#usize:=by scalar_tac
  have loopPrepared : prepareLoop memory (inert memory) floats allocator (world.machine.exec,native.store,(),.Ok ())=.ok (.executing (.done out)) := by
    simp only [prepareLoop,frames,ite_true,core.result.Result.is_ok,bind_ok,nativeStore,preparedUnit]
  refine ⟨next,nextWorld.code,nextSource,_,count,events,?_,effectActual,nextGuard,projected,?_,rfl,visible,quietCount,Abs.decode nextWorld.machine.source,counted,nextEq⟩
  · simp only [tick,mode,loopPrepared,bind_ok,acceptCall,same,next]
  · intro zero
    have smaller:=decrease zero
    omega
end Exec.Theorems.OpenReentrantControl

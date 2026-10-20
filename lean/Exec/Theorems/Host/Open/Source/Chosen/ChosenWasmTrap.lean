import Exec.Spec.Open.ExecutionCounted
import Exec.Spec.Open.ExecutionChosenCounted
import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Completeness.ChosenQuietWorld
import Exec.Theorems.Host.Open.Source.Chosen.ControlChoices
import Exec.Theorems.Host.Open.Source.State.ActiveTick
import Exec.Theorems.Host.Open.Source.Control.Publication
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

theorem trap_chosen_source_trace {H : Type} (model : Spec.OpenExecution.HostModel H)
    (choices : Spec.OpenExecution.Choices H) (occurrence : Nat)
    (before : config) (after : store) (ambient : frame) (trap : runtime.Trap)
    (values : alloc.vec.Vec runtime.Value) (expected : resulttype)
    (stack : List (Spec.OpenExecution.Continuation H))
    (prefixSteps : ChosenEventfulInvocationError choices.wasm occurrence before [] after ambient (.Trap trap)) :
    ∃count events,0<count ∧ Spec.OpenExecution.ChoiceTrace model choices occurrence count
      ⟨before.1.1,.wasm before.1.2 before.2 expected,stack⟩ events
      ⟨after,.invokeReturn (sourceInvocationResult (.Err (.Trap trap)) values),stack⟩ ∧ visibleSourceHistory events=[] := by
  obtain ⟨count,steps⟩:=prefixSteps
  have trace:=Spec.OpenExecution.ChoiceTrace.wasmCounted model choices steps expected stack
  refine ⟨count+1,List.replicate count .wasm,by omega,?_,visibleSourceHistory_wasm count⟩
  simpa only [sourceInvocationResult,List.append_nil] using trace.trans
    (Spec.OpenExecution.ChoiceTrace.next (.trap) (.nil _ _))

/-- A failed native Wasm dispatch retains its actual cause and committed world
and reaches the matching source trap under the selected primitive policy. -/
theorem source_wasm_chosen_trap {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (admissible : choices.wasm.Admissible)
    (numericChoice : choices.wasm.numeric=Spec.firstNumericChoice)
    (vectorChoice : choices.wasm.vector=Spec.firstVectorChoice)
    (compatible : GrowthChoicesCompatible memory allocator view choices.wasm) (occurrence : Nat)
    (signature : Itasca.types.FuncType)
    (world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view (signature.results.val.map sourceType))
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (guard : SourceStateGuard memory allocator view world.code native source
      (2+dispatchMeasure world.machine.pending U32.max world.machine.pc world.machine.source))
    (nativeStore : native.store=world.machine.store) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (mode : native.mode=.wasm world.machine.exec (.Ok ()) root results)
    (sourceMode : source.mode=.wasm (Abs.decode world.machine.source).1.2 (Abs.decode world.machine.source).2
      (.mk_list (signature.results.val.map sourceType)))
    (metadata : RootMetadata world.machine.store root signature)
    (typed : Config_ok (Abs.decode world.machine.source) (.mk_list (signature.results.val.map sourceType)))
    (active : 0<world.machine.exec.frames.length) (out : Answer M Unit) (trap : runtime.Trap)
    (prepared : prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform=.ok (.done out))
    (failed : out.1=.Err (.Trap trap))
 :
    ∃next afterCode nextSource count events,tick memory floats allocator select native=.ok (.cont next) ∧
      ReentrantCallbacks.Effect view world.code native.store afterCode next.store ∧
      SourceStateGuard memory allocator view afterCode next nextSource 1 ∧ 0<count ∧
      Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence count source events nextSource ∧
      EventfulDispatchCause memory (inert memory) floats allocator world.machine out (.Trap trap) ∧ next.history=native.history ∧ visibleSourceHistory events=[] ∧
      ∃quietCount,Spec.ChosenStepsN choices.wasm occurrence quietCount (Abs.decode world.machine.source) []
        ⟨⟨nextSource.store,world.machine.source.ambient⟩,[.TRAP]⟩ ∧ nextSource=⟨nextSource.store,.invokeReturn .trapped,source.stack⟩ := by
  have held : ExecutableInv view world.code world.machine.store:=by simpa only [nativeStore] using guard.invariant
  have post:=chosen_quiet_world admissible numericChoice vectorChoice occurrence memory floats allocator correct allocation view laws compatible world held active typed out prepared
  simp only [ChosenQuietWorldResult,failed] at post
  obtain ⟨afterCode,effect,path,cause⟩ := post
  obtain ⟨count,events,positive,trace,visible⟩ := trap_chosen_source_trace
    (sourceModel view (sourcePublication allocator view) select owner stop) (sourceControlChoices choices) occurrence (Abs.decode world.machine.source)
    (Store.decodeStore view afterCode out.2.2.1) world.machine.source.ambient trap results
    (.mk_list (signature.results.val.map sourceType)) source.stack path
  let next : State M:=⟨out.2.2.1,.wasm out.2.1 (.Err (.Trap trap)) root results,native.stack,native.history⟩
  let nextSource : Spec.OpenExecution.State SourceControl:=⟨Store.decodeStore view afterCode out.2.2.1,
    .invokeReturn (sourceInvocationResult (.Err (.Trap trap)) results),source.stack⟩
  have effectActual : ReentrantCallbacks.Effect view world.code native.store afterCode next.store := by
    simpa only [nativeStore,next] using effect
  have nextGuard : SourceStateGuard memory allocator view afterCode next nextSource 1 :=
    ⟨effect.invariant,.finishing out.2.1 (.Trap trap) root results signature (metadata.prefix effect.metadata),guard.stack.extend effectActual,rfl⟩
  have oldStore : source.store=(Abs.decode world.machine.source).1.1 := by
    change source.store=world.machine.source.store
    exact guard.storeEq.trans ((congrArg (Store.decodeStore view world.code) nativeStore).trans world.machine.invariant.storeEq.symm)
  have oldEq:=Spec.OpenExecution.State.wasm_eq source (Abs.decode world.machine.source) (.mk_list (signature.results.val.map sourceType)) oldStore sourceMode
  have projected : Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence count source events nextSource := by
    rw [oldEq]
    exact trace
  have token : world.machine.platform=():=Subsingleton.elim _ _
  have preparedUnit:=prepared
  rw [token,←nativeStore] at preparedUnit
  obtain ⟨quietCount,quiet⟩:=path
  refine ⟨next,afterCode,nextSource,count,events,?_,effectActual,nextGuard,positive,projected,cause,rfl,visible,
    quietCount,quiet,rfl⟩
  rw [wasm_active_tick memory floats allocator select native world.machine.exec root results mode active (.done out) preparedUnit]
  simp only [acceptCall,failed,next]
end Exec.Theorems.OpenReentrantControl

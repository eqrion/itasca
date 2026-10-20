import Exec.Spec.Open.ExecutionCounted
import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Completeness.CompletedSourceWorld
import Exec.Theorems.Host.Open.Source.State.ErrorTrace
import Exec.Theorems.Host.Open.Source.State.ActiveTick
import Exec.Theorems.Host.Open.Source.Control.Publication
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- A failed native Wasm dispatch retains its actual cause and committed world
and reaches the matching source trap or independently permitted cutoff. -/
theorem source_wasm_error {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
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
    (active : 0<world.machine.exec.frames.length) (out : Answer M Unit) (error : runtime.ExecError)
    (prepared : prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform=.ok (.done out))
    (failed : out.1=.Err error)
    (allowed : ∀reason,sourceInvocationResult (.Err error) results=.stopped reason → ∀configuration,stop reason configuration) :
    ∃next afterCode nextSource count events,tick memory floats allocator select native=.ok (.cont next) ∧
      ReentrantCallbacks.Effect view world.code native.store afterCode next.store ∧
      SourceStateGuard memory allocator view afterCode next nextSource 1 ∧ 0<count ∧
      Spec.OpenExecution.Trace (sourceModel view (sourcePublication allocator view) select owner stop) count source events nextSource ∧
      EventfulDispatchCause memory (inert memory) floats allocator world.machine out error ∧ next.history=native.history ∧ visibleSourceHistory events=[] := by
  have held : ExecutableInv view world.code world.machine.store:=by simpa only [nativeStore] using guard.invariant
  have post:=completed_source_world memory floats allocator correct allocation view laws world held active typed out prepared
  simp only [QuietWorldResult,failed] at post
  obtain ⟨afterCode,effect,path,cause⟩ := post
  obtain ⟨count,events,positive,trace,visible⟩ := error_source_trace
    (sourceModel view (sourcePublication allocator view) select owner stop) (Abs.decode world.machine.source)
    (Store.decodeStore view afterCode out.2.2.1) world.machine.source.ambient error results
    (.mk_list (signature.results.val.map sourceType)) source.stack path allowed
  let next : State M:=⟨out.2.2.1,.wasm out.2.1 (.Err error) root results,native.stack,native.history⟩
  let nextSource : Spec.OpenExecution.State SourceControl:=⟨Store.decodeStore view afterCode out.2.2.1,
    .invokeReturn (sourceInvocationResult (.Err error) results),source.stack⟩
  have effectActual : ReentrantCallbacks.Effect view world.code native.store afterCode next.store := by
    simpa only [nativeStore,next] using effect
  have nextGuard : SourceStateGuard memory allocator view afterCode next nextSource 1 :=
    ⟨effect.invariant,.finishing out.2.1 error root results signature (metadata.prefix effect.metadata),guard.stack.extend effectActual,rfl⟩
  have oldStore : source.store=(Abs.decode world.machine.source).1.1 := by
    change source.store=world.machine.source.store
    exact guard.storeEq.trans ((congrArg (Store.decodeStore view world.code) nativeStore).trans world.machine.invariant.storeEq.symm)
  have oldEq:=Spec.OpenExecution.State.wasm_eq source (Abs.decode world.machine.source) (.mk_list (signature.results.val.map sourceType)) oldStore sourceMode
  have projected : Spec.OpenExecution.Trace (sourceModel view (sourcePublication allocator view) select owner stop) count source events nextSource := by
    rw [oldEq]
    exact trace
  have token : world.machine.platform=():=Subsingleton.elim _ _
  have preparedUnit:=prepared
  rw [token,←nativeStore] at preparedUnit
  refine ⟨next,afterCode,nextSource,count,events,?_,effectActual,nextGuard,positive,projected,cause,rfl,visible⟩
  rw [wasm_active_tick memory floats allocator select native world.machine.exec root results mode active (.done out) preparedUnit]
  simp only [acceptCall,failed,next]
end Exec.Theorems.OpenReentrantControl

import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.Control.Publication
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Root input rejection and preparation exhaustion retain their separate
source rules. Resource refusal uses the independent stop policy and keeps the
actual preparation cause in the input guard. -/
theorem SourceRootCallCause.stopped {M A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform Unit M} {exec : runtime.interp.Execution} {store : runtime.store.Store M}
    {token : Unit} {address : runtime.FuncAddr} {signature : Itasca.types.FuncType} {error : runtime.ExecError}
    (cause : SourceRootCallCause allocator hooks exec store token address signature error)
    (values : alloc.vec.Vec runtime.Value) :
    ∃reason,sourceInvocationResult (.Err error) values=.stopped reason := by
  cases cause with
  | defined function instanceIndex functionIndex inst compiled functionAt kind instanceAt compiledAt cause=>
    cases error <;> simp_all [CallCause,sourceInvocationResult]
    rename_i limit
    cases limit <;> simp_all [CallCause,sourceInvocationResult]
  | host function identity functionAt kind cause=>
    have supported:=cause.error
    cases error <;> simp_all [HostPreparationError,sourceInvocationResult]
    rename_i limit
    cases limit <;> simp_all [HostPreparationError,sourceInvocationResult]

theorem source_prepared_refused {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (code : Store.CodeInterpretation)
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (guard : SourceStateGuard memory allocator view code native source 0)
    (address : runtime.FuncAddr) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value) (answer : Answer M Unit)
    (exec : runtime.interp.Execution)
    (error : runtime.ExecError) (status : answer.1=.Err error) (sameStore : answer.2.2.1=native.store)
    (metadata : RootMetadata native.store address signature)
    (arguments : ResultsTyped (Store.decodeStore view code native.store) (signature.params.val.map sourceType) (args.val.map sourceValue))
    (cause : SourceRootCallCause allocator (inert memory) exec native.store () address signature error)
    (mode : native.mode=.preparing (.waiting (.done answer) address results))
    (sourceMode : source.mode=.invokeRequest address.index.val (args.val.map sourceValue)
      (signature.params.val.map sourceType) (signature.results.val.map sourceType))
    (allowed : ∀reason configuration,stop reason configuration) :
    ∃next nextSource,tick memory floats allocator select native=.ok (.cont next) ∧
      SourceStateGuard memory allocator view code next nextSource 1 ∧
      Spec.OpenExecution.Trace (sourceModel view (sourcePublication allocator view) select owner stop) 2 source [] nextSource ∧
      next.history=native.history := by
  have mapped : ∃reason,sourceInvocationResult (.Err error) results=.stopped reason:=cause.stopped results
  obtain ⟨reason,mapped⟩:=mapped
  let next : State M:={native with mode:=.wasm answer.2.1 (.Err error) address results}
  let nextSource : Spec.OpenExecution.State SourceControl:=⟨source.store,.invokeReturn (.stopped reason),source.stack⟩
  have canonical : source=⟨Store.decodeStore view code native.store,
      .invokeRequest address.index.val (args.val.map sourceValue) (signature.params.val.map sourceType) (signature.results.val.map sourceType),source.stack⟩ := by
    rcases source with ⟨s,m,stack⟩
    dsimp only at sourceMode
    subst m
    have same : s=Store.decodeStore view code native.store:=guard.storeEq
    subst s
    rfl
  refine ⟨next,nextSource,?_,?_,?_,rfl⟩
  · simp only [tick,mode,acceptCall,status,sameStore,next]
  · refine ⟨guard.invariant,?_,guard.stack,guard.storeEq⟩
    simpa only [next,nextSource,mapped] using
      (SourceMode.finishing (memory:=memory) (allocator:=allocator) (view:=view) (code:=code)
        answer.2.1 error address results signature metadata)
  · dsimp only [nextSource]
    rw [guard.storeEq,canonical]
    exact .next (.acceptInvoke arguments) (.next (.cutoff (allowed reason _)) (.nil _))
end Exec.Theorems.OpenReentrantControl

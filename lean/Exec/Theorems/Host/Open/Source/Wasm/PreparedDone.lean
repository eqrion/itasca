import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.Control.Publication
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Root input rejection and preparation exhaustion retain their separate
source rules. Resource refusal uses the independent stop policy and keeps the
actual preparation cause in the input guard. -/
theorem source_prepared_done {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (code : Store.CodeInterpretation)
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (guard : SourceStateGuard memory allocator view code native source 0)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value) (answer : InvokeAnswer M Unit)
    (ready : SourceRootInvokeReady allocator (inert memory) view code exec native.store () Spec.invocationFrame address signature args results (.done answer))
    (mode : native.mode=.preparing (.done answer))
    (sourceMode : source.mode=.invokeRequest address.index.val (args.val.map sourceValue)
      (signature.params.val.map sourceType) (signature.results.val.map sourceType))
    (allowed : ∀reason configuration,stop reason configuration) :
    ∃next nextSource count,tick memory floats allocator select native=.ok (.cont next) ∧
      SourceStateGuard memory allocator view code next nextSource 0 ∧ 0<count ∧
      Spec.OpenExecution.Trace (sourceModel view (sourcePublication allocator view) select owner stop) count source [] nextSource ∧
      next.history=native.history := by
  let model:=sourceModel view (sourcePublication allocator view) select owner stop
  have canonical : source=⟨Store.decodeStore view code native.store,
      .invokeRequest address.index.val (args.val.map sourceValue) (signature.params.val.map sourceType) (signature.results.val.map sourceType),source.stack⟩ := by
    rcases source with ⟨s,m,stack⟩
    dsimp only at sourceMode
    subst m
    have same : s=Store.decodeStore view code native.store:=guard.storeEq
    subst s
    rfl
  cases ready with
  | rejected error kind notTyped=>
    have mapped : sourceInvocationResult (.Err error) results=.rejected := by
      rcases kind with rfl|rfl <;> rfl
    let next : State M:={native with mode:=.invokeReturn (.Err error,exec,native.store,(),results)}
    let nextSource : Spec.OpenExecution.State SourceControl:=⟨source.store,.invokeReturn .rejected,source.stack⟩
    refine ⟨next,nextSource,1,?_,?_,by omega,?_,rfl⟩
    · simp only [tick,mode,next]
    · refine ⟨guard.invariant,?_,guard.stack,guard.storeEq⟩
      simpa only [next,nextSource,mapped] using
        (SourceMode.returned (memory:=memory) (allocator:=allocator) (view:=view) (code:=code)
          (.Err error,_,native.store,(),results) rfl (by intro impossible;cases impossible))
    · dsimp only [nextSource]
      rw [guard.storeEq,canonical]
      exact .next (.rejectInvoke notTyped) (.nil _)
  | resource error afterExec typed cause=>
    have mapped : ∃reason,sourceInvocationResult (.Err error) results=.stopped reason := by
      rcases cause.kind with rfl|rfl <;> exact ⟨_,rfl⟩
    obtain ⟨reason,mapped⟩:=mapped
    let next : State M:={native with mode:=.invokeReturn (.Err error,afterExec,native.store,(),results)}
    let nextSource : Spec.OpenExecution.State SourceControl:=⟨source.store,.invokeReturn (.stopped reason),source.stack⟩
    refine ⟨next,nextSource,2,?_,?_,by omega,?_,rfl⟩
    · simp only [tick,mode,next]
    · refine ⟨guard.invariant,?_,guard.stack,guard.storeEq⟩
      simpa only [next,nextSource,mapped] using
        (SourceMode.returned (memory:=memory) (allocator:=allocator) (view:=view) (code:=code)
          (.Err error,_,native.store,(),results) rfl (by intro impossible;cases impossible))
    · dsimp only [nextSource]
      rw [guard.storeEq,canonical]
      exact .next (.acceptInvoke typed) (.next (.cutoff (allowed reason _)) (.nil _))
end Exec.Theorems.OpenReentrantControl

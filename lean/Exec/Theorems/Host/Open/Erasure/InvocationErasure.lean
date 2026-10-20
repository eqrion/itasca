import Exec.Theorems.Host.Open.Native.FiniteInvocationErasure
import Exec.Theorems.Host.Open.Driver.InvocationDriver
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- A checked prepared root which returns has exactly the synchronous native
phase answer. Expanded history remains attached to the combined result. -/
theorem prepared_run_erases {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (phase : InvokePhase M Unit)
    (history : List Observation)
    (guard : StateGuard memory view code ⟨store,.preparing phase,[],history⟩)
    (out : Outcome M) (actual : run memory floats allocator select ⟨store,.preparing phase,[],history⟩=.ok out) :
    ∃returned observed,out=.invocation returned observed ∧
      eraseInvoke memory (platform memory floats allocator select) floats allocator phase=.ok returned := by
  have safe:=run_safe memory floats allocator correct allocation view laws select code ⟨store,.preparing phase,[],history⟩ guard
  rw [actual,WP.dspec_ok] at safe
  obtain ⟨count,trace,rest⟩ := safe
  obtain ⟨returned,equal,native⟩ := Erased.finite_invocation_erases memory floats allocator select count store (.preparing phase)
    (Erased.outcome out) (erase_normal_trace memory floats allocator select trace)
  cases out with
  | host reply observed=>simp [Erased.outcome] at equal
  | invocation answer observed=>
    have same : answer=returned := by simpa [Erased.outcome] using equal
    subst answer
    exact ⟨returned,observed,rfl,native⟩

/-- Every actual returning combined invocation agrees with the public extracted
synchronous invocation under the same driver Platform. Resource and input
rejections retain their actual API answer; host normality is not an input. -/
theorem invoke_return_erases {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (owner : address.store=store.id)
    (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (signatureAt : store.types.val[function.signature.val]?=some signature)
    (args : Slice runtime.Value) (issued : ∀value∈args.val,Store.IssuedValue store value)
    (results : alloc.vec.Vec runtime.Value) (returned : InvokeAnswer M Unit) (history : List Observation)
    (actual : invoke memory floats allocator select exec store address args results=.ok (returned,history)) :
    runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator exec store () address args results=.ok returned := by
  obtain ⟨phase,prepared,ready⟩ := WP.spec_imp_exists (prepare_root_input memory (inert memory) floats allocator allocation
    (fun _=>WP.spec.ret trivial) view code exec store () held default Spec.empty_frame_wf address function signature args results
    owner issued functionAt signatureAt)
  have task:=ready.task memory held Spec.empty_frame_wf ⟨owner,function,functionAt,signatureAt⟩
  have guard : StateGuard memory view code ⟨store,.preparing phase,[],[.invokeEnter address args]⟩ := ⟨held,task,trivial⟩
  simp only [invoke,prepared,bind_ok] at actual
  obtain ⟨out,ran,packed⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
  obtain ⟨nativeAnswer,observed,rfl,native⟩ := prepared_run_erases memory floats allocator correct allocation view laws select code store phase
    [.invokeEnter address args] guard out ran
  have same : nativeAnswer=returned := by
    have pairEq : (nativeAnswer,observed)=(returned,history) := by simpa using packed
    exact congrArg Prod.fst pairEq
  subst nativeAnswer
  have graph:=erase_invoke memory (platform memory floats allocator select) floats allocator exec store () address args results
  rw [prepareInvoke_independent memory (platform memory floats allocator select) (inert memory) floats allocator exec store () address args results (fun _=>rfl),
    prepared,bind_ok,native] at graph
  exact graph.symm
end Exec.Theorems.OpenReentrantControl

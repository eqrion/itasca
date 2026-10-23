import Exec.Theorems.Host.Open.Native.NativePhaseLift
import Exec.Theorems.Host.Open.Erasure.InvocationErasure
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

theorem native_invoke_return_lifts {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (owner : address.store=store.id)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (signatureAt : store.types.val[function.signature.val]?=some signature)
    (args : Slice runtime.Value) (issued : ∀value∈args.val,Store.IssuedValue store value)
    (results : alloc.vec.Vec runtime.Value) (returned : InvokeAnswer M Unit)
    (actual : runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator exec store () address args results=.ok returned) :
    ∃history,invoke memory floats allocator select exec store address args results=.ok (returned,history) := by
  obtain ⟨phase,prepared,ready⟩ := WP.spec_imp_exists (prepare_root_input memory (inert memory) floats allocator allocation
    (fun _=>WP.spec.ret trivial) view code exec store () held default Spec.empty_frame_wf address function signature args results
    owner issued functionAt signatureAt)
  have task:=ready.task memory held Spec.empty_frame_wf ⟨owner,function,functionAt,signatureAt⟩
  have graph:=erase_invoke memory (platform memory floats allocator select) floats allocator exec store () address args results
  rw [prepareInvoke_independent memory (platform memory floats allocator select) (inert memory) floats allocator exec store () address args results (fun _=>rfl),
    prepared,bind_ok] at graph
  have nativePhase:=graph.trans actual
  obtain ⟨count,physical⟩ := Erased.native_phase_lift memory floats allocator correct allocation view laws select code store held phase task returned nativePhase
  obtain ⟨out,erased,trace⟩ := lift_normal_trace memory floats allocator select physical
    (⟨store,.preparing phase,[],[.invokeEnter address args]⟩ : State M) rfl
  cases out with
  | host reply history=>simp [Erased.outcome] at erased
  | invocation answer history=>
    have same : answer=returned := by simpa [Erased.outcome] using erased
    subst answer
    refine ⟨history,?_⟩
    have ran:=trace.result
    simp only [invoke,prepared,bind_ok,run,ran]
end Exec.Theorems.OpenReentrantControl

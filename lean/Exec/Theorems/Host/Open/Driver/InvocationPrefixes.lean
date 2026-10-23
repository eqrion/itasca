import Exec.Theorems.Host.Open.Erasure.InvocationEquivalence
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- Divergence of the synchronous native API exposes a coherent stream of
actual combined-driver ticks. Every prefix retains the full entered-world
effect and its pending observations; no infinite Wasm trace is asserted here. -/
theorem native_invoke_divergent_prefixes {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (owner : address.store=store.id)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (signatureAt : store.types.val[function.signature.val]?=some signature)
    (args : Slice runtime.Value) (issued : ∀value∈args.val,Store.IssuedValue store value)
    (results : alloc.vec.Vec runtime.Value)
    (nativeDiverges : runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator
      exec store () address args results=.div) :
    ∃phase,prepareInvoke memory (inert memory) floats allocator exec store () address args results=.ok phase ∧
      ∃states : Nat → State M,states 0=⟨store,.preparing phase,[],[.invokeEnter address args]⟩ ∧ ∀n,
        RunningFrom memory view code store (states n) ∧
        tick memory floats allocator select (states n)=.ok (.cont (states (n+1))) ∧
        run memory floats allocator select (states n)=.div ∧
        ∃events,(states n).history=[.invokeEnter address args]++events := by
  have divergent := (invoke_diverges_iff_native memory floats allocator correct allocation view laws select code store held
    exec address owner function signature functionAt signatureAt args issued results).mpr nativeDiverges
  obtain ⟨phase,prepared,ready⟩ := WP.spec_imp_exists
    (prepare_root_input memory (inert memory) floats allocator allocation (fun _=>WP.spec.ret trivial)
      view code exec store () held default Spec.empty_frame_wf address function signature args results owner issued functionAt signatureAt)
  let initial : State M:=⟨store,.preparing phase,[],[.invokeEnter address args]⟩
  have guard : StateGuard memory view code initial:=
    ⟨held,ready.task memory held Spec.empty_frame_wf ⟨owner,function,functionAt,signatureAt⟩,trivial⟩
  have safe := run_safe memory floats allocator correct allocation view laws select code initial guard
  have runDiverges : run memory floats allocator select initial=.div := by
    generalize actual : run memory floats allocator select initial=result at safe ⊢
    cases safe with
    | div=>rfl
    | ret post=>
      rename_i out
      unfold invoke at divergent
      rw [prepared,bind_ok] at divergent
      change (do let outcome←run memory floats allocator select initial
                 match outcome with
                 | .invocation answer history=>.ok (answer,history)
                 | .host answer history=>.ok ((.Err (.Trap .Host),exec,answer.2.1,(),results),history))=.div at divergent
      simp only [actual,bind_tc_eq,bind_ok] at divergent
      cases out <;> exact False.elim (ok_not_div divergent)
  obtain ⟨states,first,steps⟩ := run_divergent_stream memory floats allocator correct allocation view laws select code initial guard runDiverges
  exact ⟨phase,prepared,states,first,steps⟩
end Exec.Theorems.OpenReentrantControl

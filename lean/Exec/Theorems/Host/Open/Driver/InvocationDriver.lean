import Exec.Theorems.Host.Open.Driver.DriverPrefixes
import Exec.Theorems.Host.Open.Driver.StackTraces
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall
noncomputable section

/-- Root invocation through the same resumable native setup and combined
execution stack used for nested invocations. The history exposes pending entry. -/
def invoke {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (address : runtime.FuncAddr)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value) : Result (InvokeAnswer M Unit × List Observation) := do
  let phase ← prepareInvoke memory (inert memory) floats allocator exec store () address args results
  let outcome ← run memory floats allocator select ⟨store,.preparing phase,[],[.invokeEnter address args]⟩
  match outcome with
  | .invocation answer history => .ok (answer,history)
  | .host answer history => .ok ((.Err (.Trap .Host),exec,answer.2.1,(),results),history)

/-- The combined root adapter retains typed stores and issued results without
requiring host control or nested Wasm execution to terminate. Every returned
history retains its initial invocation entry. Synchronous native erasure is a
separate obligation from this adapter's checked prefix safety. -/
theorem invoke_safe {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (owner : address.store=store.id)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (signatureAt : store.types.val[function.signature.val]?=some signature)
    (args : Slice runtime.Value) (issued : ∀value∈args.val,Store.IssuedValue store value)
    (results : alloc.vec.Vec runtime.Value) :
    invoke memory floats allocator select exec store address args results ⦃out=>∃afterCode,
      ReentrantCallbacks.Effect view code store afterCode out.1.2.2.1 ∧
      (out.1.1=.Ok () → ∀value∈out.1.2.2.2.2.val,Store.IssuedValue out.1.2.2.1 value) ∧
      ∃events,out.2=[.invokeEnter address args]++events⦄div := by
  obtain ⟨phase,prepared,ready⟩ := WP.spec_imp_exists (prepare_root_input memory (inert memory) floats allocator allocation
    (fun _=>WP.spec.ret trivial) view code exec store () held default Spec.empty_frame_wf address function signature args results
    owner issued functionAt signatureAt)
  have task := ready.task memory held Spec.empty_frame_wf ⟨owner,function,functionAt,signatureAt⟩
  let initial : State M := ⟨store,.preparing phase,[],[.invokeEnter address args]⟩
  have guard : StateGuard memory view code initial := ⟨held,task,trivial⟩
  have safe := run_safe memory floats allocator correct allocation view laws select code initial guard
  unfold invoke
  rw [prepared,bind_ok]
  change (do let outcome←run memory floats allocator select initial
             match outcome with
             | .invocation answer history=>.ok (answer,history)
             | .host answer history=>.ok ((.Err (.Trap .Host),exec,answer.2.1,(),results),history)) ⦃_⦄div
  generalize actual : run memory floats allocator select initial=runResult at safe ⊢
  cases safe with
  | div => simp only [bind_div]; exact WP.dspec.div _
  | ret post =>
    rename_i answer
    obtain ⟨count,trace,afterCode,effect,fresh⟩ := post
    have kind := returned_shape memory floats allocator select trace (show initial.Shape .invocation from .nil _)
    have history := returned_history memory floats allocator select trace
    cases answer with
    | host answer observed => cases kind
    | invocation answer observed =>
      simp only [bind_ok]
      exact WP.dspec.ret ⟨afterCode,effect,fresh.2,history⟩
end
end Exec.Theorems.OpenReentrantControl

import Exec.Theorems.Host.Open.Source.State.Invocation
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall
section
variable {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (owner : address.store=store.id)
    (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (signatureAt : store.types.val[function.signature.val]?=some signature)
    (args : Slice runtime.Value) (owned : ∀value∈args.val,Store.ValueInStore store value)
    (results : alloc.vec.Vec runtime.Value)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (allowed : ∀reason configuration,stop reason configuration)
include correct allocation laws held owner owned functionAt signatureAt allowed

/-- The synchronous public implementation inherits the independent combined
source return theorem, including committed effects on error. -/
theorem native_invoke_source_partial :
    runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator exec store () address args results
      ⦃out=>∃afterCode completed count events,
        ReentrantCallbacks.Effect view code store afterCode out.2.2.1 ∧
        Spec.OpenExecution.Trace (sourceModel view (sourcePublication allocator view) select store.id stop) count
          (sourceInvocationEntry view code store address signature args) events completed ∧
        completed.Typed ∧ SourceOutcome view afterCode (.invocation out []) completed ∧
        ∃history,invoke memory floats allocator select exec store address args results=.ok (out,history) ∧
          sourceHistory history=sourceHistory [Observation.invokeEnter address args]++visibleSourceHistory events⦄div := by
  have safe:=native_invoke_partial memory floats allocator correct allocation view laws select code store held exec address owner
    function signature functionAt signatureAt args (fun value member=>(owned value member).issued) results
  generalize actual : runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator exec store () address args results=result at safe ⊢
  cases safe with
  | div=>exact WP.dspec.div _
  | ret post=>
    rename_i answer
    obtain ⟨history,lifted⟩:=native_invoke_return_lifts memory floats allocator correct allocation view laws select code store held exec address owner
      function signature functionAt signatureAt args (fun value member=>(owned value member).issued) results answer actual
    have source:=invoke_source_partial memory floats allocator correct allocation view laws select code store held exec address owner
      function signature functionAt signatureAt args owned results stop allowed
    rw [lifted,WP.dspec_ok] at source
    obtain ⟨afterCode,completed,count,events,effect,path,typed,matching,observed⟩:=source
    exact WP.dspec.ret ⟨afterCode,completed,count,events,effect,path,typed,matching,history,lifted,observed⟩

/-- Synchronous native divergence reflects into a productive combined trace;
it is not relabelled as divergence of Wasm alone. -/
theorem native_invoke_source_diverges
    (divergent : runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator exec store () address args results=.div) :
    Spec.OpenExecution.InfiniteTrace (sourceModel view (sourcePublication allocator view) select store.id stop)
      (sourceInvocationEntry view code store address signature args) := by
  have driver:=(invoke_diverges_iff_native memory floats allocator correct allocation view laws select code store held exec address owner
    function signature functionAt signatureAt args (fun value member=>(owned value member).issued) results).mpr divergent
  exact invoke_source_diverges memory floats allocator correct allocation view laws select code store held exec address owner
    function signature functionAt signatureAt args owned results stop allowed driver

/-- Absence of every infinite combined source execution excludes concrete
native divergence. It guarantees an ordinary API result, including classified
resource or interrupt outcomes; successful return needs stronger premises. -/
theorem native_invoke_source_terminates
    (terminates : ¬Spec.OpenExecution.InfiniteTrace (sourceModel view (sourcePublication allocator view) select store.id stop)
      (sourceInvocationEntry view code store address signature args)) :
    runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator exec store () address args results
      ⦃out=>∃afterCode completed count events,
        ReentrantCallbacks.Effect view code store afterCode out.2.2.1 ∧
        Spec.OpenExecution.Trace (sourceModel view (sourcePublication allocator view) select store.id stop) count
          (sourceInvocationEntry view code store address signature args) events completed ∧
        completed.Typed ∧ SourceOutcome view afterCode (.invocation out []) completed ∧
        ∃history,invoke memory floats allocator select exec store address args results=.ok (out,history) ∧
          sourceHistory history=sourceHistory [Observation.invokeEnter address args]++visibleSourceHistory events⦄ := by
  have source:=native_invoke_source_partial memory floats allocator correct allocation view laws select code store held exec address owner
    function signature functionAt signatureAt args owned results stop allowed
  generalize actual : runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator exec store () address args results=result at source ⊢
  cases source with
  | ret post=>exact WP.spec.ret post
  | div=>exact False.elim (terminates (native_invoke_source_diverges memory floats allocator correct allocation view laws select code store held exec address owner
      function signature functionAt signatureAt args owned results stop allowed actual))
end
end Exec.Theorems.OpenReentrantControl

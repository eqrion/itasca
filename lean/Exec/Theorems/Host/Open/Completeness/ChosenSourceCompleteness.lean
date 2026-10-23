import Exec.Theorems.Host.Open.Completeness.ReferenceCompletion
import Exec.Theorems.Host.Open.Native.NativeChosenSourceInvocation
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall
section
variable {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (choices : SourceOperationChoices) (admissible : choices.Admissible view (sourcePublication allocator view))
    (numericChoice : choices.wasm.numeric=Spec.firstNumericChoice)
    (vectorChoice : choices.wasm.vector=Spec.firstVectorChoice)
    (growthCompatible : GrowthChoicesCompatible memory allocator view choices.wasm)
    (apiCompatible : SourceAPIChoicesCompatible memory allocator view choices)
    (publicationCompatible : SourcePublicationChoicesCompatible memory floats allocator view choices) (occurrence : Nat)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (owner : address.store=store.id)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (signatureAt : store.types.val[function.signature.val]?=some signature)
    (args : Slice runtime.Value) (owned : ∀value∈args.val,Store.ValueInStore store value)
    (results : alloc.vec.Vec runtime.Value)
    (stop : Spec.OpenExecution.StopReason → config → Prop)
    (resources : ChosenSourceResources (sourceModel view (sourcePublication allocator view) select store.id stop)
      (sourceControlChoices choices) occurrence store.limits (sourceInvocationEntry view code store address signature args))
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
include correct allocation laws held owner owned functionAt signatureAt
  admissible numericChoice vectorChoice growthCompatible apiCompatible publicationCompatible resources available

/-- A terminating matched combined source run yields an ordinary public
resumable invocation result with its exact source outcome and visible history. -/
theorem invoke_source_chosen_complete {count events target}
    (reference : Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select store.id stop)
      (sourceControlChoices choices) occurrence count
      (sourceInvocationEntry view code store address signature args) events target)
    (completed : ∃result,target.mode=.completed result) :
    invoke memory floats allocator select exec store address args results ⦃out=>∃afterCode,
      ReentrantCallbacks.Effect view code store afterCode out.1.2.2.1 ∧
      SourceOutcome view afterCode (.invocation out.1 out.2) target ∧
      sourceHistory out.2=sourceHistory [Observation.invokeEnter address args]++visibleSourceHistory events⦄ := by
  obtain ⟨phase,prepared,guard,shape,safe⟩:=WP.spec_imp_exists
    (prepare_source_root_guard memory floats allocator allocation view code exec store held address function signature args results owner owned functionAt signatureAt)
  let initial : State M:=⟨store,.preparing phase,[],[.invokeEnter address args]⟩
  obtain ⟨ticks,outcome,afterCode,trace,effect,matching,observed⟩:=chosen_source_complete memory floats allocator correct allocation view laws select store.id stop
    choices admissible numericChoice vectorChoice growthCompatible apiCompatible publicationCompatible available occurrence code initial _ 0
    guard shape safe rfl resources reference completed
  have returned : run memory floats allocator select initial=.ok outcome:=trace.result
  unfold invoke
  rw [prepared,bind_ok]
  change (do let out←run memory floats allocator select initial
             match out with
             | .invocation answer history=>.ok (answer,history)
             | .host answer history=>.ok ((.Err (.Trap .Host),exec,answer.2.1,(),results),history)) ⦃_⦄
  rw [returned,bind_ok]
  cases outcome with
  | host answer history=>cases matching
  | invocation answer history=>exact WP.spec.ret ⟨afterCode,effect,matching,observed⟩

/-- The actual synchronous invoke_with implementation returns the outcome of
one terminating chosen combined source run. No universal callback-normality
or absence-of-all-infinite-runs premise is used. -/
theorem native_invoke_chosen_source_complete {count events target}
    (reference : Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select store.id stop)
      (sourceControlChoices choices) occurrence count
      (sourceInvocationEntry view code store address signature args) events target)
    (completed : ∃result,target.mode=.completed result) :
    runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator exec store () address args results
      ⦃out=>∃afterCode,
        ReentrantCallbacks.Effect view code store afterCode out.2.2.1 ∧
        SourceOutcome view afterCode (.invocation out []) target ∧
        ∃history,invoke memory floats allocator select exec store address args results=.ok (out,history) ∧
          sourceHistory history=sourceHistory [Observation.invokeEnter address args]++visibleSourceHistory events⦄ := by
  obtain ⟨⟨answer,history⟩,returned,afterCode,effect,matching,observed⟩:=WP.spec_imp_exists
    (invoke_source_chosen_complete memory floats allocator correct allocation view laws select choices admissible numericChoice vectorChoice
      growthCompatible apiCompatible publicationCompatible occurrence code store held exec address owner function signature functionAt signatureAt
      args owned results stop resources available reference completed)
  have erased:=invoke_return_erases memory floats allocator correct allocation view laws select code store held exec address owner
    function signature functionAt signatureAt args (fun value member=>(owned value member).issued) results answer history returned
  rw [erased]
  exact WP.spec.ret ⟨afterCode,effect,matching,history,returned,observed⟩
end
end Exec.Theorems.OpenReentrantControl

import Exec.Theorems.Host.Open.Source.State.Invocation
import Exec.Theorems.Host.Open.Source.Chosen.ChosenFinite
import Exec.Theorems.Host.Open.Source.Chosen.ChosenDivergence
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall
/-- Public open invocation retains independently admissible selected choices
and exact reached outcomes. Capacity conditions concern source prefixes at
initial limits; callback or nested-invocation normality is not assumed. -/
theorem invoke_source_chosen_partial {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
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
    (available : Platform.AllocationAvailable allocator (2*Usize.max)) :
    invoke memory floats allocator select exec store address args results ⦃out=>∃afterCode completed count events,
      ReentrantCallbacks.Effect view code store afterCode out.1.2.2.1 ∧
      Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select store.id stop)
        (sourceControlChoices choices) occurrence count
        (sourceInvocationEntry view code store address signature args) events completed ∧
      completed.Typed ∧ SourceOutcome view afterCode (.invocation out.1 out.2) completed ∧
      sourceHistory out.2=sourceHistory [Observation.invokeEnter address args]++visibleSourceHistory events⦄div := by
  obtain ⟨phase,prepared,guard,shape,safe⟩:=WP.spec_imp_exists
    (prepare_source_root_guard memory floats allocator allocation view code exec store held address function signature args results owner owned functionAt signatureAt)
  let initial : State M:=⟨store,.preparing phase,[],[.invokeEnter address args]⟩
  let source:=sourceInvocationEntry view code store address signature args
  have runSafe:=run_safe memory floats allocator correct allocation view laws select code initial guard.native
  unfold invoke
  rw [prepared,bind_ok]
  change (do let outcome←run memory floats allocator select initial
             match outcome with
             | .invocation answer history=>.ok (answer,history)
             | .host answer history=>.ok ((.Err (.Trap .Host),exec,answer.2.1,(),results),history)) ⦃_⦄div
  generalize actual : run memory floats allocator select initial=result at runSafe ⊢
  cases runSafe with
  | div=>simp only [bind_div];exact WP.dspec.div _
  | ret post=>
    rename_i outcome
    obtain ⟨ticks,nativeTrace,nativePost⟩:=post
    obtain ⟨afterCode,completed,count,events,effect,path,typed,matching,observed⟩:=normal_trace_chosen_source memory floats allocator correct allocation
      view laws select store.id stop choices admissible.wasm numericChoice vectorChoice growthCompatible apiCompatible publicationCompatible
      nativeTrace occurrence code source 0 guard shape safe rfl resources available
    cases outcome with
    | host answer history=>cases matching
    | invocation answer history=>
      simp only [bind_ok]
      exact WP.dspec.ret ⟨afterCode,completed,count,events,effect,path,typed,matching,observed⟩

/-- Divergence of the resumable public adapter reflects to productive combined
source execution, starting at the actual checked invocation request. -/
theorem invoke_source_chosen_diverges {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
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
    (divergent : invoke memory floats allocator select exec store address args results=.div) :
    Spec.OpenExecution.ChoiceInfinite (sourceModel view (sourcePublication allocator view) select store.id stop)
      (sourceControlChoices choices) occurrence
      (sourceInvocationEntry view code store address signature args) := by
  obtain ⟨phase,prepared,guard,shape,safe⟩:=WP.spec_imp_exists
    (prepare_source_root_guard memory floats allocator allocation view code exec store held address function signature args results owner owned functionAt signatureAt)
  let initial : State M:=⟨store,.preparing phase,[],[.invokeEnter address args]⟩
  have runSafe:=run_safe memory floats allocator correct allocation view laws select code initial guard.native
  have diverges : run memory floats allocator select initial=.div:=by
    generalize actual : run memory floats allocator select initial=result at runSafe ⊢
    cases runSafe with
    | div=>rfl
    | ret post=>
      rename_i outcome
      unfold invoke at divergent
      rw [prepared,bind_ok] at divergent
      change (do let answer←run memory floats allocator select initial;_) =.div at divergent
      rw [actual] at divergent
      simp only [bind_tc_eq,bind_ok] at divergent
      cases outcome <;> exact False.elim (ok_not_div divergent)
  exact run_chosen_source_infinite memory floats allocator correct allocation view laws select store.id stop
    choices admissible.wasm numericChoice vectorChoice growthCompatible apiCompatible publicationCompatible occurrence
    code initial _ 0 guard shape safe rfl resources available diverges
end Exec.Theorems.OpenReentrantControl

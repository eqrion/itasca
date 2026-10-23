import Exec.Theorems.Host.Open.Completeness.ChosenSourceCompleteness
import Exec.Theorems.Host.Open.Completeness.ReturningRecovery
import Exec.Theorems.Host.Open.Native.NativeChosenSourceInvocation

/-!
# Host driver

Guarantees of the certified synchronous host driver `Theorems.OpenReentrantControl`: its entry
`invoke`, and `runtime.interp.invoke_with` run with the driver as its `platform`. Callbacks are
Lean programs over a checked action language (`Selector`), so these results cover unbounded
reentrancy and code publication against one combined Wasm/host source semantics.

The chosen-run results fix one admissible combined source policy (`SourceOperationChoices`) and
require the actual platform to agree with it; see [Contracts](../Contracts.lean). The callbacks are
Lean models of the interface: arbitrary Rust callbacks still need a refinement contract, and
concrete publication covers modules with empty imports and no start function.
-/

open Aeneas Aeneas.Std SpecExt

namespace Exec

open Theorems Theorems.OpenReentrantControl Interp Interp.OpenCall

/-- A terminating matched combined source run yields an ordinary result of the driver entry
`invoke`, with its exact source outcome and visible history. Source-prefix capacities, allocation
availability and numeric/vector/growth/API/publication compatibility are explicit premises. -/
theorem Theorems.OpenReentrantControl.invoke.chosen_complete
    {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
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
    (available : Platform.AllocationAvailable allocator (2*Usize.max)) {count events target}
    (reference : Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select store.id stop)
      (sourceControlChoices choices) occurrence count
      (sourceInvocationEntry view code store address signature args) events target)
    (completed : ∃result,target.mode=.completed result) :
    invoke memory floats allocator select exec store address args results ⦃out=>∃afterCode,
      ReentrantCallbacks.Effect view code store afterCode out.1.2.2.1 ∧
      SourceOutcome view afterCode (.invocation out.1 out.2) target ∧
      sourceHistory out.2=sourceHistory [Observation.invokeEnter address args]++visibleSourceHistory events⦄ :=
  invoke_source_chosen_complete memory floats allocator correct allocation view laws select choices
    admissible numericChoice vectorChoice growthCompatible apiCompatible publicationCompatible
    occurrence code store held exec address owner function signature functionAt signatureAt args
    owned results stop resources available reference completed

/-- The actual synchronous `invoke_with` with the driver as its platform returns the outcome of one
terminating chosen combined source run, including unbounded reentrancy and expanded nesting
observations. No universal callback-normality or absence-of-all-infinite-runs premise is used. The
driver supplies continuing interrupts and excludes host stack exhaustion. -/
theorem Theorems.OpenReentrantControl.platform.invoke_chosen_complete
    {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
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
    (available : Platform.AllocationAvailable allocator (2*Usize.max)) {count events target}
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

/-- The synchronous public implementation inherits the independent combined source return theorem,
including committed effects on error: every normal result has a typed chosen combined source run
with the same outcome and visible history. Divergence is allowed; see `invoke_chosen_diverges`. -/
theorem Theorems.OpenReentrantControl.platform.invoke_chosen_sound
    {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
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
    runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator exec store () address args results
      ⦃out=>∃afterCode completed count events,
        ReentrantCallbacks.Effect view code store afterCode out.2.2.1 ∧
        Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select store.id stop)
          (sourceControlChoices choices) occurrence count
          (sourceInvocationEntry view code store address signature args) events completed ∧
        completed.Typed ∧ SourceOutcome view afterCode (.invocation out []) completed ∧
        ∃history,invoke memory floats allocator select exec store address args results=.ok (out,history) ∧
          sourceHistory history=sourceHistory [Observation.invokeEnter address args]++visibleSourceHistory events⦄div :=
  native_invoke_chosen_source_partial memory floats allocator correct allocation view laws select
    choices admissible numericChoice vectorChoice growthCompatible apiCompatible
    publicationCompatible occurrence code store held exec address owner function signature
    functionAt signatureAt args owned results stop resources available

/-- Synchronous native divergence reflects into a productive combined trace under the same selected
policy; it is not relabelled as divergence of Wasm alone. -/
theorem Theorems.OpenReentrantControl.platform.invoke_chosen_diverges
    {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
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
    (divergent : runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator exec store () address args results=.div) :
    Spec.OpenExecution.ChoiceInfinite (sourceModel view (sourcePublication allocator view) select store.id stop)
      (sourceControlChoices choices) occurrence
      (sourceInvocationEntry view code store address signature args) :=
  native_invoke_chosen_source_diverges memory floats allocator correct allocation view laws select
    choices admissible numericChoice vectorChoice growthCompatible apiCompatible
    publicationCompatible occurrence code store held exec address owner function signature
    functionAt signatureAt args owned results stop resources available divergent

/-- Absence of an infinite combined run under this selected policy excludes native divergence. Source
capacities and primitive compatibility are explicit; this theorem does not replace termination by
one chosen finite-run premise. -/
theorem Theorems.OpenReentrantControl.platform.invoke_chosen_terminates
    {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
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
    (terminates : ¬Spec.OpenExecution.ChoiceInfinite (sourceModel view (sourcePublication allocator view) select store.id stop)
      (sourceControlChoices choices) occurrence
      (sourceInvocationEntry view code store address signature args)) :
    runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator exec store () address args results
      ⦃out=>∃afterCode completed count events,
        ReentrantCallbacks.Effect view code store afterCode out.2.2.1 ∧
        Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select store.id stop)
          (sourceControlChoices choices) occurrence count
          (sourceInvocationEntry view code store address signature args) events completed ∧
        completed.Typed ∧ SourceOutcome view afterCode (.invocation out []) completed ∧
        ∃history,invoke memory floats allocator select exec store address args results=.ok (out,history) ∧
          sourceHistory history=sourceHistory [Observation.invokeEnter address args]++visibleSourceHistory events⦄ := by
  have source:=native_invoke_chosen_source_partial memory floats allocator correct allocation view laws select
      choices admissible numericChoice vectorChoice growthCompatible apiCompatible publicationCompatible occurrence code store held exec address owner
    function signature functionAt signatureAt args owned results stop resources available
  generalize actual : runtime.interp.invoke_with memory (platform memory floats allocator select) floats allocator exec store () address args results=result at source ⊢
  cases source with
  | ret post=>exact WP.spec.ret post
  | div=>exact False.elim (terminates (native_invoke_chosen_source_diverges memory floats allocator correct allocation view laws select
      choices admissible numericChoice vectorChoice growthCompatible apiCompatible publicationCompatible occurrence code store held exec address owner
      function signature functionAt signatureAt args owned results stop resources available actual))

/-- The combined driver recovers the existing finite checked-action callback implementation exactly.
Its two host-control ticks introduce only history, which the synchronous platform method erases. -/
theorem Theorems.OpenReentrantControl.platform.returning_call_host
    {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view)
    (select : U64 → Slice runtime.Value → CallbackActions.Program)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (token : Unit) (identity : U64) (args defaults : Slice runtime.Value) :
    (platform memory floats allocator (fun identity args=>[.returnAction (select identity args)])).call_host token store identity args defaults=
      (CallbackActions.platform memory allocator select).call_host token store identity args defaults :=
  returning_actions_erases memory floats allocator allocation view laws select code store held token
    identity args defaults

/-- Returning checked-action callbacks run by the driver recover the full world package: ordinary
return, retained code and metadata, source store typing, extern retention and issued results. -/
theorem Theorems.OpenReentrantControl.platform.returning_package
    {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view)
    (select : U64 → Slice runtime.Value → CallbackActions.Program) :
    ReentrantCallbacks.Package
      (platform memory floats allocator (fun identity args=>[.returnAction (select identity args)])) view :=
  returning_actions_package memory floats allocator allocation view laws select

/-- For the returning subclass of the same driver, the original absence-of-source-divergence
invocation contract is recovered: absence of every infinite source run yields an ordinary result
with the full invariant and source correspondence. -/
theorem Theorems.OpenReentrantControl.platform.invoke_returning_terminates {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view)
    (select : U64 → Slice runtime.Value → CallbackActions.Program)
    (code : Store.CodeInterpretation) (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (held : ExecutableInv view code store) (address : runtime.FuncAddr)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (finite : ¬Spec.InfiniteSourceWithEvents initial) :
    runtime.interp.invoke_with memory
      (platform memory floats allocator (fun identity args=>[.returnAction (select identity args)])) floats allocator
      exec store () address args results ⦃answer=>∃afterCode,
        ReturnedWorldEffect view (ExecutableInv view) code store afterCode answer.2.2.1 ∧
        store.externs.length≤answer.2.2.1.externs.length ∧
        ExecutableWorldInvocationOutcome view code store exec () results initial answer⦄ :=
  ReentrantCallbacks.invoke_terminates memory _ floats allocator correct allocation
    (fun _=>WP.spec.ret trivial) view laws
    (returning_actions_package memory floats allocator allocation view laws select)
    code exec store held () address args results issued argumentIssued initial invoked finite

end Exec

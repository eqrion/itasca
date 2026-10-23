import Exec.Theorems.Invocation.PublicExecutableWorldInvocation
import Exec.Theorems.Invocation.PublicExecutableWorldResources
import Exec.Theorems.Invocation.PublicExecutableWorldDivergence
import Exec.Theorems.Invocation.PublicWorldChosenMatches
import Exec.Theorems.Progress.ExecutableWorldFinite

/-!
# Invocation

Guarantees of `runtime.interp.invoke_with` on an issued Wasm or host function handle, in an
evolving world where host callbacks may publish fresh code.

The store starts in the public invariant `Theorems.ExecutableInv` for a ghost code interpretation
`code`, and `fun_invoke` gives the source invocation configuration. The platform and host laws are
the explicit premises of [Contracts](../Contracts.lean): `Platform.FloatOpsCorrect`,
`Platform.AllocCorrect`, normally returning interrupts, `Platform.MemoryLaws`, `HostWorldSound`,
and raw frame, extern and issued-result retention.

- Soundness: `sound`, `recorded_sound` and `recorder_sound` relate every returned value, error and
  final store to a source run, with the actual recorded events.
- Divergence: `diverges` reflects divergence into an infinite source run; `terminates` excludes
  divergence when the source has no infinite run.
- Progress: `finite_progress` bounds the dispatches of a finite prefix by source steps.
- Completeness: `chosen_complete` matches one preselected terminating source run.
-/

open Aeneas Aeneas.Std SpecExt

namespace Exec

open Theorems Interp

/-- Issued public function handles may denote either Wasm or host functions. The actual API checks
retain exact unchanged-state rejection; accepted calls preserve the full invariant with a chosen
final code interpretation and refine source results, errors and store effects. The platform and
host laws are the component-wise fields of `WorldInvocationLaws`. This is partial correctness:
divergence is allowed and characterized by `diverges`. -/
theorem runtime.interp.invoke_with.sound {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ExecutableWorldInvocationOutcome view code store exec platform results initial out ⦄div :=
  invoke_executable_world_issued memory hooks floats allocator correct allocation interrupts view
    laws code sound preserve externs issuedResults exec store platform valid address args results
    issued argumentIssued initial invoked

/-- The canonical public invocation guarantee. Every normal result carries the exact event log of the
transparent recorder `recordedInvokeWith`; the source run uses that same log. The full invariant,
source correspondence and classified resource causes of every error share all witnesses. Divergence
is allowed. -/
theorem runtime.interp.invoke_with.recorded_sound {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∃events,
        recordedInvokeWith memory hooks floats allocator exec store platform address args results []=.ok (out,events) ∧
        ExecutableWorldRecordedOutcome view code store exec platform results initial out events ∧
        ∀error,out.1=.Err error → ExecutableWorldInvocationSourceCause memory hooks floats allocator view code store address args out.2.2.1 error ⦄div :=
  invoke_executable_world_source_resources memory hooks floats allocator correct allocation
    interrupts view laws code sound preserve externs issuedResults exec store platform valid address
    args results issued argumentIssued initial invoked

/-- `recorded_sound` stated for the recording model `recordedInvokeWith` itself, which erases to
`invoke_with`. -/
theorem runtime.interp.invoke_with.recorder_sound {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    recordedInvokeWith memory hooks floats allocator exec store platform address args results []
      ⦃ (out,events) => (ExecutableWorldRecordedOutcome view code store exec platform results initial out events ∧
        ∀error,out.1=.Err error → ExecutableWorldInvocationSourceCause memory hooks floats allocator view code store address args out.2.2.1 error) ⦄div :=
  invoke_executable_world_recorded_resources memory hooks floats allocator correct allocation
    interrupts view laws code sound preserve externs issuedResults exec store platform valid address
    args results issued argumentIssued initial invoked

/-- Actual public invocation divergence has a coherent infinite labeled source execution under the
full API invariant and the explicit callback laws. It does not say the source run is unique. -/
theorem runtime.interp.invoke_with.diverges {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results=.div) :
    Spec.InfiniteSourceWithEvents initial :=
  invoke_executable_world_infinite_source memory hooks floats allocator correct allocation
    interrupts view laws code sound preserve externs issuedResults exec store platform valid address
    args results issued argumentIssued initial invoked divergent

/-- Absence of every infinite source run yields an ordinary API result with its actual recorded trace
and full retained invariant. The result may be a Rust error (including exhaustion or
interruption); this is neither successful return completeness nor termination from existence of
one finite source run. Returning callbacks and the other platform laws remain explicit premises. -/
theorem runtime.interp.invoke_with.terminates {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (finite : ¬ Spec.InfiniteSourceWithEvents initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∃ events,
        recordedInvokeWith memory hooks floats allocator exec store platform address args results [] = .ok (out, events) ∧
        ExecutableWorldRecordedOutcome view code store exec platform results initial out events ⦄ :=
  invoke_executable_world_terminates memory hooks floats allocator correct allocation interrupts
    view laws code sound preserve externs issuedResults exec store platform valid address args
    results issued argumentIssued initial invoked finite

/-- Complete-profile actual finite dispatch progress, including host calls and reentrant
publication: every finite prefix of the dispatch loop of `invoke_with` (`Interp.executionBody`)
from a world machine with the public invariant makes source progress. The uniform constant is
independent of the initial or future source-store size. Conditional callback retention laws remain
explicit. -/
theorem runtime.interp.invoke_with.finite_progress {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    {expected : List valtype} (dispatches : Nat)
    (initial : EventfulWorld M P view expected)
    (valid : ExecutableInv view initial.code initial.machine.store) (last : ExecutionState M P)
    (trace : ContinuingTrace (executionBody memory hooks floats allocator) dispatches
      (initial.machine.exec,initial.machine.store,initial.machine.platform,.Ok ()) last) :
    ∃previous events count, Spec.StepsHN count (Abs.decode initial.machine.source) events (Abs.decode previous) ∧
      dispatches / (2 * U32.max + 3) ≤ count :=
  executable_world_finite_progress memory hooks floats allocator correct allocation interrupts view
    laws sound preserve externs issuedResults dispatches initial valid last trace

/-- Corresponding-outcome completeness for both complete profiles and issued Wasm/host functions.
Source capacities and primitive platform/callback compatibility exclude resource errors; recorder
events and final stores match one preselected terminating source run. Interrupts must continue,
and callbacks must not report stack exhaustion. It does not assert global source-step
determinism. -/
theorem runtime.interp.invoke_with.chosen_complete {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice)
    {M P F A : Type} {valueLimit frameLimit : Nat}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p,hooks.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (sound : HostWorldChosenSound memory hooks view (ExecutableResourceInv view valueLimit frameLimit) choices)
    (preserve : ∀code store,ExecutableResourceInv view valueLimit frameLimit code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀code store,ExecutableResourceInv view valueLimit frameLimit code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀code store,ExecutableResourceInv view valueLimit frameLimit code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableResourceInv view valueLimit frameLimit code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store=store.id) (issued : Store.ExternalIssued store (.Func address))
    (owned : ∀ value∈args.val,Store.ValueInStore store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (sourceFunction : funcinst) (params resultsTypes : List valtype)
    (sourceAt : (Store.decodeStore view code store).FUNCS[address.index.val]?=some sourceFunction)
    (sourceType : sourceFunction.TYPE=.mk_functype (.mk_list params) (.mk_list resultsTypes))
    (typedArguments : ResultsTyped (Store.decodeStore view code store) params (args.val.map sourceValue))

    {events : List HostEvent} {target : config}
    (run : Spec.ChoiceSteps choices 0 initial events target) (terminal : Spec.SourceTerminal target)
    (signatureFits : signatureWords sourceFunction.TYPE≤valueLimit)
    (entryCapacity : ∀words,SourceCanonicalFunctionCapacity (Store.decodeStore view code store) address.index.val words → words≤valueLimit)
    (positiveFrames : 0<frameLimit)
    (resources : ChosenWorldResources choices 0 initial valueLimit frameLimit)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (noOverflow : NoHostStackOverflow hooks (ExecutableResourceInv view valueLimit frameLimit)) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∃afterCode,ExecutableResourceInv view valueLimit frameLimit afterCode out.2.2.1 ∧
        Store_ok (Store.decodeStore view afterCode out.2.2.1) ∧ FrameStorePrefix store out.2.2.1 ∧
        Store.CodeAgreesOn store code afterCode ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
        recordedInvokeWith memory hooks floats allocator exec store platform address args results []=.ok (out,events) ∧
        match out.1 with
        | .Ok _ => target=⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩ ∧
            (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value)
        | .Err (.Trap _) => target=⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,[.TRAP]⟩
        | .Err _ => False ⦄ :=
  invoke_executable_world_chosen_matches admissible numericChoice vector memory hooks floats
    allocator correct allocation interrupts view laws code compatible sound preserve externs
    issuedResults exec store platform valid address args results owner issued owned initial invoked
    sourceFunction params resultsTypes sourceAt sourceType typedArguments run terminal signatureFits
    entryCapacity positiveFrames resources available continuing noOverflow

end Exec

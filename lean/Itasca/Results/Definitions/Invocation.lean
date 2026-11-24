import Itasca.Generated.FunsInterp
import Itasca.Results.Definitions.Host
import Itasca.Results.Definitions.Resources

/-!
# Invocation behavior and resource completeness

Read argument typing, returned outcomes and divergence behavior first. The
operation laws then connect those meanings to invoke_with. Resource sufficiency
is separate from termination; combining them excludes exhaustion and interruption
while permitting successful return or a source trap.
-/

section InvocationArguments

/-!
## Source argument typing

Invocation arguments have the parameter types of the selected source function.
-/

namespace Itasca.Integration

open Aeneas Aeneas.Std SpecExt Itasca.Interp Itasca.Spec

/-- The arguments of a source invocation have the parameter types of its callee. -/
def InvocationArgumentsTyped (store : _root_.store) (address : funcaddr) (args : List val) : Prop :=
  ∀ function params results,store.FUNCS[address]?=some function →
    function.TYPE=.mk_functype (.mk_list params) (.mk_list results) → ResultsTyped store params args

end Itasca.Integration

end InvocationArguments

namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Representation Itasca.Interp Itasca.Store

/-- Every returned invocation preserves the store predicate, old code meanings
and identities, and reaches the decoded final store with the actual host events.
The result then selects exactly one case:

* Success reaches the returned source values and returns owned values.
* Wrong-store or argument rejection requires invalid inputs, changes no API state,
  and emits no host events.
* A trap reaches a source trap; the concrete trap reason is not classified here.
* Exhaustion or interruption may stop at the reachable store established above.
* Link and internal errors are impossible.

One final code interpretation governs all preservation and source-run facts.
Termination and resource sufficiency are separate guarantees. -/
def InvocationOutcome {M P : Type}
    (view : M → Slice U8)
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop) (code : Representation.CodeInterpretation) (before : runtime.store.Store M)
    (exec : runtime.interp.Execution) (platform : P) (address : runtime.FuncAddr)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (initial : config)
    (result : core.result.Result Unit runtime.ExecError) (execution : runtime.interp.Execution)
    (after : runtime.store.Store M) (nextPlatform : P) (returned : alloc.vec.Vec runtime.Value)
    (events : List HostEvent) : Prop :=
  ∃ afterCode, Store.CodeAgreesOn before code afterCode ∧
  Inv afterCode after ∧ Store.MetadataExtended before after ∧
  Extend_store (Representation.decodeStore view code before) (Representation.decodeStore view afterCode after) ∧
  (∃body,StepsH initial events ⟨⟨Representation.decodeStore view afterCode after,Spec.invocationFrame⟩,body⟩) ∧
  match result with
  | .Ok () =>
    StepsH initial events
      ⟨⟨decodeStore view afterCode after,Spec.invocationFrame⟩,vals (returned.val.map sourceValue)⟩ ∧
      ∀ value ∈ returned.val, Store.ValueInStore after value
  | .Err .WrongStore | .Err .BadArguments =>
    ¬ (address.store = before.id ∧ (∀ value ∈ args.val, Store.ValueInStore before value) ∧
      InvocationArgumentsTyped (decodeStore view code before) address.index.val (args.val.map sourceValue)) ∧
    (result,execution,after,nextPlatform,returned) = (result,exec,before,platform,results) ∧ events = []
  | .Err (.Trap _) =>
    StepsH initial events ⟨⟨decodeStore view afterCode after,Spec.invocationFrame⟩,[.TRAP]⟩
  | .Err (.Exhausted _) | .Err .Terminated => True
  | .Err (.Link _) | .Err .Internal => False

/-- Execute the actual extracted interpreter with a transparent callback observer.
On return, every completed callback matches one source event in order, including
host traps and rejected replies. The observer forwards the same platform state
and store effects; its log does not select bytecode call sites or reconstruct
arguments from interpreter scratch buffers. Source events supply Wasm addresses,
which may alias the same observed host identity.

The source outcome describes the original result and its retained effects.
Divergence reflects an infinite source run or a reachable diverging callback. -/
def InvocationBehavior {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8)
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop) (code : Representation.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (initial : config)
    (outcome : Result (core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P × alloc.vec.Vec runtime.Value)) : Prop :=
  outcome ⦃ (result, execution, after, nextPlatform, returned) => ∃ observations events,
    runtime.interp.invoke_with memory (Platform.observing hooks) floats allocator exec store
      (platform,[]) address args results = .ok (result,execution,after,(nextPlatform,observations),returned) ∧
    List.Forall₂ Platform.HostObservation.Matches observations events ∧
    InvocationOutcome view Inv code store exec platform address args results initial result execution after nextPlatform returned events ⦄div ∧
  (outcome = .div → Spec.InfiniteSourceWithEvents initial ∨ HostCallDiverged hooks view initial)

end Itasca.Integration


namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Representation Itasca.Interp Itasca.Store

/-- Issued public function handles may denote either Wasm or host functions. Every returned result
  carries actual callback exchanges observed by `Platform.observing`, matched in order to
  the events of a source run. The API checks reject with the store unchanged; accepted calls preserve the full
  invariant with a final code interpretation and refine source results, errors and store effects, and
  permit resource exhaustion or interruption at a reachable source state. Divergence is an infinite source run, or a source run
  reaches a store on which a callback diverges; it does not say the source run is unique. -/
def InvocationLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ {P F A : Type}
  (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
  (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
  (_platform_laws : Platform.Laws memory hooks floats allocator view) (code : Representation.CodeInterpretation)
  (_host_laws : HostLaws hooks view (Inv))
  (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
  (_store_invariant : Inv code store)
  (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
  (_function_issued : Store.ExternalIssued store (.Func address))
  (_arguments_issued : ∀value∈args.val,Store.IssuedValue store value)
  (initial : config)
  (_source_invocation : fun_invoke (Representation.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) ,
  InvocationBehavior memory hooks floats allocator view Inv code exec store platform address args results initial
    (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results)

/-- Embedding availability for resource completeness. These laws quantify over
all admitted callback invocations: callbacks keep the limits, allocations are
granted, interrupts continue, and hosts do not report their own stack exhaustion.
They do not assert success of the interpreter being verified. -/
structure ResourceAvailability {M P A : Type}
    (hooks : runtime.platform.Platform P M) (allocator : runtime.platform.Alloc A)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop where
  limits : ∀ code store, Inv code store → ∀ host p args defaults result nextPlatform after returned,
    hooks.call_host p store host args defaults = .ok (result, nextPlatform, after, returned) →
    after.limits = store.limits
  /-- Every modeled allocation request is granted. This is an embedding
  assumption, separate from the source storage and call-depth bounds. -/
  allocations : ∀ (T : Type) (values : alloc.vec.Vec T) (additional : Usize),
    allocator.reserve values additional = .ok (true, values)
  interrupts : ∀ before after, hooks.interrupt before ≠ .ok (.Terminate, after)
  hosts : ∀ code store, Inv code store → ∀ p identity args defaults nextPlatform after returned,
    hooks.call_host p store identity args defaults ≠
      .ok (.Err .StackOverflow, nextPlatform, after, returned)

/-- Within conservative source budgets and with available embedding resources,
a well-typed owned invocation can only succeed, trap, or diverge. Resource errors,
interruption and API argument rejection are excluded. Termination remains the
separate source/host termination obligation of `InvocationLaw`. -/
def InvocationResourceLaw {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ {P F A : Type}
  (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
  (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
  (_platform_laws : Platform.Laws memory hooks floats allocator view)
  (code : CodeInterpretation) (_host_laws : HostLaws hooks view Inv)
  (_available : ResourceAvailability hooks allocator Inv)
  (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
  (_store_invariant : Inv code store)
  (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
  (_owner : address.store = store.id) (_issued : Store.ExternalIssued store (.Func address))
  (_arguments : ∀ value ∈ args.val, Store.ValueInStore store value)
  (initial : config)
  (_invocation : fun_invoke (decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
  (_typed : InvocationArgumentsTyped (decodeStore view code store) address.index.val (args.val.map sourceValue))
  (calleeWords : Nat)
  (_budget : Spec.Resources.Fits (decodeStore view code store) initial calleeWords
    store.limits.max_values.val store.limits.max_frames.val),
  runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
    ⦃ (result, _, _, _, _) => ∀ error, result = .Err error → ∃ trap, error = .Trap trap ⦄div


end Itasca.Integration

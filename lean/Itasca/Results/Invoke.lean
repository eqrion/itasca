import Itasca.Results.Definitions.Runtime
import Itasca.Runtime.Integration.RuntimeContract

open Itasca.Representation

/-!
# Invocation

Guarantees of `runtime.interp.invoke_with` on an issued Wasm or host function handle, in an
evolving world where host callbacks may publish fresh code.

The store starts in the chosen predicate of `Integration.RuntimeContract` for a ghost code interpretation
`code`, and `fun_invoke` gives the source invocation configuration. The platform and host laws are
the contracts `Platform.Laws` in [Platform](Definitions/Platform.lean) and `HostLaws`
in [Host laws](Definitions/Host.lean).

`behaves` relates the actual callback log and final store to source execution.
`InvocationOutcome` states the returned cases directly:

| Result | Guarantee |
| --- | --- |
| Success | The source reaches the returned values; returned references are owned. |
| Wrong store / bad arguments | Inputs fail ownership or source typing; all API state is unchanged and no callback occurs. |
| Trap | The source reaches a trap with the same final store and host events. |
| Exhaustion / interruption | The final store and host events are source reachable. |
| Link / internal error | Impossible under the theorem premises. |
| Divergence | An infinite source run exists, or a source-reachable callback can diverge. |

Every returned case preserves the store predicate and existing code meanings
and identities. The trap guarantee does not classify the concrete trap reason.

`terminates` excludes divergence when every source run is finite and reachable
callbacks return. It still permits ordinary errors. `resource_complete` excludes
resource errors and interruption under owned, source-typed inputs, source budgets
and embedding availability; it still permits divergence and source traps.
Together the two laws yield normal return with success or a source trap.
-/

open Aeneas Aeneas.Std SpecExt

namespace Itasca

open Integration Interp

/-- Issued public function handles may denote either Wasm or host functions. Every returned result
carries the actual callback exchanges observed by `Platform.observing`, matched in order to
the host events of a source run. The extracted interpreter itself supplies the execution. The API checks reject with the store unchanged; accepted calls preserve the full
invariant with a final code interpretation and refine source results, errors and store effects, and
resource exhaustion or interruption retains a reachable source store. Divergence is an infinite source run, or a source run
reaches a store on which a callback diverges; it does not say the source run is unique. -/
theorem Interp.invoke_with.behaves {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : InvocationContract view Inv)
    (platform_laws : Platform.Laws memory hooks floats allocator view)
    (code : CodeInterpretation)
    (host_laws : HostLaws hooks view Inv)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (store_invariant : Inv code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (function_issued : Store.ExternalIssued store (.Func address))
    (arguments_issued : ∀ value ∈ args.val, Store.IssuedValue store value)
    (initial : config)
    (source_invocation : fun_invoke (decodeStore view code store)
      address.index.val (args.val.map sourceValue) initial) :
    InvocationBehavior memory hooks floats allocator view Inv code exec store platform address args results initial
      (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results) :=
  contract.behaves memory hooks floats allocator platform_laws code host_laws exec store platform store_invariant address args results function_issued arguments_issued initial source_invocation

/-- Absence of every infinite source run and of every reachable diverging callback yields an
ordinary API result with the guarantees of `behaves`. The result may be a Rust error (including exhaustion or interruption); this is neither
successful return completeness nor termination from existence of one finite source run. -/
theorem Interp.invoke_with.terminates {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : InvocationContract view Inv)
    (platform_laws : Platform.Laws memory hooks floats allocator view)
    (code : CodeInterpretation)
    (host_laws : HostLaws hooks view Inv)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (store_invariant : Inv code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (function_issued : Store.ExternalIssued store (.Func address))
    (arguments_issued : ∀ value ∈ args.val, Store.IssuedValue store value)
    (initial : config)
    (source_invocation : fun_invoke (decodeStore view code store)
      address.index.val (args.val.map sourceValue) initial)
    (no_infinite_run : ¬ Spec.InfiniteSourceWithEvents initial)
    (callbacks_return : ¬ HostCallDiverged hooks view initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ (result, execution, after, nextPlatform, returned) => ∃ observations events,
        runtime.interp.invoke_with memory (Platform.observing hooks) floats allocator exec store
          (platform,[]) address args results = .ok (result,execution,after,(nextPlatform,observations),returned) ∧
        List.Forall₂ Platform.HostObservation.Matches observations events ∧
        InvocationOutcome view Inv code store exec platform address args results initial result execution after nextPlatform returned events ⦄ :=
  (Interp.invoke_with.behaves memory hooks floats allocator view Inv contract platform_laws code host_laws exec store platform
    store_invariant address args results function_issued arguments_issued initial source_invocation).returns no_infinite_run callbacks_return

/-- Sufficient source budgets and embedding availability exclude resource errors
and interruption. Owned, source-typed calls return success or a source trap, or
may diverge. Combine this law with `terminates` to obtain normal return with no
resource failure. The complete premises are stated once in `InvocationResourceLaw`. -/
theorem Interp.invoke_with.resource_complete {M : Type} (view : M → Slice U8)
    (Inv : CodeInterpretation → runtime.store.Store M → Prop)
    (contract : InvocationResourceContract view Inv) : InvocationResourceLaw view Inv :=
  contract.resource_complete

end Itasca

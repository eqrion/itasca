import Itasca.Runtime.Theorems.Invocation.PublicBehaves
import Itasca.Runtime.Theorems.Invocation.PublicNoSpuriousErrors

/-!
# Invocation

Guarantees of `runtime.interp.invoke_with` on an issued Wasm or host function handle, in an
evolving world where host callbacks may publish fresh code.

The store starts in the public invariant `Theorems.ExecutableInv` for a ghost code interpretation
`code`, and `fun_invoke` gives the source invocation configuration. The platform and host laws are
the bundles `Platform.Laws` and `HostLaws` of [Contracts](../Runtime/Contracts.lean).

- Behavior: `behaves` relates every returned value, error and final store to a source run with the
  actual recorded events, and reflects divergence into an infinite source run or a reachable store
  on which a callback diverges (`HostCallDiverged`). `terminates` excludes divergence when neither
  exists.
- Completeness: `no_spurious_errors` reports only traps when every source run fits the store
  limits and the platform grants resources.
-/

open Aeneas Aeneas.Std SpecExt

namespace Itasca.Runtime

open Theorems Interp

/-- Issued public function handles may denote either Wasm or host functions. Every returned result
carries the exact event log of the transparent recorder `recordedInvokeWith`, and the source run
uses that same log. The API checks reject with the store unchanged; accepted calls preserve the full
invariant with a final code interpretation and refine source results, errors and store effects, and
every resource error has a classified cause. Divergence is an infinite source run, or a source run
reaches a store on which a callback diverges; it does not say the source run is unique. -/
theorem runtime.interp.invoke_with.behaves {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
    (callbacks : HostLaws hooks view (ExecutableInv view))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    InvocationBehaves memory hooks floats allocator view code exec store platform address args results initial
      (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results) :=
  invoke_executable_world_behaves memory hooks floats allocator view laws code callbacks exec store platform
    valid address args results issued argumentIssued initial invoked

/-- Absence of every infinite source run and of every reachable diverging callback yields an
ordinary API result with the guarantees of `behaves`. The result may be a Rust error (including exhaustion or interruption); this is neither
successful return completeness nor termination from existence of one finite source run. -/
theorem runtime.interp.invoke_with.terminates {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
    (callbacks : HostLaws hooks view (ExecutableInv view))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (finite : ¬ Spec.InfiniteSourceWithEvents initial)
    (callbacksReturn : ¬ HostCallDiverged hooks view initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∃ events,
        recordedInvokeWith memory hooks floats allocator exec store platform address args results [] = .ok (out, events) ∧
        ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial out events ∧
        ∀ error, out.1 = .Err error → ExecutableWorldInvocationSourceCause memory hooks floats allocator view
          (ExecutableInv view) code store address args out.2.2.1 error ⦄ :=
  (runtime.interp.invoke_with.behaves memory hooks floats allocator view laws code callbacks exec store platform
    valid address args results issued argumentIssued initial invoked).returns finite callbacksReturn

/-- An owned, typed call reports only traps when every source run of the invocation fits the
store's value and frame limits (`SourceResourcesFit`, over all typed host replies), the allocator
grants every request, interrupts continue and callbacks keep the store limits and never report
stack overflow. Divergence is allowed; `terminates` excludes it. -/
theorem runtime.interp.invoke_with.no_spurious_errors {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
    (callbacks : HostLaws hooks view (ExecutableInv view))
    (limitsKept : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → answer.2.2.1.limits=store.limits)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store=store.id) (issued : Store.ExternalIssued store (.Func address))
    (owned : ∀value∈args.val,Store.ValueInStore store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (typedArguments : InvocationArgumentsTyped (Store.decodeStore view code store) address.index.val (args.val.map sourceValue))
    (fits : SourceResourcesFit (Store.decodeStore view code store) address.index.val initial
      store.limits.max_values.val store.limits.max_frames.val)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (noOverflow : NoHostStackOverflow hooks (ExecutableInv view)) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∀error,out.1=.Err error → ∃trap,error=.Trap trap ⦄div :=
  invoke_executable_world_no_spurious_errors memory hooks floats allocator view laws code callbacks limitsKept exec store platform valid address args
    results owner issued owned initial invoked typedArguments fits available continuing noOverflow

end Itasca.Runtime

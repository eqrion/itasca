import Exec.Theorems.Host.Open.Completeness.ReturningRecovery

/-!
# Host driver

Guarantees of the certified synchronous host driver `Theorems.OpenReentrantControl`: its entry
`invoke`, and `runtime.interp.invoke_with` run with the driver as its `platform`. Callbacks are
Lean programs over a checked action language (`Selector`), so these results cover unbounded
reentrancy and code publication against one combined Wasm/host source semantics.

The callbacks are Lean models of the interface: arbitrary Rust callbacks still need a refinement
contract, and concrete publication covers modules with empty imports and no start function.
-/

open Aeneas Aeneas.Std SpecExt

namespace Exec

open Theorems Theorems.OpenReentrantControl Interp Interp.OpenCall

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

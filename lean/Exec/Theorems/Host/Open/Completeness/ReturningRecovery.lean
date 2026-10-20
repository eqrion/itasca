import Exec.Theorems.Host.Open.Driver.ReentrantControl
import Exec.Theorems.Host.Reentrant.ReentrantPackage
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- The combined driver recovers the existing finite checked-action callback
implementation exactly. Its two host-control ticks introduce only history,
which the synchronous Platform method erases. -/
theorem returning_actions_erases {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view)
    (select : U64 → Slice runtime.Value → CallbackActions.Program)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (token : Unit) (identity : U64) (args defaults : Slice runtime.Value) :
    (platform memory floats allocator (fun identity args=>[.returnAction (select identity args)])).call_host token store identity args defaults=
      (CallbackActions.platform memory allocator select).call_host token store identity args defaults := by
  cases token
  obtain ⟨answer,actual,effect,issued⟩:=WP.spec_imp_exists
    ((select identity args).correct memory allocator allocation view laws code store held)
  rcases answer with ⟨status,after,values⟩
  unfold platform run CallbackActions.platform
  dsimp only
  rw [loop.eq_def]
  simp only [tick,initialHost,List.getElem?_cons_zero,actual,bind_ok]
  rw [loop.eq_def]
  simp only [tick,bind_ok]

/-- Returning checked-action callbacks recover the full stage-4 world package
from their implementations: ordinary return, retained code/metadata, source
store typing, extern retention and issued results. -/
theorem returning_actions_package {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view)
    (select : U64 → Slice runtime.Value → CallbackActions.Program) :
    ReentrantCallbacks.Package
      (platform memory floats allocator (fun identity args=>[.returnAction (select identity args)])) view := by
  intro code store held token identity args defaults
  rw [returning_actions_erases memory floats allocator allocation view laws select code store held token identity args defaults]
  exact ReentrantCallbacks.actions_package memory allocator allocation select view laws code store held token identity args defaults

/-- The original source-absence-of-divergence invocation contract is recovered
for this returning subclass of the same combined driver. -/
theorem invoke_returning_actions_terminates {M F A : Type}
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
        ExecutableWorldInvocationOutcome view code store exec () results initial answer⦄ := by
  exact ReentrantCallbacks.invoke_terminates memory _ floats allocator correct allocation
    (fun token=>WP.spec.ret trivial) view laws
    (returning_actions_package memory floats allocator allocation view laws select)
    code exec store held () address args results issued argumentIssued initial invoked finite
end Exec.Theorems.OpenReentrantControl

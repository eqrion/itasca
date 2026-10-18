import Exec.Theorems.Api.RecordedInvTotal
import Exec.Theorems.Composition.Recorded.RecordedLoopResult
import Exec.Theorems.Api.ExecutableInv
import Exec.Interp.StructuredMachine.ExecutableCoverage
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- Complete-profile interpreter-loop safety including host callbacks, under
explicit source host laws plus raw metadata/namespace retention and issued
callback values. These extra premises are not inferred from `HostSound`. -/
theorem executable_recorded_loop_results
    {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : Platform.HostSound hooks (ExecutableInv view code) (Store.decodeStore view code))
    (preserve : ∀ store, ExecutableInv view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ store, ExecutableInv view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ store, ExecutableInv view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    {expected : List valtype}
    (initial : EventfulMachine Interp.Executable.emission Abs.ExecutableInstr M P view code expected)
    (valid : ExecutableInv view code initial.store) :
    runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ result => ExecutableInv view code result.2.2.2.2.2.1 ∧
        RecordedLoopResult memory hooks floats allocator initial result ⦄div :=
  recorded_inv_loop_results memory hooks floats allocator (ExecutableInv view code)
    (recorded_inv_step_outcomes Abs.executable_language memory hooks floats allocator correct allocation interrupts view laws code
      (ExecutableInv view code) (fun _ held=>held.toCertifiedApiStore.toCertifiedSupportedStore)
      (fun _ _ held mutation=>held.update mutation) sound preserve externs issued expected) initial valid
end Exec.Theorems

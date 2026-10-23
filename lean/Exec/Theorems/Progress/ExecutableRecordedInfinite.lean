import Exec.Theorems.Composition.Executable.ExecutableRecordedLoop
import Exec.Theorems.Progress.RecordedInfinite
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
theorem executable_recorded_loop_prefixes
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
    (valid : ExecutableInv view code initial.store)
    (divergent : runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())=.div) :
    ∃ (states : Nat → EventfulMachine Interp.Executable.emission Abs.ExecutableInstr M P view code expected) (events : Nat → List HostEvent),
      states 0=initial ∧
      (∀n,ExecutableInv view code (states n).store ∧ RecordedEventfulTransition memory hooks floats allocator (states n) (events n) (states (n+1))) ∧
      (∀n,runtime.interp.invoke_with_loop1 memory hooks floats allocator (states n).exec (states n).store (states n).platform (.Ok ())=.div) ∧
      (∀n prior,recordedSteps memory hooks floats allocator n initial.exec initial.store initial.platform prior=
        .ok ((.Ok (),(states n).exec,(states n).store,(states n).platform),prior++recordedPrefixEvents events n)) ∧
      (∀n,∃count,Spec.StepsHN count (Abs.decode initial.source) (recordedPrefixEvents events n) (Abs.decode (states n).source)) :=
  recorded_inv_loop_prefixes memory hooks floats allocator (ExecutableInv view code)
    (recorded_inv_step_outcomes Abs.executable_language memory hooks floats allocator correct allocation interrupts view laws code
      (ExecutableInv view code) (fun _ held=>held.toCertifiedApiStore.toCertifiedSupportedStore)
      (fun _ _ held mutation=>held.update mutation) sound preserve externs issued expected) initial valid divergent
end Exec.Theorems

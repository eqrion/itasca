import Exec.Theorems.Composition.Executable.ExecutableWorldLoop
import Exec.Theorems.Composition.World.WorldRecordedPrefixes
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
theorem executable_world_loop_recorded_prefixes
    {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀ code store, ExecutableInv view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ code store, ExecutableInv view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ code store, ExecutableInv view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    {expected : List valtype}
    (initial : EventfulWorld Interp.Executable.emission Abs.ExecutableInstr M P view expected)
    (valid : ExecutableInv view initial.code initial.machine.store)
    (divergent : runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())=.div) :
    ∃ (states : Nat → EventfulWorld Interp.Executable.emission Abs.ExecutableInstr M P view expected) (events : Nat → List HostEvent),
      states 0=initial ∧
      (∀n,ExecutableInv view (states n).code (states n).machine.store ∧ WorldRecordedTransition memory hooks floats allocator (states n) (events n) (states (n+1))) ∧
      (∀n,runtime.interp.invoke_with_loop1 memory hooks floats allocator (states n).machine.exec (states n).machine.store (states n).machine.platform (.Ok ())=.div) ∧
      (∀n prior,recordedSteps memory hooks floats allocator n initial.machine.exec initial.machine.store initial.machine.platform prior=
        .ok ((.Ok (),(states n).machine.exec,(states n).machine.store,(states n).machine.platform),prior++recordedPrefixEvents events n)) ∧
      (∀n,∃count,Spec.StepsHN count (Abs.decode initial.machine.source) (recordedPrefixEvents events n) (Abs.decode (states n).machine.source)) :=
  world_loop_recorded_prefixes memory hooks floats allocator (ExecutableInv view)
    (world_step_outcomes Abs.executable_language memory hooks floats allocator correct allocation interrupts view laws
      (ExecutableInv view) (fun _ _ held=>held.toCertifiedApiStore.toCertifiedSupportedStore)
      (fun _ _ _ held mutation=>held.update mutation) sound preserve externs issued expected) initial valid divergent
end Exec.Theorems

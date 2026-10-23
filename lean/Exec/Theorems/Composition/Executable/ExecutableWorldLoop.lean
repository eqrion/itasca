import Exec.Theorems.Composition.Eventful.EventfulWorldTotal
import Exec.Theorems.Progress.EventfulWorldInfinite
import Exec.Theorems.Api.ExecutableInv
import Exec.Interp.StructuredMachine.ExecutableCoverage
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- Complete-profile interpreter-loop safety including host callbacks, under
explicit source host laws plus raw metadata/namespace retention and issued
callback values. These extra premises are not inferred from `HostSound`. -/
theorem executable_world_loop_results
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
    (valid : ExecutableInv view initial.code initial.machine.store) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())
      ⦃ result => WorldLoopResult (ExecutableInv view) initial result ⦄div := by
  apply WP.dspec_mono (world_loop_results memory hooks floats allocator (ExecutableInv view)
    (world_step_outcomes Abs.executable_language memory hooks floats allocator correct allocation interrupts view laws
      (ExecutableInv view) (fun _ _ held=>held.toCertifiedApiStore.toCertifiedSupportedStore)
      (fun _ _ _ held mutation=>held.update mutation) sound preserve externs issued expected) initial valid)
  intro result outcome
  exact outcome.1
theorem executable_world_loop_infinite
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
    Spec.InfiniteSourceWithEvents (Abs.decode initial.machine.source) :=
  world_loop_infinite memory hooks floats allocator (ExecutableInv view)
    (world_step_outcomes Abs.executable_language memory hooks floats allocator correct allocation interrupts view laws
      (ExecutableInv view) (fun _ _ held=>held.toCertifiedApiStore.toCertifiedSupportedStore)
      (fun _ _ _ held mutation=>held.update mutation) sound preserve externs issued expected) initial valid divergent
end Exec.Theorems

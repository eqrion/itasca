import Exec.Theorems.Composition.Eventful.EventfulTotal
import Exec.Theorems.Composition.Certified.CertifiedExecutable
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- Complete-profile interpreter-loop safety including host callbacks, under
explicit source host laws plus raw metadata/namespace retention and issued
callback values. These extra premises are not inferred from `HostSound`. -/
theorem executable_eventful_loop_safe
    {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : Platform.HostSound hooks (CertifiedExecutableStore view code) (Store.decodeStore view code))
    (preserve : ∀ store, CertifiedExecutableStore view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ store, CertifiedExecutableStore view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ store, CertifiedExecutableStore view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    {expected : List valtype}
    (initial : EventfulMachine Interp.Executable.emission Abs.ExecutableInstr M P view code expected) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ _ => True ⦄div :=
  eventful_loop_safe memory hooks floats allocator
    (eventful_step_total Abs.executable_language memory hooks floats allocator correct allocation interrupts view laws code sound preserve externs issued expected) initial

/-- Divergence of the actual complete-profile interpreter loop yields a
coherent infinite source execution with host-event labels. There is no
host-free premise or assumed per-step simulation in this statement. -/
theorem executable_eventful_loop_infinite
    {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : Platform.HostSound hooks (CertifiedExecutableStore view code) (Store.decodeStore view code))
    (preserve : ∀ store, CertifiedExecutableStore view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ store, CertifiedExecutableStore view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ store, CertifiedExecutableStore view code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    {expected : List valtype}
    (initial : EventfulMachine Interp.Executable.emission Abs.ExecutableInstr M P view code expected)
    (divergent : runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())=.div) :
    Spec.InfiniteSourceWithEvents (Abs.decode initial.source) :=
  eventful_loop_infinite memory hooks floats allocator
    (eventful_step_total Abs.executable_language memory hooks floats allocator correct allocation interrupts view laws code sound preserve externs issued expected) initial divergent
end Exec.Theorems

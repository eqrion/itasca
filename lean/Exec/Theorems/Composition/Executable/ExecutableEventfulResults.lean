import Exec.Theorems.Composition.Eventful.EventfulLoopOutcomes
import Exec.Theorems.Composition.Certified.CertifiedExecutable
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- The actual complete-profile loop refines finite source results and errors,
including retained callback store effects, under the explicit callback laws.
No host-free or assumed per-dispatch simulation premise is required. -/
theorem executable_eventful_loop_results
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
      ⦃ result => EventfulLoopResult initial result ⦄div :=
  eventful_loop_results memory hooks floats allocator
    (eventful_step_outcomes Abs.executable_language memory hooks floats allocator correct allocation interrupts view laws code sound preserve externs issued expected) initial
end Exec.Theorems

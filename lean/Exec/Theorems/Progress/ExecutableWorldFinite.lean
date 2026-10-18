import Exec.Theorems.Composition.Uniform.UniformWorldTotal
import Exec.Theorems.Api.ExecutableInv
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- Complete-profile actual finite dispatch progress, including host calls and
reentrant publication. The uniform constant is independent of the initial or
future source-store size. Conditional callback retention laws remain explicit. -/
theorem executable_world_finite_progress {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    {expected : List valtype} (dispatches : Nat)
    (initial : EventfulWorld Interp.Executable.emission Abs.ExecutableInstr M P view expected)
    (valid : ExecutableInv view initial.code initial.machine.store) (last : ExecutionState M P)
    (trace : ContinuingTrace (executionBody memory hooks floats allocator) dispatches
      (initial.machine.exec,initial.machine.store,initial.machine.platform,.Ok ()) last) :
    ∃previous events count, Spec.StepsHN count (Abs.decode initial.machine.source) events (Abs.decode previous) ∧
      dispatches / (2 * U32.max + 3) ≤ count := by
  apply uniform_world_finite_progress memory hooks floats allocator (ExecutableInv view) ?_ dispatches initial valid last trace
  exact uniform_world_step_total Abs.executable_language memory hooks floats allocator correct allocation interrupts view laws
    (ExecutableInv view) (fun _ _ held => held.toCertifiedApiStore.toCertifiedSupportedStore) (fun _ _ _ held mutation => held.update mutation)
    sound preserve externs issuedResults expected
end Exec.Theorems

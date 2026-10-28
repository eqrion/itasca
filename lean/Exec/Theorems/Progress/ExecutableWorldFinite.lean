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
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view)
    (callbacks : HostLaws hooks view (ExecutableInv view))
    {expected : List valtype} (dispatches : Nat)
    (initial : EventfulWorld M P view expected)
    (valid : ExecutableInv view initial.code initial.machine.store) (last : ExecutionState M P)
    (trace : ContinuingTrace (executionBody memory hooks floats allocator) dispatches
      (initial.machine.exec,initial.machine.store,initial.machine.platform,.Ok ()) last) :
    ∃previous events count, Spec.StepsHN count (Abs.decode initial.machine.source) events (Abs.decode previous) ∧
      dispatches / (2 * U32.max + 3) ≤ count := by
  apply uniform_world_finite_progress memory hooks floats allocator (ExecutableInv view) ?_ dispatches initial valid last trace
  exact uniform_world_step_total memory hooks floats allocator view laws
    (ExecutableInv view) (fun _ _ held => held.toCertifiedApiStore.toCertifiedSupportedStore) (fun _ _ _ held mutation => held.update mutation)
    callbacks expected
end Exec.Theorems

import Exec.Theorems.Composition.Uniform.UniformEventfulTotal
import Exec.Theorems.Api.ExecutableInv
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- Complete-profile actual finite dispatch progress, including host calls and
reentrant publication. The uniform constant is independent of the initial or
future source-store size. Conditional callback retention laws remain explicit. -/
theorem executable_eventful_finite_progress {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : Platform.HostSound hooks (ExecutableInv view code) (Store.decodeStore view code))
    (preserve : ∀store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    {expected : List valtype} (dispatches : Nat)
    (initial : EventfulMachine Interp.Executable.emission Abs.ExecutableInstr M P view code expected)
    (valid : ExecutableInv view code initial.store) (last : ExecutionState M P)
    (trace : ContinuingTrace (executionBody memory hooks floats allocator) dispatches
      (initial.exec,initial.store,initial.platform,.Ok ()) last) :
    ∃previous events count, Spec.StepsHN count (Abs.decode initial.source) events (Abs.decode previous) ∧
      dispatches / (2 * U32.max + 3) ≤ count := by
  apply uniform_eventful_finite_progress memory hooks floats allocator (ExecutableInv view code) ?_ dispatches initial valid last trace
  exact uniform_eventful_inv_step_total Abs.executable_language memory hooks floats allocator correct allocation interrupts view laws code
    (ExecutableInv view code) (fun _ held => held.toCertifiedApiStore.toCertifiedSupportedStore) (fun _ _ held mutation => held.update mutation)
    sound preserve externs issuedResults expected
end Exec.Theorems

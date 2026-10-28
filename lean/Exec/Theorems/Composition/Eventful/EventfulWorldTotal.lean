import Exec.Theorems.Composition.Eventful.EventfulWorldNonhost
import Exec.Theorems.Host.HostSiteWorld
import Exec.Theorems.Composition.ExecutionCode
import Exec.Generated.Types
import Exec.Spec.Extend
import Exec.Contracts
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- Full actual dispatch under a current-world callback contract. Each ordinary
case reuses the fixed-world proof; actual host calls choose their post-world. -/
theorem world_step_outcomes
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ code s,Inv code s → CertifiedSupportedStore view code s)
    (update : ∀ code before after,Inv code before → CumulativeStoreMutation view code before after → Inv code after)
    (callbacks : HostLaws hooks view Inv)
    (expected : List valtype) :
    WorldStepOutcomes memory hooks floats allocator view expected Inv := by
  intro world valid active
  rcases world_step_or_host memory hooks floats allocator view laws world.code
    Inv update world.machine valid active with site | ordinary
  · rcases (site.world_outcomes memory hooks floats allocator laws.allocCorrect laws.interruptsReturn view world.code Inv certify
        world.machine.exec world.machine.store world.machine.platform valid
        (fun host p => callbacks.sound world.code world.machine.store valid p host)
        (callbacks.retains _ _ valid) world.machine.invariant.typed.typed).imp_exists with
      ⟨out,actual,result⟩ | ⟨actual,diverged⟩
    · rw [actual,DivSpec.ok_iff]
      exact result.bundle actual
    · rw [actual]
      exact .div _ diverged
  · exact .of_spec _ _ _ _ ordinary
end Exec.Theorems

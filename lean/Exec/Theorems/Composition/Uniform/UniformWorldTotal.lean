import Exec.Theorems.Composition.Uniform.UniformEventfulNonhost
import Exec.Theorems.Progress.UniformWorldFinite
import Exec.Theorems.Host.HostSiteWorldUniform
import Exec.Theorems.Composition.ExecutionCode
import Exec.Generated.Types
import Exec.Spec.Extend
import Exec.Contracts
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- Full actual dispatch under a current-world callback contract. Each ordinary
case reuses the fixed-world proof; actual host calls choose their post-world. -/
theorem uniform_world_step_total
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ code s,Inv code s → CertifiedSupportedStore view code s)
    (update : ∀ code before after,Inv code before → CumulativeStoreMutation view code before after → Inv code after)
    (callbacks : HostLaws hooks view Inv)
    (expected : List valtype) :
    UniformWorldStepTotal memory hooks floats allocator view expected Inv := by
  intro world valid active
  rcases uniform_eventful_inv_step_or_host memory hooks floats allocator view laws world.code
    (Inv world.code) (update world.code) world.machine valid active with site | ordinary
  · obtain ⟨out,actual,result⟩ := WP.spec_imp_exists
      (site.world_uniform memory hooks floats allocator laws.allocCorrect laws.interruptsReturn view world.code Inv certify
        world.machine.exec world.machine.store world.machine.platform valid
        (fun host p => callbacks.sound world.code world.machine.store valid p host)
        (callbacks.retains _ _ valid) world.machine.invariant.typed.typed)
    rw [actual,WP.spec_ok]
    exact result.bundle actual
  · apply WP.spec_mono ordinary
    intro out result success
    obtain ⟨events,next,equal,edge⟩ := result.2.1 success
    refine ⟨events,⟨world.code,next⟩,?_,equal,edge.toEventfulTransition.world,edge.uniform⟩
    have stores := congrArg (fun out : EventfulDispatchResult M P => out.2.2.1) equal
    simpa only [stores] using result.1
end Exec.Theorems

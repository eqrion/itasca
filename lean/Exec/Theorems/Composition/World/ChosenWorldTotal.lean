import Exec.Theorems.Composition.World.ChosenWorldNonhost
import Exec.Theorems.Composition.World.ChosenWorld
import Exec.Theorems.Host.Chosen.HostSiteChosenWorld
import Exec.Theorems.Host.Chosen.HostWorldChosenSound
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- Full actual dispatch under a current-world callback contract. Each ordinary
case reuses the fixed-world proof; actual host calls choose their post-world. -/
theorem chosen_world_step_outcomes {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice)
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ code s,Inv code s → CertifiedSupportedStore view code s)
    (update : ∀ code before after,Inv code before → CumulativeStoreMutation view code before after → Inv code after)
    (typed : ∀ code store,Inv code store → Store_ok (Store.decodeStore view code store))
    (sound : HostWorldChosenSound memory hooks view Inv choices)
    (preserve : ∀ code store, Inv code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ code store, Inv code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ code store, Inv code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (expected : List valtype) :
    ChosenWorldStepOutcomes choices memory hooks floats allocator view expected Inv := by
  intro world valid active
  rcases chosen_world_step_or_host admissible numericChoice vector world.occurrence memory hooks floats allocator correct allocation
    interrupts view laws world.code compatible Inv update world.machine valid active with site | ordinary
  · obtain ⟨out,actual,result⟩ := WP.spec_imp_exists
      (site.chosen_world_outcomes admissible vector world.occurrence memory hooks floats allocator allocation interrupts view world.code Inv certify
        world.machine.exec world.machine.store world.machine.platform valid (typed _ _ valid)
        (fun occurrence host p => sound occurrence world.code world.machine.store valid p host)
        (preserve _ _ valid) (externs _ _ valid) (issued _ _ valid) world.machine.invariant.typed.typed)
    rw [actual,WP.spec_ok]
    exact result.chosen_bundle admissible actual
  · obtain ⟨out,actual,result⟩ := WP.spec_imp_exists ordinary
    rw [actual,WP.spec_ok]
    exact result.chosen_bundle admissible actual
end Exec.Theorems

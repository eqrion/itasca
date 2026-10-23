import Exec.Theorems.Host.Open.Driver.CompletedEvents
import Exec.Theorems.Host.Chosen.PureChosenCallbacks
import Exec.Theorems.Composition.World.ChosenWorldTotal
import Exec.Theorems.Host.Reentrant.FiniteReentrantCallbacks
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- A normally completed resumable native step reuses the existing complete
profile dispatcher proof. The inert callback dictionary has a proved concrete
contract; no native-step simulation is assumed by this adapter. -/
theorem completed_chosen_world {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice)
    (hostChoice : choices.host=Spec.trappingHostChoice) (occurrence : Nat) {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    {expected : List valtype}
    (world : EventfulWorld M Unit view expected)
    (held : ExecutableInv view world.code world.machine.store) (active : 0<world.machine.exec.frames.length)
    (typed : Config_ok (Abs.decode world.machine.source) (.mk_list expected)) (out : Answer M Unit)
    (completed : prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform=
      .ok (.done out)) :
    ChosenWorldStepResult choices memory (inert memory) floats allocator
      (ReentrantCallbacks.FloorInv view world.machine.store.externs.length) (⟨world,occurrence⟩ : ChosenWorld M Unit view expected) out ∧
      stepHostEvents world.machine.exec world.machine.store out=[] := by
  have raw : ∀before token identity args defaults,
      (inert memory).call_host token before identity args defaults ⦃ answer=>
        FrameStorePrefix before answer.2.2.1 ∧ before.externs.length≤answer.2.2.1.externs.length ∧
        ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value ⦄ := by
    intro before token identity args defaults
    exact WP.spec.ret ⟨.refl _,Nat.le_refl _,by simp [PureCallbacks.Program.evaluate]⟩
  let Inv := ReentrantCallbacks.FloorInv view world.machine.store.externs.length
  have sound : HostWorldChosenSound memory (inert memory) view Inv choices:=
    PureCallbacks.trapping_chosen_sound memory view Inv (fun _ _ valid=>valid.1.source_typed) choices hostChoice
  have post := chosen_world_step_outcomes admissible numericChoice vector memory (inert memory) floats allocator correct allocation
    (fun _=>WP.spec.ret trivial) view laws compatible Inv
    (fun _ _ valid=>valid.1.toCertifiedApiStore.toCertifiedSupportedStore)
    (fun _ _ _ valid mutation=>valid.update mutation) (fun _ _ valid=>valid.1.source_typed) sound
    (fun _ before _ identity token args defaults answer actual=>by
      have law := raw before token identity args defaults
      rw [actual,WP.spec_ok] at law
      exact law.1)
    (fun _ before _ identity token args defaults answer actual=>by
      have law := raw before token identity args defaults
      rw [actual,WP.spec_ok] at law
      exact law.2.1)
    (fun _ before _ identity token args defaults answer actual=>by
      have law := raw before token identity args defaults
      rw [actual,WP.spec_ok] at law
      exact law.2.2)
    expected ⟨world,occurrence⟩ ⟨held,Nat.le_refl _⟩ active
  have graph := erase_step memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform
  simp only [completed,bind_ok,resume] at graph
  rw [←graph,WP.spec_ok] at post
  exact ⟨post,completed_step_events memory floats allocator allocation view world held active typed out completed⟩
end Exec.Theorems.OpenReentrantControl

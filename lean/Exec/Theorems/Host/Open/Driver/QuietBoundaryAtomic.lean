import Exec.Theorems.Host.Open.Driver.CompletedEvents
import Exec.Theorems.Host.Chosen.PureChosenCallbacks
import Exec.Theorems.Composition.World.ChosenWorldTotal
import Exec.Theorems.Host.Reentrant.FiniteReentrantCallbacks
import Exec.Theorems.Composition.World.ChosenWorldCompletion
import Exec.Abs.Sim.OpenQuietBoundaryCompletion
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- An independently terminating silent source segment makes the auxiliary
inert native Wasm loop return. A pending host boundary is completed only in
this auxiliary loop; the open driver still suspends before the real callback. -/
theorem quiet_boundary_atomic_terminates {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice)
    (occurrence : Nat) {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    {expected : List valtype} (world : EventfulWorld M Unit view expected)
    (held : ExecutableInv view world.code world.machine.store) {count endpoint}
    (prefixSteps : Spec.ChosenStepsN choices occurrence count (Abs.decode world.machine.source) [] endpoint)
    (boundary : Spec.OpenHost.QuietBoundary endpoint) :
    let trapped : Spec.SourceChoices:={choices with host:=Spec.trappingHostChoice}
    let Inv:=ReentrantCallbacks.FloorInv view world.machine.store.externs.length
    let initial : ChosenWorld M Unit view expected:=⟨world,occurrence⟩
    runtime.interp.invoke_with_loop1 memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform (.Ok ())
      ⦃result=>∃state,ChosenWorldLoopInvariant trapped memory (inert memory) floats allocator Inv initial state ∧
        ¬ActiveExecution state ∧ finishExecution state=result⦄ := by
  dsimp only
  let trapped : Spec.SourceChoices:={choices with host:=Spec.trappingHostChoice}
  have permitted : trapped.Admissible:=⟨Spec.trappingHostChoice_admissible,admissible.numeric,admissible.vector,admissible.memory,admissible.table⟩
  have growth : GrowthChoicesCompatible memory allocator view trapped:=⟨compatible.memoryReply,compatible.tableReply⟩
  have raw : ∀before token identity args defaults,
      (inert memory).call_host token before identity args defaults ⦃ answer=>
        FrameStorePrefix before answer.2.2.1 ∧ before.externs.length≤answer.2.2.1.externs.length ∧
        ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value ⦄ := by
    intro before token identity args defaults
    exact WP.spec.ret ⟨.refl _,Nat.le_refl _,by simp [PureCallbacks.Program.evaluate]⟩
  let Inv := ReentrantCallbacks.FloorInv view world.machine.store.externs.length
  have sound : HostWorldChosenSound memory (inert memory) view Inv trapped:=
    PureCallbacks.trapping_chosen_sound memory view Inv (fun _ _ valid=>valid.1.source_typed) trapped rfl
  have steps : ChosenWorldStepOutcomes trapped memory (inert memory) floats allocator view expected Inv:=
    chosen_world_step_outcomes permitted numericChoice vector memory (inert memory) floats allocator correct allocation
    (fun _=>WP.spec.ret trivial) view laws growth Inv
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
    expected
  obtain ⟨total,events,target,run,terminal⟩:=boundary.trapping_completion admissible prefixSteps
  exact WP.spec_mono (chosen_world_loop_terminates permitted memory (inert memory) floats allocator Inv steps
    (⟨world,occurrence⟩ : ChosenWorld M Unit view expected)
    ⟨held,Nat.le_refl _⟩ run.erase_count terminal) (fun result post=>post.2)
end Exec.Theorems.OpenReentrantControl

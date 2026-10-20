import Exec.Spec.Choices.CoreDeterminism
import Exec.Spec.Choices.ContextUniqueness
import Exec.Spec.Choices.Normalization
namespace Exec.Spec
open SpecExt

/-- Fixed admissible choices determine every step before trap cleanup becomes
active. Administrative trap cleanup uses strong normalization instead. -/
theorem choice_step_nonactive_deterministic {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence : Nat} {before left right : config} {leftEvents rightEvents : List HostEvent}
    (first : ChoiceStep choices occurrence before leftEvents left)
    (second : ChoiceStep choices occurrence before rightEvents right)
    (nonactive : activeTrap (trapCode before)=false) : leftEvents=rightEvents ∧ left=right := by
  have boundedDet : ∀ budget, ∀ (before left right : config) (le re : List HostEvent),
      ChoiceStep choices occurrence before le left → ChoiceStep choices occurrence before re right →
      activeTrap (trapCode before)=false → sizeOf (trapCode before)≤budget → le=re ∧ left=right := by
    intro budget
    induction budget using Nat.strong_induction_on with
    | h budget ih =>
      intro before left right le re first second nonactive bounded
      obtain ⟨z,next,front,body,result,tail,firstBefore,firstAfter,firstCore⟩ := first.contextualCore.view
      obtain ⟨otherZ,otherNext,otherFront,otherBody,otherResult,otherTail,secondBefore,secondAfter,secondCore⟩ := second.contextualCore.view
      have wholeEq := firstBefore.symm.trans secondBefore
      have stateEq := congrArg trapState wholeEq
      dsimp only [trapState] at stateEq
      cases stateEq
      have codeEq := congrArg trapCode wholeEq
      dsimp only [trapCode] at codeEq
      rw [firstBefore] at nonactive bounded
      dsimp only [trapCode] at nonactive bounded
      obtain ⟨frontEq,bodyEq,tailEq⟩ := core_context_unique admissible firstCore secondCore nonactive codeEq
      cases frontEq
      cases bodyEq
      cases tailEq
      have coreActive := firstCore.nonactive_in_context admissible front tail nonactive
      have coreSize := sizeOf_instruction_context front body tail
      have within : sizeOf body≤budget := by omega
      have coreEq := core_deterministic_of_children admissible firstCore secondCore rfl coreActive within (by
        intro state body le re left right small nonactive first second
        exact ih (sizeOf body) small ⟨state,body⟩ left right le re first second nonactive (by rfl))
      refine ⟨coreEq.1,?_⟩
      rw [firstAfter,secondAfter]
      exact congrArg (fun c : config => match c with | ⟨z,code⟩ => config.mk_config z (vals front++(code++tail))) coreEq.2
  exact boundedDet (sizeOf (trapCode before)) before left right leftEvents rightEvents first second nonactive (Nat.le_refl _)
end Exec.Spec

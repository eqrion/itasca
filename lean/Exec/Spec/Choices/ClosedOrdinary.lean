import Exec.Spec.Choices.Steps
import Exec.Spec.Steps
import Exec.Spec.Choices.ChosenCounted
namespace Exec.Spec
open SpecExt

/-- An instruction region closed under ordinary reductions: no calls,
embedded control code, numeric alternatives, growth, labels or frames. This
includes the complete generated bulk-memory/table expansion language. -/
def closedOrdinaryInstruction : admininstr → Bool
  | .BLOCK _ _ | .LOOP _ _ | .IFELSE _ _ _ | .CALL _ | .CALL_INDIRECT _ _ | .CALL_ADDR _
  | .LABEL_ _ _ _ | .FRAME_ _ _ _ | .UNOP _ _ | .BINOP _ _ | .CVTOP _ _ _
  | .VUNOP _ _ | .VBINOP _ _ | .VCVTOP _ _ _ | .MEMORY_GROW | .TABLE_GROW _ => false
  | _ => true

def ClosedOrdinaryCode (code : List admininstr) : Prop :=
  Forall (fun instruction => closedOrdinaryInstruction instruction=true) code

theorem closedOrdinary_value (value : val) : closedOrdinaryInstruction (admininstr_val value)=true := by
  cases value <;> rfl

theorem closedOrdinary_ref (value : ref) : closedOrdinaryInstruction (admininstr_ref value)=true := by
  cases value <;> rfl

theorem closedOrdinary_nil : ClosedOrdinaryCode [] := by simp [ClosedOrdinaryCode,Forall]

theorem closedOrdinary_cons (head : admininstr) (tail : List admininstr) :
    ClosedOrdinaryCode (head::tail) ↔ closedOrdinaryInstruction head=true ∧ ClosedOrdinaryCode tail := by
  simp [ClosedOrdinaryCode,Forall]

theorem closedOrdinary_append (front tail : List admininstr) :
    ClosedOrdinaryCode (front++tail) ↔ ClosedOrdinaryCode front ∧ ClosedOrdinaryCode tail := by
  constructor
  · intro closed
    exact ⟨fun i hi => closed i (List.mem_append_left _ hi), fun i hi => closed i (List.mem_append_right _ hi)⟩
  · rintro ⟨front,tail⟩ i hi
    rcases List.mem_append.mp hi with left | right
    · exact front i left
    · exact tail i right

theorem closedOrdinary_values (values : List val) : ClosedOrdinaryCode (values.map admininstr_val) := by
  intro instruction member
  obtain ⟨value,_,rfl⟩ := List.mem_map.mp member
  exact closedOrdinary_value value

theorem ClosedOrdinaryCode.choice_free {z : state} {body : List admininstr} (closed : ClosedOrdinaryCode body) :
    ChoiceFreeConfig ⟨z,body⟩ := by
  intro instruction member
  apply ChoiceFreeInstruction.atom
  have ordinary := closed instruction member
  cases instruction <;> simp_all [closedOrdinaryInstruction,ordinaryChoiceTag]

set_option maxHeartbeats 2000000 in
theorem pure_closedOrdinary {before after : List admininstr} (source : Step_pure before after)
    (closed : ClosedOrdinaryCode before) : ClosedOrdinaryCode after := by
  cases source
  all_goals try simp only [vals,Map] at closed ⊢
  all_goals try simp only [closedOrdinary_append,closedOrdinary_cons,closedOrdinary_nil,
    closedOrdinary_values,closedOrdinary_value,closedOrdinary_ref,true_and,and_true] at closed ⊢
  all_goals try simp [closedOrdinaryInstruction,ClosedOrdinaryCode,Forall] at closed ⊢

set_option maxHeartbeats 2000000 in
theorem read_closedOrdinary {z : state} {before after : List admininstr} (source : Step_read ⟨z,before⟩ after)
    (closed : ClosedOrdinaryCode before) : ClosedOrdinaryCode after := by
  cases source
  all_goals try simp only [vals,Map] at closed ⊢
  all_goals try simp only [closedOrdinary_append,closedOrdinary_cons,closedOrdinary_nil,
    closedOrdinary_values,closedOrdinary_value,closedOrdinary_ref,true_and,and_true] at closed ⊢
  all_goals try simp [closedOrdinaryInstruction,ClosedOrdinaryCode,Forall] at closed ⊢

/-- The restricted region is preserved by every generated ordinary step. -/
theorem step_closedOrdinary {before after : config} (source : Step before after)
    (closed : ClosedOrdinaryCode (trapCode before)) : ClosedOrdinaryCode (trapCode after) := by
  revert closed
  induction source
  all_goals intro closed
  case pure z body result source input output => exact pure_closedOrdinary source closed
  case read z body result source input output => exact read_closedOrdinary source closed
  case ctxt_instrs z front body tail next result source nonempty input output inside outside ih =>
    change ClosedOrdinaryCode (vals front++(body++tail)) at closed
    change ClosedOrdinaryCode (vals front++(result++tail))
    have parts := (closedOrdinary_append body tail).mp ((closedOrdinary_append (vals front) (body++tail)).mp closed).2
    apply (closedOrdinary_append _ _).mpr
    exact ⟨closedOrdinary_values front,(closedOrdinary_append _ _).mpr ⟨ih parts.1,parts.2⟩⟩
  all_goals try simp only [trapCode,vals,Map] at closed ⊢
  all_goals try simp only [closedOrdinary_append,closedOrdinary_cons,closedOrdinary_nil,
    closedOrdinary_values,closedOrdinary_value,closedOrdinary_ref,true_and,and_true] at closed ⊢
  all_goals simp [closedOrdinaryInstruction,ClosedOrdinaryCode,Forall] at closed ⊢

/-- A finite closed region consumes the same ordinary reductions under every
policy. Its source proof, rather than an interpreter trace, establishes closure. -/
theorem StepsHN.closed_chosen (choices : SourceChoices) (occurrence : Nat)
    {count : Nat} {before after : config} {events : List HostEvent}
    (source : StepsHN count before events after) (closed : ClosedOrdinaryCode (trapCode before))
    (silent : events=[]) : ChosenStepsN choices occurrence count before events after := by
  revert closed silent
  induction source generalizing occurrence with
  | refl typed => exact fun _ _ => .refl occurrence typed
  | cons edge tail ih =>
    intro closed silent
    rcases List.append_eq_nil_iff.mp silent with ⟨headEmpty,tailEmpty⟩
    subst headEmpty
    subst tailEmpty
    have ordinary := stepH_nil_to_step edge
    have nextClosed := step_closedOrdinary ordinary closed
    have first : ChoiceStep choices occurrence _ [] _ := .ordinary ordinary closed.choice_free
    exact .cons first (ih (occurrence+1) nextClosed rfl)
end Exec.Spec

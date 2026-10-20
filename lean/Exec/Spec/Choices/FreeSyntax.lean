import Exec.Spec.Choices.Steps
namespace Exec.Spec
open SpecExt

theorem ChoiceFreeInstruction.label_body {arity : Nat} {cont : List instr} {body : List admininstr}
    (free : ChoiceFreeInstruction (.LABEL_ arity cont body)) :
    ∀ instruction ∈ body, ChoiceFreeInstruction instruction := by
  cases free <;> first | assumption | simp_all [ordinaryChoiceTag]

theorem ChoiceFreeInstruction.frame_body {arity : Nat} {frame : _root_.frame} {body : List admininstr}
    (free : ChoiceFreeInstruction (.FRAME_ arity frame body)) :
    ∀ instruction ∈ body, ChoiceFreeInstruction instruction := by
  cases free <;> first | assumption | simp_all [ordinaryChoiceTag]

theorem ChoiceFreeConfig.instructions {state : _root_.state} {front : List val} {body tail : List admininstr}
    (free : ChoiceFreeConfig ⟨state,vals front++(body++tail)⟩) : ChoiceFreeConfig ⟨state,body⟩ := by
  intro instruction member
  exact free instruction (List.mem_append_right _ (List.mem_append_left _ member))

theorem ChoiceFreeConfig.pure {state : _root_.state} {body : List admininstr}
    (free : ChoiceFreeConfig ⟨state,body⟩) : ChoiceFreePureRedex body := by
  unfold ChoiceFreePureRedex
  cases choosing : pureRedexUsesChoice body
  · rfl
  · exfalso
    unfold pureRedexUsesChoice at choosing
    split at choosing
    all_goals try contradiction
    all_goals simp only [ChoiceFreeConfig,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at free
    all_goals first
      | obtain ⟨_,_,illegal⟩ := free; cases illegal; simp [ordinaryChoiceTag] at *
      | obtain ⟨_,illegal⟩ := free; cases illegal; simp [ordinaryChoiceTag] at *

theorem ordinaryChoiceTag_value (value : val) : ordinaryChoiceTag (admininstr_val value)=true := by
  cases value <;> rfl

theorem ordinaryChoiceTag_ref (value : ref) : ordinaryChoiceTag (admininstr_ref value)=true := by
  cases value <;> rfl

theorem ChoiceFreeWriteRedex.config {state : _root_.state} {body : List admininstr}
    (free : ChoiceFreeWriteRedex body) : ChoiceFreeConfig ⟨state,body⟩ := by
  cases free
  all_goals intro instruction member
  all_goals apply ChoiceFreeInstruction.atom
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl
  all_goals first | exact ordinaryChoiceTag_value _ | exact ordinaryChoiceTag_ref _ | rfl
end Exec.Spec

import Exec.Spec.Typing.ValueInversion
namespace Exec.Spec
open SpecExt

theorem value_instruction_injective {left right : val} (same : admininstr_val left=admininstr_val right) : left=right := by
  have read := congrArg instructionValue same
  simpa only [instructionValue_val,Option.some.injEq] using read

theorem nonvalue_not_in_values {instruction : admininstr} (notValue : instructionValue instruction=none) (values : List val) :
    instruction ∉ vals values := by
  intro member
  obtain ⟨value,_,same⟩ := List.mem_map.mp member
  rw [← same,instructionValue_val] at notValue
  contradiction

theorem values_ne_nonvalue_prefix (left right : List val) (instruction : admininstr) (tail : List admininstr)
    (notValue : instructionValue instruction=none) : vals left≠vals right++instruction::tail := by
  intro same
  apply nonvalue_not_in_values notValue left
  rw [same]
  simp

theorem value_prefix_unique {left right : List val} {first second : admininstr} {tail rest : List admininstr}
    (leftNonvalue : instructionValue first=none) (rightNonvalue : instructionValue second=none)
    (same : vals left++first::tail=vals right++second::rest) : left=right ∧ first=second ∧ tail=rest := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil =>
      have parts := List.cons.inj same
      exact ⟨rfl,parts⟩
    | cons value right =>
      have head : first=admininstr_val value := (List.cons.inj same).1
      have no := leftNonvalue
      rw [head,instructionValue_val] at no
      contradiction
  | cons value left ih =>
    cases right with
    | nil =>
      have head : admininstr_val value=second := (List.cons.inj same).1
      have no := rightNonvalue
      rw [← head,instructionValue_val] at no
      contradiction
    | cons other right =>
      have head := value_instruction_injective (List.cons.inj same).1
      have rest := ih (List.cons.inj same).2
      exact ⟨congrArg₂ List.cons head rest.1,rest.2⟩
end Exec.Spec

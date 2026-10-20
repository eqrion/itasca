import Exec.Spec.Choices.ValuePrefixSyntax
/-! Uniqueness and disjointness of branch/return value prefixes, including
retained suffixes of the fixed result arity. -/

namespace Exec.Spec
open SpecExt

theorem ordinary_value_prefix_unique {left right : List val} {first second : admininstr} {tail rest : List admininstr}
    (same : vals left++first::tail=vals right++second::rest)
    (leftNonvalue : instructionValue first=none) (rightNonvalue : instructionValue second=none) : left=right :=
  (value_prefix_unique leftNonvalue rightNonvalue same).1

theorem retained_value_suffix_unique {saved left others right : List val} {first second : admininstr} {tail rest : List admininstr}
    (same : vals (saved++left)++first::tail=vals (others++right)++second::rest)
    (leftNonvalue : instructionValue first=none) (rightNonvalue : instructionValue second=none)
    (count : left.length=right.length) : left=right :=
  List.append_inj_right' (ordinary_value_prefix_unique same leftNonvalue rightNonvalue) count

theorem branch_return_prefix_disjoint {left right : List val} {index : idx} {tail rest : List admininstr}
    (same : vals left++(.BR index)::tail=vals right++.RETURN::rest) : False := by
  have marker := (value_prefix_unique rfl rfl same).2.1
  cases marker

theorem branch_zero_successor_prefix_disjoint {left right : List val} {index : idx} {tail rest : List admininstr}
    (same : vals left++(.BR (.mk_uN 0))::tail=vals right++(.BR (.mk_uN (proj_uN_0 index+1)))::rest) : False := by
  have marker := (value_prefix_unique rfl rfl same).2.1
  have numbers := congrArg (fun instruction => match instruction with | .BR index => proj_uN_0 index | _ => 0) marker
  simp only [proj_uN_0] at numbers
  omega

theorem source_branch_successor_unique {left right : List val} {index other : idx} {tail rest : List admininstr}
    (same : vals left++(.BR (.mk_uN (proj_uN_0 index+1)))::tail=
      vals right++(.BR (.mk_uN (proj_uN_0 other+1)))::rest) :
    vals left++[.BR index]=vals right++[.BR other] := by
  obtain ⟨values,marker,_⟩ := value_prefix_unique rfl rfl same
  cases values
  have numbers := congrArg (fun instruction => match instruction with | .BR index => proj_uN_0 index | _ => 0) marker
  simp only [proj_uN_0] at numbers
  have sameIndex : index=other := by
    cases index
    cases other
    simp only [proj_uN_0] at numbers
    congr 1
    omega
  cases sameIndex
  rfl
end Exec.Spec

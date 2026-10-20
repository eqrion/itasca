import Exec.Spec.Choices.SimdAuxDeterminism
namespace Exec.Spec
open SpecExt

theorem packnum_present_unique {type : lanetype} {input : num_} {left right : Option lane_}
    (first : fun_packnum_ type input left) (second : fun_packnum_ type input right)
    (leftPresent : left≠none) (rightPresent : right≠none) : left=right := by
  cases left <;> cases right
  all_goals first | contradiction | exact congrArg some (packnum_some_unique first second)

theorem unpacknum_present_unique {type : lanetype} {input : lane_} {left right : Option num_}
    (first : fun_unpacknum_ type input left) (second : fun_unpacknum_ type input right)
    (leftPresent : left≠none) (rightPresent : right≠none) : left=right := by
  cases left <;> cases right
  all_goals first | contradiction | exact congrArg some (unpacknum_some_unique first second)

theorem vector_shift_present_unique {shape : ishape} {operator : vshiftop_} {input : lane_} {shift : u32}
    {left right : Option lane_} (first : fun_vshiftop_ shape operator input shift left)
    (second : fun_vshiftop_ shape operator input shift right) (leftPresent : left≠none) (rightPresent : right≠none) : left=right := by
  cases left <;> cases right
  all_goals first | contradiction | exact congrArg some (vector_shift_some_unique first second)

theorem vector_shift_list_unique {shape : ishape} {operator : vshiftop_} {shift : u32} (inputs : List lane_)
    (left right : List (Option lane_)) (leftLength : left.length=inputs.length) (rightLength : right.length=inputs.length)
    (first : Forall₂ (fun reply lane => fun_vshiftop_ shape operator lane shift reply) left inputs)
    (second : Forall₂ (fun reply lane => fun_vshiftop_ shape operator lane shift reply) right inputs)
    (leftPresent : Forall (fun reply => reply≠none) left) (rightPresent : Forall (fun reply => reply≠none) right) : left=right := by
  apply forall2_functional_left (fun reply lane => fun_vshiftop_ shape operator lane shift reply ∧ reply≠none)
    (fun _ _ _ one two => vector_shift_present_unique one.1 two.1 one.2 two.2) inputs left right leftLength rightLength
  · intro pair member
    exact ⟨first pair member,leftPresent pair.1 (List.of_mem_zip member).1⟩
  · intro pair member
    exact ⟨second pair member,rightPresent pair.1 (List.of_mem_zip member).1⟩

theorem signed_lane_negative_list_unique (width : Nat) (inputs : List lane_) (left right : List uN)
    (leftLength : left.length=inputs.length) (rightLength : right.length=inputs.length)
    (first : Forall₂ (fun result lane => fun_ilt_ width .S (proj_lane__0 lane).get! (.mk_uN 0) result) left inputs)
    (second : Forall₂ (fun result lane => fun_ilt_ width .S (proj_lane__0 lane).get! (.mk_uN 0) result) right inputs) : left=right :=
  forall2_functional_left (fun result lane => fun_ilt_ width .S (proj_lane__0 lane).get! (.mk_uN 0) result)
    (fun _ _ _ first second => ilt_results_unique first second) inputs left right leftLength rightLength first second
end Exec.Spec

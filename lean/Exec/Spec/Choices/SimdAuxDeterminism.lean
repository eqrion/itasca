import Exec.Spec.Choices.NumericPredicateDeterminism
import Exec.Spec.Choices.VectorDeterminism
/-! Deterministic packing, unpacking, lane shifts and vector predicates.
Functional list lemmas retain the generated zip length obligations. -/

namespace Exec.Spec
open SpecExt

theorem packnum_some_unique {type : lanetype} {input : num_} {left right : lane_}
    (first : fun_packnum_ type input (some left)) (second : fun_packnum_ type input (some right)) : left=right := by
  cases first <;> cases second <;> rfl

theorem unpacknum_some_unique {type : lanetype} {input : lane_} {left right : num_}
    (first : fun_unpacknum_ type input (some left)) (second : fun_unpacknum_ type input (some right)) : left=right := by
  cases first <;> cases second <;> rfl

theorem vector_shift_some_unique {shape : ishape} {operator : vshiftop_} {input : lane_} {shift : u32} {left right : lane_}
    (first : fun_vshiftop_ shape operator input shift (some left))
    (second : fun_vshiftop_ shape operator input shift (some right)) : left=right := by
  cases first <;> cases second <;> rfl

theorem ieq_results_unique {width : Nat} {a b left right : uN}
    (first : fun_ieq_ width a b left) (second : fun_ieq_ width a b right) : left=right := by
  cases first <;> cases second
  all_goals grind only [signed_deterministic]

theorem list_ieq_unique (width : Nat) {inputs others : List lane_} {left right : List uN}
    (leftLength : left.length=inputs.length) (rightLength : right.length=inputs.length)
    (otherLength : others.length=inputs.length)
    (first : Forall₃ (fun result a b => fun_ieq_ width (proj_lane__0 a).get! (proj_lane__0 b).get! result) left inputs others)
    (second : Forall₃ (fun result a b => fun_ieq_ width (proj_lane__0 a).get! (proj_lane__0 b).get! result) right inputs others) : left=right :=
  forall3_functional_left (fun result a b => fun_ieq_ width (proj_lane__0 a).get! (proj_lane__0 b).get! result)
    (fun _ _ _ _ first second => ieq_results_unique first second) inputs others left right
    leftLength rightLength otherLength first second

theorem ine_results_unique {width : Nat} {a b left right : uN}
    (first : fun_ine_ width a b left) (second : fun_ine_ width a b right) : left=right := by
  cases first <;> cases second
  all_goals grind only [signed_deterministic]

theorem list_ine_unique (width : Nat) {inputs others : List lane_} {left right : List uN}
    (leftLength : left.length=inputs.length) (rightLength : right.length=inputs.length)
    (otherLength : others.length=inputs.length)
    (first : Forall₃ (fun result a b => fun_ine_ width (proj_lane__0 a).get! (proj_lane__0 b).get! result) left inputs others)
    (second : Forall₃ (fun result a b => fun_ine_ width (proj_lane__0 a).get! (proj_lane__0 b).get! result) right inputs others) : left=right :=
  forall3_functional_left (fun result a b => fun_ine_ width (proj_lane__0 a).get! (proj_lane__0 b).get! result)
    (fun _ _ _ _ first second => ine_results_unique first second) inputs others left right
    leftLength rightLength otherLength first second

theorem ilt_results_unique {width : Nat} {sign : sx} {a b left right : uN}
    (first : fun_ilt_ width sign a b left) (second : fun_ilt_ width sign a b right) : left=right := by
  cases first <;> cases second
  all_goals grind only [signed_deterministic]

theorem list_ilt_unique (width : Nat) (sign : sx) {inputs others : List lane_} {left right : List uN}
    (leftLength : left.length=inputs.length) (rightLength : right.length=inputs.length)
    (otherLength : others.length=inputs.length)
    (first : Forall₃ (fun result a b => fun_ilt_ width sign (proj_lane__0 a).get! (proj_lane__0 b).get! result) left inputs others)
    (second : Forall₃ (fun result a b => fun_ilt_ width sign (proj_lane__0 a).get! (proj_lane__0 b).get! result) right inputs others) : left=right :=
  forall3_functional_left (fun result a b => fun_ilt_ width sign (proj_lane__0 a).get! (proj_lane__0 b).get! result)
    (fun _ _ _ _ first second => ilt_results_unique first second) inputs others left right
    leftLength rightLength otherLength first second

theorem ile_results_unique {width : Nat} {sign : sx} {a b left right : uN}
    (first : fun_ile_ width sign a b left) (second : fun_ile_ width sign a b right) : left=right := by
  cases first <;> cases second
  all_goals grind only [signed_deterministic]

theorem list_ile_unique (width : Nat) (sign : sx) {inputs others : List lane_} {left right : List uN}
    (leftLength : left.length=inputs.length) (rightLength : right.length=inputs.length)
    (otherLength : others.length=inputs.length)
    (first : Forall₃ (fun result a b => fun_ile_ width sign (proj_lane__0 a).get! (proj_lane__0 b).get! result) left inputs others)
    (second : Forall₃ (fun result a b => fun_ile_ width sign (proj_lane__0 a).get! (proj_lane__0 b).get! result) right inputs others) : left=right :=
  forall3_functional_left (fun result a b => fun_ile_ width sign (proj_lane__0 a).get! (proj_lane__0 b).get! result)
    (fun _ _ _ _ first second => ile_results_unique first second) inputs others left right
    leftLength rightLength otherLength first second

theorem igt_results_unique {width : Nat} {sign : sx} {a b left right : uN}
    (first : fun_igt_ width sign a b left) (second : fun_igt_ width sign a b right) : left=right := by
  cases first <;> cases second
  all_goals grind only [signed_deterministic]

theorem list_igt_unique (width : Nat) (sign : sx) {inputs others : List lane_} {left right : List uN}
    (leftLength : left.length=inputs.length) (rightLength : right.length=inputs.length)
    (otherLength : others.length=inputs.length)
    (first : Forall₃ (fun result a b => fun_igt_ width sign (proj_lane__0 a).get! (proj_lane__0 b).get! result) left inputs others)
    (second : Forall₃ (fun result a b => fun_igt_ width sign (proj_lane__0 a).get! (proj_lane__0 b).get! result) right inputs others) : left=right :=
  forall3_functional_left (fun result a b => fun_igt_ width sign (proj_lane__0 a).get! (proj_lane__0 b).get! result)
    (fun _ _ _ _ first second => igt_results_unique first second) inputs others left right
    leftLength rightLength otherLength first second

theorem ige_results_unique {width : Nat} {sign : sx} {a b left right : uN}
    (first : fun_ige_ width sign a b left) (second : fun_ige_ width sign a b right) : left=right := by
  cases first <;> cases second
  all_goals grind only [signed_deterministic]

theorem list_ige_unique (width : Nat) (sign : sx) {inputs others : List lane_} {left right : List uN}
    (leftLength : left.length=inputs.length) (rightLength : right.length=inputs.length)
    (otherLength : others.length=inputs.length)
    (first : Forall₃ (fun result a b => fun_ige_ width sign (proj_lane__0 a).get! (proj_lane__0 b).get! result) left inputs others)
    (second : Forall₃ (fun result a b => fun_ige_ width sign (proj_lane__0 a).get! (proj_lane__0 b).get! result) right inputs others) : left=right :=
  forall3_functional_left (fun result a b => fun_ige_ width sign (proj_lane__0 a).get! (proj_lane__0 b).get! result)
    (fun _ _ _ _ first second => ige_results_unique first second) inputs others left right
    leftLength rightLength otherLength first second

set_option maxHeartbeats 2000000 in
theorem vector_relop_some_unique {shape : _root_.shape} {operator : vrelop_} {leftInput rightInput left right : vec_}
    (first : fun_vrelop_ shape operator leftInput rightInput (some left))
    (second : fun_vrelop_ shape operator leftInput rightInput (some right)) : left=right := by
  cases first <;> cases second
  all_goals subst_vars
  all_goals try { casesm* Inn
                  all_goals norm_num [isize,size,valtype_Fnn,numtype_Fnn,valtype_numtype,numtype_Inn,valtype_Inn] at *
                  all_goals rfl }
  all_goals try {
    congr 3
    first
    | { apply list_ieq_unique _
        rotate_left 3
        all_goals first | assumption | omega }
    | { apply list_ine_unique _
        rotate_left 3
        all_goals first | assumption | omega }
    | { apply list_ilt_unique _ _
        rotate_left 3
        all_goals first | assumption | omega }
    | { apply list_ile_unique _ _
        rotate_left 3
        all_goals first | assumption | omega }
    | { apply list_igt_unique _ _
        rotate_left 3
        all_goals first | assumption | omega }
    | { apply list_ige_unique _ _
        rotate_left 3
        all_goals first | assumption | omega }
  }
end Exec.Spec

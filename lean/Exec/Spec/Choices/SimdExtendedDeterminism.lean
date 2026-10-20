import Exec.Spec.Choices.InterleavingUnique
/-! Uniqueness of relational pairwise sums, extended products and dot products
from explicit list lengths and consecutive-pair decompositions. -/

namespace Exec.Spec
open SpecExt

theorem add_words_unique {width : Nat} {a b left right : uN}
    (first : fun_iadd_ width a b left) (second : fun_iadd_ width a b right) : left=right := by
  cases first
  cases second
  rfl

theorem multiply_words_unique {width : Nat} {a b left right : uN}
    (first : fun_imul_ width a b left) (second : fun_imul_ width a b right) : left=right := by
  cases first
  cases second
  rfl

theorem list_add_words_unique (width : Nat) {inputs others left right : List uN}
    (leftLength : left.length=inputs.length) (rightLength : right.length=inputs.length)
    (otherLength : others.length=inputs.length)
    (first : Forall₃ (fun result a b => fun_iadd_ width a b result) left inputs others)
    (second : Forall₃ (fun result a b => fun_iadd_ width a b result) right inputs others) : left=right :=
  forall3_functional_left (fun result a b => fun_iadd_ width a b result)
    (fun _ _ _ _ first second => add_words_unique first second) inputs others left right leftLength rightLength otherLength first second

theorem list_multiply_words_unique (width : Nat) {inputs others left right : List uN}
    (leftLength : left.length=inputs.length) (rightLength : right.length=inputs.length)
    (otherLength : others.length=inputs.length)
    (first : Forall₃ (fun result a b => fun_imul_ width a b result) left inputs others)
    (second : Forall₃ (fun result a b => fun_imul_ width a b result) right inputs others) : left=right :=
  forall3_functional_left (fun result a b => fun_imul_ width a b result)
    (fun _ _ _ _ first second => multiply_words_unique first second) inputs others left right leftLength rightLength otherLength first second

theorem add_interleaved_lists_unique (width : Nat) {left right a b c d : List uN}
    (first : Forall₃ (fun result x y => fun_iadd_ width x y result) left a b)
    (second : Forall₃ (fun result x y => fun_iadd_ width x y result) right c d)
    (leftA : left.length=a.length) (leftB : left.length=b.length)
    (rightC : right.length=c.length) (rightD : right.length=d.length)
    (same : concat_ uN (Map₂ (fun x y => [x,y]) a b)=concat_ uN (Map₂ (fun x y => [x,y]) c d)) : left=right := by
  obtain ⟨rfl,rfl⟩ := interleaved_lists_unique a b c d (by omega) (by omega) same
  exact list_add_words_unique width leftA rightC (by omega) first second

theorem mapped_product_lists_unique (width : Nat) (leftMap rightMap : lane_ → uN)
    {inputs others : List lane_} {left right : List uN}
    (first : Forall₃ (fun result a b => fun_imul_ width (leftMap a) (rightMap b) result) left inputs others)
    (second : Forall₃ (fun result a b => fun_imul_ width (leftMap a) (rightMap b) result) right inputs others)
    (leftLength : left.length=inputs.length) (rightLength : right.length=inputs.length)
    (otherLength : others.length=inputs.length) : left=right :=
  forall3_functional_left (fun result a b => fun_imul_ width (leftMap a) (rightMap b) result)
    (fun _ _ _ _ first second => multiply_words_unique first second) inputs others left right leftLength rightLength otherLength first second

set_option maxHeartbeats 2000000 in
theorem vector_extunop_some_unique {inputShape outputShape : ishape} {operator : vextunop__} {input left right : vec_}
    (first : fun_vextunop__ inputShape outputShape operator input (some left))
    (second : fun_vextunop__ inputShape outputShape operator input (some right)) : left=right := by
  cases first <;> cases second
  all_goals subst_vars
  all_goals congr 2
  all_goals apply add_interleaved_lists_unique _ (by assumption) (by assumption)
  all_goals first | assumption | omega | (with_reducible grind only)

set_option maxHeartbeats 3000000 in
theorem vector_extbinop_some_unique {inputShape outputShape : ishape} {operator : vextbinop__}
    {leftInput rightInput left right : vec_}
    (first : fun_vextbinop__ inputShape outputShape operator leftInput rightInput (some left))
    (second : fun_vextbinop__ inputShape outputShape operator leftInput rightInput (some right)) : left=right := by
  cases first <;> cases second
  all_goals subst_vars
  all_goals congr 2
  all_goals first
    | { apply mapped_product_lists_unique _ _ _ (by assumption) (by assumption)
        all_goals first | assumption | omega }
    | { apply add_interleaved_lists_unique _ (by assumption) (by assumption)
        all_goals first
          | assumption
          | omega
          | { apply mapped_product_lists_unique _ _ _ (by assumption) (by assumption)
              all_goals first | assumption | omega } }
end Exec.Spec

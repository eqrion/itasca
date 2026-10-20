import Exec.Spec.Choices.NumericDeterminism

/-! Unique permitted SIMD unary/binary result lists. Lane-wise relational
outputs use explicit lengths; permitted floating-point choices remain in the
lists rather than being identified with one selected representation. -/

namespace Exec.Spec

theorem forall2_functional_left {A B : Type} (relation : A → B → Prop)
    (functional : ∀ x y input, relation x input → relation y input → x = y)
    (inputs : List B) (left right : List A)
    (leftLength : left.length = inputs.length) (rightLength : right.length = inputs.length)
    (first : Forall₂ relation left inputs) (second : Forall₂ relation right inputs) : left = right := by
  induction inputs generalizing left right with
  | nil =>
    have l : left = [] := by simpa using leftLength
    have r : right = [] := by simpa using rightLength
    exact l.trans r.symm
  | cons input inputs ih =>
    cases left with
    | nil => simp at leftLength
    | cons x left =>
      cases right with
      | nil => simp at rightLength
      | cons y right =>
        have head := functional x y input (first (x,input) (by simp)) (second (y,input) (by simp))
        have tail := ih left right (by simpa using leftLength) (by simpa using rightLength)
          (fun pair member => first pair (by simp [member]))
          (fun pair member => second pair (by simp [member]))
        exact congrArg₂ List.cons head tail

theorem ineg_results_unique {width : Nat} {input left right : uN}
    (first : fun_ineg_ width input left) (second : fun_ineg_ width input right) : left = right := by
  cases first
  cases second
  rfl

theorem iabs_results_unique {width : Nat} {input left right : uN}
    (first : fun_iabs_ width input left) (second : fun_iabs_ width input right) : left = right := by
  cases first
  cases second
  grind only [ineg_results_unique,signed_deterministic]

theorem forall2_iabs_unique {width : Nat} {inputs : List lane_} {left right : List uN}
    (leftLength : left.length = inputs.length) (rightLength : right.length = inputs.length)
    (first : Forall₂ (fun result lane => fun_iabs_ width (proj_lane__0 lane).get! result) left inputs)
    (second : Forall₂ (fun result lane => fun_iabs_ width (proj_lane__0 lane).get! result) right inputs) : left = right :=
  forall2_functional_left (fun result lane => fun_iabs_ width (proj_lane__0 lane).get! result)
    (fun _ _ _ => iabs_results_unique) inputs left right leftLength rightLength first second

theorem forall2_ineg_unique {width : Nat} {inputs : List lane_} {left right : List uN}
    (leftLength : left.length = inputs.length) (rightLength : right.length = inputs.length)
    (first : Forall₂ (fun result lane => fun_ineg_ width (proj_lane__0 lane).get! result) left inputs)
    (second : Forall₂ (fun result lane => fun_ineg_ width (proj_lane__0 lane).get! result) right inputs) : left = right :=
  forall2_functional_left (fun result lane => fun_ineg_ width (proj_lane__0 lane).get! result)
    (fun _ _ _ => ineg_results_unique) inputs left right leftLength rightLength first second

set_option maxHeartbeats 800000 in
theorem vector_unop_results_unique {shape : _root_.shape} {op : vunop_} {input : vec_}
    {left right : List vec_}
    (first : fun_vunop_ shape op input (some left))
    (second : fun_vunop_ shape op input (some right)) : left = right := by
  cases first <;> cases second
  all_goals subst_vars
  all_goals try rfl
  all_goals
    congr 3
    first
    | apply forall2_iabs_unique <;> assumption
    | apply forall2_ineg_unique <;> assumption



theorem forall3_functional_left {A B C : Type} (relation : A → B → C → Prop)
    (functional : ∀ x y input other, relation x input other → relation y input other → x = y)
    (inputs : List B) (others : List C) (left right : List A)
    (leftLength : left.length = inputs.length) (rightLength : right.length = inputs.length)
    (otherLength : others.length = inputs.length)
    (first : Forall₃ relation left inputs others) (second : Forall₃ relation right inputs others) : left = right := by
  induction inputs generalizing others left right with
  | nil =>
    have l : left = [] := by simpa using leftLength
    have r : right = [] := by simpa using rightLength
    exact l.trans r.symm
  | cons input inputs ih =>
    cases left with
    | nil => simp at leftLength
    | cons x left =>
      cases right with
      | nil => simp at rightLength
      | cons y right =>
        cases others with
        | nil => simp at otherLength
        | cons other others =>
          have head := functional x y input other
            (first ((x,input),other) (by simp)) (second ((y,input),other) (by simp))
          have tail := ih others left right (by simpa using leftLength) (by simpa using rightLength)
            (by simpa using otherLength)
            (fun pair member => first pair (by simp [member]))
            (fun pair member => second pair (by simp [member]))
          exact congrArg₂ List.cons head tail

theorem iadd_results_unique {width : Nat} {a b left right : uN}
    (first : fun_iadd_ width a b left) (second : fun_iadd_ width a b right) : left = right := by
  cases first; cases second; rfl

theorem isub_results_unique {width : Nat} {a b left right : uN}
    (first : fun_isub_ width a b left) (second : fun_isub_ width a b right) : left = right := by
  cases first; cases second; rfl

theorem imul_results_unique {width : Nat} {a b left right : uN}
    (first : fun_imul_ width a b left) (second : fun_imul_ width a b right) : left = right := by
  cases first; cases second; rfl

theorem iadd_sat_results_unique {width : Nat} {sign : sx} {a b left right : uN}
    (first : fun_iadd_sat_ width sign a b left) (second : fun_iadd_sat_ width sign a b right) : left = right := by
  cases first <;> cases second
  all_goals first | rfl | grind only [signed_deterministic,inv_signed_deterministic]

theorem isub_sat_results_unique {width : Nat} {sign : sx} {a b left right : uN}
    (first : fun_isub_sat_ width sign a b left) (second : fun_isub_sat_ width sign a b right) : left = right := by
  cases first <;> cases second
  all_goals first | rfl | grind only [signed_deterministic,inv_signed_deterministic]

theorem imin_results_unique {width : Nat} {sign : sx} {a b left right : uN}
    (first : fun_imin_ width sign a b left) (second : fun_imin_ width sign a b right) : left = right := by
  cases first <;> cases second
  all_goals first | rfl | omega | grind only [signed_deterministic]

theorem imax_results_unique {width : Nat} {sign : sx} {a b left right : uN}
    (first : fun_imax_ width sign a b left) (second : fun_imax_ width sign a b right) : left = right := by
  cases first <;> cases second
  all_goals first | rfl | omega | grind only [signed_deterministic]


private theorem forall3_iadd_unique {width : Nat}
    {inputs others : List lane_} {left right : List uN}
    (leftLength : left.length = inputs.length) (rightLength : right.length = inputs.length)
    (otherLength : others.length = inputs.length)
    (first : Forall₃ (fun result lane other => fun_iadd_ width (proj_lane__0 lane).get! (proj_lane__0 other).get! result) left inputs others)
    (second : Forall₃ (fun result lane other => fun_iadd_ width (proj_lane__0 lane).get! (proj_lane__0 other).get! result) right inputs others) : left = right :=
  forall3_functional_left (fun result lane other => fun_iadd_ width (proj_lane__0 lane).get! (proj_lane__0 other).get! result)
    (fun _ _ _ _ => iadd_results_unique) inputs others left right leftLength rightLength otherLength first second

private theorem forall3_isub_unique {width : Nat}
    {inputs others : List lane_} {left right : List uN}
    (leftLength : left.length = inputs.length) (rightLength : right.length = inputs.length)
    (otherLength : others.length = inputs.length)
    (first : Forall₃ (fun result lane other => fun_isub_ width (proj_lane__0 lane).get! (proj_lane__0 other).get! result) left inputs others)
    (second : Forall₃ (fun result lane other => fun_isub_ width (proj_lane__0 lane).get! (proj_lane__0 other).get! result) right inputs others) : left = right :=
  forall3_functional_left (fun result lane other => fun_isub_ width (proj_lane__0 lane).get! (proj_lane__0 other).get! result)
    (fun _ _ _ _ => isub_results_unique) inputs others left right leftLength rightLength otherLength first second

private theorem forall3_imul_unique {width : Nat}
    {inputs others : List lane_} {left right : List uN}
    (leftLength : left.length = inputs.length) (rightLength : right.length = inputs.length)
    (otherLength : others.length = inputs.length)
    (first : Forall₃ (fun result lane other => fun_imul_ width (proj_lane__0 lane).get! (proj_lane__0 other).get! result) left inputs others)
    (second : Forall₃ (fun result lane other => fun_imul_ width (proj_lane__0 lane).get! (proj_lane__0 other).get! result) right inputs others) : left = right :=
  forall3_functional_left (fun result lane other => fun_imul_ width (proj_lane__0 lane).get! (proj_lane__0 other).get! result)
    (fun _ _ _ _ => imul_results_unique) inputs others left right leftLength rightLength otherLength first second

private theorem forall3_iadd_sat_unique {width : Nat} {sign : sx}
    {inputs others : List lane_} {left right : List uN}
    (leftLength : left.length = inputs.length) (rightLength : right.length = inputs.length)
    (otherLength : others.length = inputs.length)
    (first : Forall₃ (fun result lane other => fun_iadd_sat_ width sign (proj_lane__0 lane).get! (proj_lane__0 other).get! result) left inputs others)
    (second : Forall₃ (fun result lane other => fun_iadd_sat_ width sign (proj_lane__0 lane).get! (proj_lane__0 other).get! result) right inputs others) : left = right :=
  forall3_functional_left (fun result lane other => fun_iadd_sat_ width sign (proj_lane__0 lane).get! (proj_lane__0 other).get! result)
    (fun _ _ _ _ => iadd_sat_results_unique) inputs others left right leftLength rightLength otherLength first second

private theorem forall3_isub_sat_unique {width : Nat} {sign : sx}
    {inputs others : List lane_} {left right : List uN}
    (leftLength : left.length = inputs.length) (rightLength : right.length = inputs.length)
    (otherLength : others.length = inputs.length)
    (first : Forall₃ (fun result lane other => fun_isub_sat_ width sign (proj_lane__0 lane).get! (proj_lane__0 other).get! result) left inputs others)
    (second : Forall₃ (fun result lane other => fun_isub_sat_ width sign (proj_lane__0 lane).get! (proj_lane__0 other).get! result) right inputs others) : left = right :=
  forall3_functional_left (fun result lane other => fun_isub_sat_ width sign (proj_lane__0 lane).get! (proj_lane__0 other).get! result)
    (fun _ _ _ _ => isub_sat_results_unique) inputs others left right leftLength rightLength otherLength first second

private theorem forall3_imin_unique {width : Nat} {sign : sx}
    {inputs others : List lane_} {left right : List uN}
    (leftLength : left.length = inputs.length) (rightLength : right.length = inputs.length)
    (otherLength : others.length = inputs.length)
    (first : Forall₃ (fun result lane other => fun_imin_ width sign (proj_lane__0 lane).get! (proj_lane__0 other).get! result) left inputs others)
    (second : Forall₃ (fun result lane other => fun_imin_ width sign (proj_lane__0 lane).get! (proj_lane__0 other).get! result) right inputs others) : left = right :=
  forall3_functional_left (fun result lane other => fun_imin_ width sign (proj_lane__0 lane).get! (proj_lane__0 other).get! result)
    (fun _ _ _ _ => imin_results_unique) inputs others left right leftLength rightLength otherLength first second

private theorem forall3_imax_unique {width : Nat} {sign : sx}
    {inputs others : List lane_} {left right : List uN}
    (leftLength : left.length = inputs.length) (rightLength : right.length = inputs.length)
    (otherLength : others.length = inputs.length)
    (first : Forall₃ (fun result lane other => fun_imax_ width sign (proj_lane__0 lane).get! (proj_lane__0 other).get! result) left inputs others)
    (second : Forall₃ (fun result lane other => fun_imax_ width sign (proj_lane__0 lane).get! (proj_lane__0 other).get! result) right inputs others) : left = right :=
  forall3_functional_left (fun result lane other => fun_imax_ width sign (proj_lane__0 lane).get! (proj_lane__0 other).get! result)
    (fun _ _ _ _ => imax_results_unique) inputs others left right leftLength rightLength otherLength first second

set_option maxHeartbeats 1600000 in
theorem vector_binop_results_unique {shape : _root_.shape} {op : vbinop_} {a b : vec_}
    {left right : List vec_}
    (first : fun_vbinop_ shape op a b (some left))
    (second : fun_vbinop_ shape op a b (some right)) : left = right := by
  cases first <;> cases second
  all_goals subst_vars
  all_goals try rfl
  all_goals
    apply congrArg (fun words : List uN => [inv_lanes_ _ (Map _ words)])
    first
    | (apply forall3_iadd_unique; rotate_left 3; all_goals first | assumption | omega)
    | (apply forall3_isub_unique; rotate_left 3; all_goals first | assumption | omega)
    | (apply forall3_imul_unique; rotate_left 3; all_goals first | assumption | omega)
    | (apply forall3_iadd_sat_unique; rotate_left 3; all_goals first | assumption | omega)
    | (apply forall3_isub_sat_unique; rotate_left 3; all_goals first | assumption | omega)
    | (apply forall3_imin_unique; rotate_left 3; all_goals first | assumption | omega)
    | (apply forall3_imax_unique; rotate_left 3; all_goals first | assumption | omega)

end Exec.Spec


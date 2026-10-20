import Exec.Spec.Typing.ValueSubtyping

/-! Result-subtype composition and value-prefix splitting for source typing. -/

namespace Exec.Spec
open SpecExt

theorem resulttype_sub_append {left left' right right' : List valtype}
    (first : Resulttype_sub (.mk_list left) (.mk_list left'))
    (second : Resulttype_sub (.mk_list right) (.mk_list right')) :
    Resulttype_sub (.mk_list (left++right)) (.mk_list (left'++right')) := by
  have before := resulttype_sub_iff.mp first
  have after := resulttype_sub_iff.mp second
  clear first second
  apply resulttype_sub_iff.mpr
  induction before with
  | nil => exact after
  | cons head tail ih => exact .cons head ih

theorem resulttype_sub_append_split {left right target : List valtype}
    (sub : Resulttype_sub (.mk_list (left++right)) (.mk_list target)) :
    ∃ before after, target = before++after ∧
      Resulttype_sub (.mk_list left) (.mk_list before) ∧ Resulttype_sub (.mk_list right) (.mk_list after) := by
  have paired := resulttype_sub_iff.mp sub
  clear sub
  induction left generalizing target with
  | nil => exact ⟨[],target,rfl,resulttype_sub_refl [],resulttype_sub_iff.mpr paired⟩
  | cons type left ih =>
    cases paired with
    | @cons _ other _ rest head tail =>
      obtain ⟨before,after,same,subBefore,subAfter⟩ := ih tail
      refine ⟨other::before,after,?_,resulttype_sub_iff.mpr (.cons head (resulttype_sub_iff.mp subBefore)),subAfter⟩
      simp [same]

theorem resultsTyped_append {s : store} {left right : List valtype} {xs ys : List val}
    (first : ResultsTyped s left xs) (second : ResultsTyped s right ys) :
    ResultsTyped s (left++right) (xs++ys) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

theorem vals_split {values : List val} {left right : List admininstr} (same : vals values = left++right) :
    ∃ xs ys, values = xs++ys ∧ left = vals xs ∧ right = vals ys := by
  refine ⟨values.take left.length,values.drop left.length,(List.take_append_drop _ _).symm,?_,?_⟩
  · have selected := congrArg (List.take left.length) same
    simpa only [vals,List.map_take,List.take_append,List.take_length,Nat.sub_self,List.take_zero,List.append_nil] using selected.symm
  · have selected := congrArg (List.drop left.length) same
    simpa only [vals,List.map_drop,List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] using selected.symm

end Exec.Spec


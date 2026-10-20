import Exec.Spec.IntegerDeterminism

/-! Result-list uniqueness is distinct from choosing a member of a permitted
floating-point result list. These lemmas retain that nondeterminism. -/
namespace Exec.Spec

/-- Every successful scalar unary judgment yields one particular permitted
result list, including all floating-point NaN and rounding alternatives. -/
theorem numeric_unop_results_unique {type : numtype} {op : unop_} {input : num_}
    {left right : List num_}
    (first : fun_unop_ type op input (some left))
    (second : fun_unop_ type op input (some right)) : left = right := by
  cases first <;> cases second <;> rfl

/-- Scalar binary source judgments agree on their permitted result list.
Integer division and remainder use their checked guarded auxiliary relations. -/
theorem numeric_binop_results_unique {type : numtype} {op : binop_} {a b : num_}
    {left right : List num_}
    (first : fun_binop_ type op a b (some left))
    (second : fun_binop_ type op a b (some right)) : left = right := by
  cases first <;> cases second
  all_goals first | rfl | skip
  all_goals try casesm* fun_iadd_ .., fun_isub_ .., fun_imul_ ..
  all_goals first | rfl | grind only [idiv_deterministic, irem_deterministic]

/-- Scalar conversion rules also yield one permitted list; float truncation
failure is represented by an empty list, and promotion retains NaN choices. -/
theorem numeric_cvtop_results_unique {source target : numtype} {op : cvtop__} {input : num_}
    {left right : List num_}
    (first : fun_cvtop__ source target op input (some left))
    (second : fun_cvtop__ source target op input (some right)) : left = right := by
  cases first <;> cases second <;> rfl

end Exec.Spec

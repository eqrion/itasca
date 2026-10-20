import Exec.Spec.Choices.NumericDeterminism

namespace Exec.Spec

/-- Scalar tests have a unique successful source result; they introduce no
floating-point, host, or allocation choice. -/
theorem numeric_testop_results_unique {type : numtype} {op : testop_} {input left right : num_}
    (first : fun_testop_ type op input (some left))
    (second : fun_testop_ type op input (some right)) : left = right := by
  cases first <;> cases second
  all_goals casesm* fun_ieqz_ ..
  all_goals rfl

/-- Scalar comparisons are deterministic even when their floating operands are
NaNs or signed zeros. Their Boolean result is distinct from a NaN choice. -/
theorem numeric_relop_results_unique {type : numtype} {op : relop_} {a b left right : num_}
    (first : fun_relop_ type op a b (some left))
    (second : fun_relop_ type op a b (some right)) : left = right := by
  cases first <;> cases second
  all_goals try casesm* fun_ieq_ .., fun_ine_ .., fun_ilt_ .., fun_igt_ .., fun_ile_ .., fun_ige_ ..
  all_goals first | rfl | grind only [signed_deterministic]

end Exec.Spec

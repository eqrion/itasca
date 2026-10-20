import Exec.Spec.Steps
namespace Exec.Spec
open SpecExt

theorem admininstr_val_injective : Function.Injective admininstr_val := by
  intro left right same
  cases left <;> cases right <;> simp_all [admininstr_val]

/-- Operand-only administrative syntax retains the complete source values. -/
theorem vals_injective : Function.Injective vals := by
  intro left right same
  induction left generalizing right with
  | nil => cases right <;> simp_all [vals]
  | cons head tail ih =>
    cases right with
    | nil => simp [vals] at same
    | cons other rest =>
      simp only [vals,List.map_cons,List.cons.injEq] at same
      have heads:=admininstr_val_injective same.1
      have tails:=ih same.2
      cases heads
      cases tails
      rfl
end Exec.Spec

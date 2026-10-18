import Exec.Interp.Relations.DecodeValue

/-! The extracted range guard checks subtraction before addition and casts only
bounded endpoints. This holds at both supported machine-index widths. -/
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem usize_to_u64_exact (value : Usize) :
    (UScalar.cast .U64 value).val = value.val := by
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  rcases Usize.bounds_eq with h | h <;> scalar_tac

def RangeEffect (start len : U64) (size : Usize) (trap : runtime.Trap)
    (result : core.result.Result (core.ops.range.Range Usize) runtime.ExecError) : Prop :=
  if start.val + len.val ≤ size.val then
    ∃ range, result = .Ok range ∧ range.start.val = start.val ∧ range.end.val = start.val + len.val
  else result = .Err (.Trap trap)

@[step] theorem range_effect (start len : U64) (size : Usize) (trap : runtime.Trap) :
    runtime.range start len size trap ⦃ result => RangeEffect start len size trap result ⦄ := by
  have sizeCast := usize_to_u64_exact size
  unfold runtime.range
  simp only [lift, bind_ok]
  split
  · rename_i outside
    simp only [WP.spec_ok, RangeEffect]
    split
    · scalar_tac
    · trivial
  · rename_i inside
    step as ⟨remaining, hremaining⟩
    split
    · rename_i outside
      simp only [WP.spec_ok, RangeEffect]
      split
      · scalar_tac
      · trivial
    · rename_i insideLength
      have fits : start.val + len.val ≤ size.val := by scalar_tac
      have startCast := cast_usize_exact start (by scalar_tac)
      step as ⟨last, hlast⟩
      have endCast := cast_usize_exact last (by scalar_tac)
      simp [RangeEffect, fits, startCast, endCast, hlast]

end Exec.Interp

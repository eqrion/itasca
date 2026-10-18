import Exec.Interp.Numeric.Float.Float
import SpecExt.Builtins.Float.TruncRange
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt.Builtins.Float

@[step] theorem overflow_effect (negative : Bool) (width : U32) (signed saturating : Bool)
    (validWidth : width = 32#u32 ∨ width = 64#u32) :
    runtime.interp.float.overflow negative width signed saturating ⦃ result =>
      if saturating then ∃ value, result = .Ok value ∧ value.val = magnitudeBoundary width.val negative signed
      else result = .Err (.Trap .IntegerOverflow) ⦄ := by
  rcases validWidth with rfl | rfl
  all_goals cases negative <;> cases signed <;> cases saturating
  all_goals simp [runtime.interp.float.overflow, magnitudeBoundary, bind_ok]
  all_goals repeat first | step | scalar_tac | simp_all
  all_goals norm_num [U32.rMax, U64.rMax, Nat.shiftRight_eq_div_pow]

end Exec.Interp

import Exec.Interp.Machines.Slice.SliceDivergence

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- One extra unit in the potential bound pays for a final failing dispatch. -/
theorem finite_prefix_div_bound (bound successes dispatches : Nat) (counted : dispatches ≤ successes + 1) :
    dispatches / (bound + 2) ≤ successes / (bound + 1) := by
  have remainder := Nat.mod_lt successes (by omega : 0 < bound + 1)
  have division := Nat.mod_add_div successes (bound + 1)
  have positive : 0 < successes / (bound + 1) + 1 := Nat.succ_pos _
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < bound + 2)).2
  simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.mul_comm] at *
  omega

end Exec.Interp

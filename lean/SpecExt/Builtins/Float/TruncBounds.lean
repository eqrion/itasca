import SpecExt.Builtins.Float.TruncSemantics
namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem convertMagnitude_zero (width : Nat) (negative signed saturating : Bool)
    (validWidth : width = 32 ∨ width = 64) :
    convertMagnitude width negative signed saturating 0 = some (.mk_uN 0) := by
  have inside : magnitudeWithin width negative signed 0 := by simp [magnitudeWithin]
  have effect := convertMagnitude_inside width 0 negative signed saturating validWidth inside
  cases negative <;> simpa using effect

theorem magnitudeLimit_bounded (width : Nat) (negative signed : Bool)
    (validWidth : width = 32 ∨ width = 64) : magnitudeLimit width negative signed < 2^64 := by
  rcases validWidth with rfl | rfl
  all_goals cases negative <;> cases signed <;> decide

theorem rawTruncMagnitude_large (fractionBits bias exponent fraction width : Nat)
    (negative signed : Bool) (validWidth : width = 32 ∨ width = 64)
    (power : 64 ≤ exponent-bias) (small : fraction < 2^fractionBits) :
    ¬magnitudeWithin width negative signed (rawTruncMagnitude fractionBits bias exponent fraction) := by
  have normal : bias ≤ exponent := by omega
  have bound := (rawTruncMagnitude_normal_bound fractionBits bias exponent fraction normal small).1
  have least : 2^64 ≤ 2^(exponent-bias) := Nat.pow_le_pow_right (by omega) power
  have limit := magnitudeLimit_bounded width negative signed validWidth
  intro inside
  have := inside.1
  omega

theorem rawTruncMagnitude_u64 (fractionBits bias exponent fraction : Nat)
    (power : exponent-bias < 64) (small : fraction < 2^fractionBits) :
    rawTruncMagnitude fractionBits bias exponent fraction < 2^64 := by
  by_cases tiny : exponent < bias
  · simp [rawTruncMagnitude, tiny]
  · have normal : bias ≤ exponent := by omega
    have bound := (rawTruncMagnitude_normal_bound fractionBits bias exponent fraction normal small).2
    have most : 2^(exponent-bias+1) ≤ 2^64 := Nat.pow_le_pow_right (by omega) (by omega)
    exact lt_of_lt_of_le bound most

end SpecExt.Builtins.Float

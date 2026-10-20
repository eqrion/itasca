import SpecExt.Builtins.Float.MinMax
import SpecExt.Builtins.Float.FirstChoice
namespace SpecExt.Builtins.Float

theorem nans_head (width : Nat) (inputs : List fN) (positive : 0<canon_ width) :
    (nans width inputs).head?=some (.POS (.NAN (canon_ width))) := by
  unfold nans
  split
  · rfl
  · exact arithmeticNaNs_head width positive

theorem raw_min32_first_choice (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    (fmin_ 32 (floatOfBits 32 a) (floatOfBits 32 b)).head?=some (floatOfBits 32 (if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then 2143289344
      else if rawEqual 2147483648 a b then a ||| b else if rawLess 2147483648 a b then a else b)) := by
  have member := raw_min32_sound a b ha hb
  by_cases nan : (isNaN (floatOfBits 32 a) || isNaN (floatOfBits 32 b))=true
  · apply (min_reply_family 32 _ _).head_of_canonical_result (by decide) member
    intro resultNan
    have rawNan : a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 := by
      simpa only [isNaN_floatOfBits_32,Bool.or_eq_true,decide_eq_true_eq] using nan
    have canonical : floatOfBits 32 2143289344=fN.POS (.NAN (canon_ 32)) := by decide +kernel
    simpa only [rawNan,ite_true] using canonical
  · have singleton : ∃ value, fmin_ 32 (floatOfBits 32 a) (floatOfBits 32 b)=[value] := by
      unfold fmin_
      rw [if_neg nan]
      split <;> exact ⟨_,rfl⟩
    obtain ⟨value,same⟩ := singleton
    rw [same] at member ⊢
    simpa only [List.head?_cons,Option.some.injEq] using (List.mem_singleton.mp member).symm

theorem raw_min64_first_choice (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    (fmin_ 64 (floatOfBits 64 a) (floatOfBits 64 b)).head?=some (floatOfBits 64 (if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then 9221120237041090560
      else if rawEqual 9223372036854775808 a b then a ||| b else if rawLess 9223372036854775808 a b then a else b)) := by
  have member := raw_min64_sound a b ha hb
  by_cases nan : (isNaN (floatOfBits 64 a) || isNaN (floatOfBits 64 b))=true
  · apply (min_reply_family 64 _ _).head_of_canonical_result (by decide) member
    intro resultNan
    have rawNan : a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 := by
      simpa only [isNaN_floatOfBits_64,Bool.or_eq_true,decide_eq_true_eq] using nan
    have canonical : floatOfBits 64 9221120237041090560=fN.POS (.NAN (canon_ 64)) := by decide +kernel
    simpa only [rawNan,ite_true] using canonical
  · have singleton : ∃ value, fmin_ 64 (floatOfBits 64 a) (floatOfBits 64 b)=[value] := by
      unfold fmin_
      rw [if_neg nan]
      split <;> exact ⟨_,rfl⟩
    obtain ⟨value,same⟩ := singleton
    rw [same] at member ⊢
    simpa only [List.head?_cons,Option.some.injEq] using (List.mem_singleton.mp member).symm

theorem raw_max32_first_choice (a b : Nat) (ha : a < 2^32) (hb : b < 2^32) :
    (fmax_ 32 (floatOfBits 32 a) (floatOfBits 32 b)).head?=some (floatOfBits 32 (if a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 then 2143289344
      else if rawEqual 2147483648 a b then a &&& b else if rawLess 2147483648 a b then b else a)) := by
  have member := raw_max32_sound a b ha hb
  by_cases nan : (isNaN (floatOfBits 32 a) || isNaN (floatOfBits 32 b))=true
  · apply (max_reply_family 32 _ _).head_of_canonical_result (by decide) member
    intro resultNan
    have rawNan : a % 2147483648 > 2139095040 ∨ b % 2147483648 > 2139095040 := by
      simpa only [isNaN_floatOfBits_32,Bool.or_eq_true,decide_eq_true_eq] using nan
    have canonical : floatOfBits 32 2143289344=fN.POS (.NAN (canon_ 32)) := by decide +kernel
    simpa only [rawNan,ite_true] using canonical
  · have singleton : ∃ value, fmax_ 32 (floatOfBits 32 a) (floatOfBits 32 b)=[value] := by
      unfold fmax_
      rw [if_neg nan]
      split <;> exact ⟨_,rfl⟩
    obtain ⟨value,same⟩ := singleton
    rw [same] at member ⊢
    simpa only [List.head?_cons,Option.some.injEq] using (List.mem_singleton.mp member).symm

theorem raw_max64_first_choice (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    (fmax_ 64 (floatOfBits 64 a) (floatOfBits 64 b)).head?=some (floatOfBits 64 (if a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 then 9221120237041090560
      else if rawEqual 9223372036854775808 a b then a &&& b else if rawLess 9223372036854775808 a b then b else a)) := by
  have member := raw_max64_sound a b ha hb
  by_cases nan : (isNaN (floatOfBits 64 a) || isNaN (floatOfBits 64 b))=true
  · apply (max_reply_family 64 _ _).head_of_canonical_result (by decide) member
    intro resultNan
    have rawNan : a % 9223372036854775808 > 9218868437227405312 ∨ b % 9223372036854775808 > 9218868437227405312 := by
      simpa only [isNaN_floatOfBits_64,Bool.or_eq_true,decide_eq_true_eq] using nan
    have canonical : floatOfBits 64 9221120237041090560=fN.POS (.NAN (canon_ 64)) := by decide +kernel
    simpa only [rawNan,ite_true] using canonical
  · have singleton : ∃ value, fmax_ 64 (floatOfBits 64 a) (floatOfBits 64 b)=[value] := by
      unfold fmax_
      rw [if_neg nan]
      split <;> exact ⟨_,rfl⟩
    obtain ⟨value,same⟩ := singleton
    rw [same] at member ⊢
    simpa only [List.head?_cons,Option.some.injEq] using (List.mem_singleton.mp member).symm

end SpecExt.Builtins.Float

import SpecExt.Builtins.Float.Encoding

/-! Every machine float bit pattern decodes to a well-formed specification float
and packs back to the same bits, including all NaN payloads and both zeros. -/

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem decoded_magnitude_bits_32 (exponent fraction : Nat) :
    magnitudeBits 32 (if exponent = 0 then fNmag.SUBNORM fraction else if exponent = 255 then if fraction = 0 then .INF else .NAN fraction else .NORM fraction ((exponent : Int) - 127)) = exponent * 8388608 + fraction := by
  split_ifs <;> simp_all [magnitudeBits, floatBias, E, fun_M, expon, signif]

theorem decoded_magnitude_wf_32 (exponent fraction : Nat)
    (he : exponent < 256) (hf : fraction < 8388608) :
    wf_fNmag 32 (if exponent = 0 then fNmag.SUBNORM fraction else if exponent = 255 then if fraction = 0 then .INF else .NAN fraction else .NORM fraction ((exponent : Int) - 127)) := by
  split_ifs with hzero hmax hfzero
  · exact .fNmag_case_1 32 (-126) fraction ⟨hf, rfl⟩
  · exact .fNmag_case_2 32
  · exact .fNmag_case_3 32 fraction ⟨by change 1 ≤ fraction; omega, hf⟩
  · apply wf_fNmag.fNmag_case_0
    change fraction < 8388608 ∧ -126 ≤ (exponent : Int) - 127 ∧
      (exponent : Int) - 127 ≤ 127
    omega

theorem float_bits_roundtrip_32 (bits : Nat) (h : bits < 2 ^ 32) :
    floatBits 32 (floatOfBits 32 bits) = bits := by
  let fraction := bits % 8388608
  let exponent := bits / 8388608 % 256
  have hf : fraction < 8388608 := Nat.mod_lt _ (by decide)
  have he : exponent < 256 := Nat.mod_lt _ (by decide)
  by_cases hs : bits < 2147483648
  · have hb : bits = exponent * 8388608 + fraction := by
      dsimp [exponent, fraction]
      omega
    conv_lhs => rw [hb, decodeFieldsPos32 exponent fraction he hf]
    change magnitudeBits 32 _ = bits
    rw [decoded_magnitude_bits_32 exponent fraction, ← hb]
  · have hb : bits = 2147483648 + (exponent * 8388608 + fraction) := by
      dsimp [exponent, fraction]
      omega
    conv_lhs => rw [hb, decodeFieldsNeg32 exponent fraction he hf]
    change 2147483648 + magnitudeBits 32 _ = bits
    rw [decoded_magnitude_bits_32 exponent fraction, ← hb]

theorem floatOfBits_wf_32 (bits : Nat) (h : bits < 2 ^ 32) :
    wf_fN 32 (floatOfBits 32 bits) := by
  let fraction := bits % 8388608
  let exponent := bits / 8388608 % 256
  have hf : fraction < 8388608 := Nat.mod_lt _ (by decide)
  have he : exponent < 256 := Nat.mod_lt _ (by decide)
  by_cases hs : bits < 2147483648
  · have hb : bits = exponent * 8388608 + fraction := by
      dsimp [exponent, fraction]
      omega
    rw [hb, decodeFieldsPos32 exponent fraction he hf]
    exact .fN_case_0 32 _ (decoded_magnitude_wf_32 exponent fraction he hf)
  · have hb : bits = 2147483648 + (exponent * 8388608 + fraction) := by
      dsimp [exponent, fraction]
      omega
    rw [hb, decodeFieldsNeg32 exponent fraction he hf]
    exact .fN_case_1 32 _ (decoded_magnitude_wf_32 exponent fraction he hf)

theorem decoded_magnitude_bits_64 (exponent fraction : Nat) :
    magnitudeBits 64 (if exponent = 0 then fNmag.SUBNORM fraction else if exponent = 2047 then if fraction = 0 then .INF else .NAN fraction else .NORM fraction ((exponent : Int) - 1023)) = exponent * 4503599627370496 + fraction := by
  split_ifs <;> simp_all [magnitudeBits, floatBias, E, fun_M, expon, signif]

theorem decoded_magnitude_wf_64 (exponent fraction : Nat)
    (he : exponent < 2048) (hf : fraction < 4503599627370496) :
    wf_fNmag 64 (if exponent = 0 then fNmag.SUBNORM fraction else if exponent = 2047 then if fraction = 0 then .INF else .NAN fraction else .NORM fraction ((exponent : Int) - 1023)) := by
  split_ifs with hzero hmax hfzero
  · exact .fNmag_case_1 64 (-1022) fraction ⟨hf, rfl⟩
  · exact .fNmag_case_2 64
  · exact .fNmag_case_3 64 fraction ⟨by change 1 ≤ fraction; omega, hf⟩
  · apply wf_fNmag.fNmag_case_0
    change fraction < 4503599627370496 ∧ -1022 ≤ (exponent : Int) - 1023 ∧
      (exponent : Int) - 1023 ≤ 1023
    omega

theorem float_bits_roundtrip_64 (bits : Nat) (h : bits < 2 ^ 64) :
    floatBits 64 (floatOfBits 64 bits) = bits := by
  let fraction := bits % 4503599627370496
  let exponent := bits / 4503599627370496 % 2048
  have hf : fraction < 4503599627370496 := Nat.mod_lt _ (by decide)
  have he : exponent < 2048 := Nat.mod_lt _ (by decide)
  by_cases hs : bits < 9223372036854775808
  · have hb : bits = exponent * 4503599627370496 + fraction := by
      dsimp [exponent, fraction]
      omega
    conv_lhs => rw [hb, decodeFieldsPos64 exponent fraction he hf]
    change magnitudeBits 64 _ = bits
    rw [decoded_magnitude_bits_64 exponent fraction, ← hb]
  · have hb : bits = 9223372036854775808 + (exponent * 4503599627370496 + fraction) := by
      dsimp [exponent, fraction]
      omega
    conv_lhs => rw [hb, decodeFieldsNeg64 exponent fraction he hf]
    change 9223372036854775808 + magnitudeBits 64 _ = bits
    rw [decoded_magnitude_bits_64 exponent fraction, ← hb]

theorem floatOfBits_wf_64 (bits : Nat) (h : bits < 2 ^ 64) :
    wf_fN 64 (floatOfBits 64 bits) := by
  let fraction := bits % 4503599627370496
  let exponent := bits / 4503599627370496 % 2048
  have hf : fraction < 4503599627370496 := Nat.mod_lt _ (by decide)
  have he : exponent < 2048 := Nat.mod_lt _ (by decide)
  by_cases hs : bits < 9223372036854775808
  · have hb : bits = exponent * 4503599627370496 + fraction := by
      dsimp [exponent, fraction]
      omega
    rw [hb, decodeFieldsPos64 exponent fraction he hf]
    exact .fN_case_0 64 _ (decoded_magnitude_wf_64 exponent fraction he hf)
  · have hb : bits = 9223372036854775808 + (exponent * 4503599627370496 + fraction) := by
      dsimp [exponent, fraction]
      omega
    rw [hb, decodeFieldsNeg64 exponent fraction he hf]
    exact .fN_case_1 64 _ (decoded_magnitude_wf_64 exponent fraction he hf)


/-- The raw magnitude test used by the Rust wrapper recognizes exactly NaNs. -/
theorem isNaN_floatOfBits_32 (bits : Nat) :
    isNaN (floatOfBits 32 bits) = decide (bits % 2147483648 > 2139095040) := by
  unfold floatOfBits
  norm_num only [fun_M, E, signif, expon]
  split_ifs <;> simp_all [isNaN, magnitude] <;> omega

/-- The raw magnitude test used by the Rust wrapper recognizes exactly NaNs. -/
theorem isNaN_floatOfBits_64 (bits : Nat) :
    isNaN (floatOfBits 64 bits) = decide (bits % 9223372036854775808 > 9218868437227405312) := by
  unfold floatOfBits
  norm_num only [fun_M, E, signif, expon]
  split_ifs <;> simp_all [isNaN, magnitude] <;> omega

/-- Decoding is total even for naturals with high bits beyond the format. -/
theorem floatOfBits_wf (width : Nat) (hw : width = 32 ∨ width = 64) (bits : Nat) :
    wf_fN width (floatOfBits width bits) := by
  rcases hw with rfl | rfl
  · unfold floatOfBits
    norm_num [fun_M, E, signif, expon, floatBias]
    split <;> first
    | exact .fN_case_0 32 _ (decoded_magnitude_wf_32 _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)))
    | exact .fN_case_1 32 _ (decoded_magnitude_wf_32 _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)))
  · unfold floatOfBits
    norm_num [fun_M, E, signif, expon, floatBias]
    split <;> first
    | exact .fN_case_0 64 _ (decoded_magnitude_wf_64 _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)))
    | exact .fN_case_1 64 _ (decoded_magnitude_wf_64 _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)))

end SpecExt.Builtins.Float

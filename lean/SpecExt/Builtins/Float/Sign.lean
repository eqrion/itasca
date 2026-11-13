import «wasm2.0»
import Mathlib.Tactic

/-!
Sections, each formerly its own module: Encoding, Decoding, Lemmas, RoundingLemmas, Canonical, Wf, Sign.
-/

/-! ## Encoding -/

section

/-! Bit-field decoding and representation roundtrips for both IEEE widths.
These proofs cover every well-formed float, including arbitrary NaN payloads. -/

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem decodeFieldsPos32 (e m : Nat) (he : e < 256) (hm : m < 8388608) :
  floatOfBits 32 (e * 8388608 + m) =
    .POS (if e = 0 then .SUBNORM m else if e = 255 then
      if m = 0 then .INF else .NAN m else .NORM m ((e : Int) - 127)) := by
  have hs : (e * 8388608 + m) / 2147483648 % 2 = 0 := by omega
  have hx : (e * 8388608 + m) / 8388608 % 256 = e := by omega
  have hi : ((e : Int) * 8388608 + m) / 8388608 % 256 - 127 = (e : Int) - 127 := by omega
  norm_num [floatOfBits, fun_M, E, signif, expon, floatBias]
  simp only [hs, hx, Nat.mod_eq_of_lt hm, hi, ite_true]
theorem decodeFieldsNeg32 (e m : Nat) (he : e < 256) (hm : m < 8388608) :
  floatOfBits 32 (2147483648 + (e * 8388608 + m)) =
    .NEG (if e = 0 then .SUBNORM m else if e = 255 then
      if m = 0 then .INF else .NAN m else .NORM m ((e : Int) - 127)) := by
  have hs : ((e * 8388608 + m) / 2147483648 + 1) % 2 = 1 := by omega
  have hf : (2147483648 + (e * 8388608 + m)) % 8388608 = m := by omega
  have hx : (2147483648 + (e * 8388608 + m)) / 8388608 % 256 = e := by omega
  have hi : (2147483648 + ((e : Int) * 8388608 + m)) / 8388608 % 256 - 127 = (e : Int) - 127 := by omega
  norm_num [floatOfBits, fun_M, E, signif, expon, floatBias]
  simp only [hs, hx, hf, hi, show (1 : Nat) = 0 ↔ False from by decide, ite_false]

theorem decodeFieldsPos64 (e m : Nat) (he : e < 2048) (hm : m < 4503599627370496) :
  floatOfBits 64 (e * 4503599627370496 + m) =
    .POS (if e = 0 then .SUBNORM m else if e = 2047 then
      if m = 0 then .INF else .NAN m else .NORM m ((e : Int) - 1023)) := by
  have hs : (e * 4503599627370496 + m) / 9223372036854775808 % 2 = 0 := by omega
  have hx : (e * 4503599627370496 + m) / 4503599627370496 % 2048 = e := by omega
  have hi : ((e : Int) * 4503599627370496 + m) / 4503599627370496 % 2048 - 1023 = (e : Int) - 1023 := by omega
  norm_num [floatOfBits, fun_M, E, signif, expon, floatBias]
  simp only [hs, hx, Nat.mod_eq_of_lt hm, hi, ite_true]
theorem decodeFieldsNeg64 (e m : Nat) (he : e < 2048) (hm : m < 4503599627370496) :
  floatOfBits 64 (9223372036854775808 + (e * 4503599627370496 + m)) =
    .NEG (if e = 0 then .SUBNORM m else if e = 2047 then
      if m = 0 then .INF else .NAN m else .NORM m ((e : Int) - 1023)) := by
  have hs : ((e * 4503599627370496 + m) / 9223372036854775808 + 1) % 2 = 1 := by omega
  have hf : (9223372036854775808 + (e * 4503599627370496 + m)) % 4503599627370496 = m := by omega
  have hx : (9223372036854775808 + (e * 4503599627370496 + m)) / 4503599627370496 % 2048 = e := by omega
  have hi : (9223372036854775808 + ((e : Int) * 4503599627370496 + m)) / 4503599627370496 % 2048 - 1023 = (e : Int) - 1023 := by omega
  norm_num [floatOfBits, fun_M, E, signif, expon, floatBias]
  simp only [hs, hx, hf, hi, show (1 : Nat) = 0 ↔ False from by decide, ite_false]

theorem float_roundtrip_32 (value : fN) (h : wf_fN 32 value) :
    floatOfBits 32 (floatBits 32 value) = value := by
  cases h with
  | fN_case_0 mag hm =>
    cases hm with
    | fNmag_case_0 fraction exponent bounds =>
      change Nat at fraction
      change Int at exponent
      have hb : fraction < 8388608 ∧ -126 ≤ exponent ∧ exponent ≤ 127 := by
        exact bounds
      have he : (exponent + 127).toNat < 256 := by omega
      have h0 : (exponent + 127).toNat ≠ 0 := by omega
      have hmax : (exponent + 127).toNat ≠ 255 := by omega
      have hexp : ((exponent + 127).toNat : Int) - 127 = exponent := by omega
      change floatOfBits 32 ((exponent + 127).toNat * 8388608 + fraction) = .POS (.NORM fraction exponent)
      rw [decodeFieldsPos32 _ _ he hb.1]
      simp only [if_neg h0, if_neg hmax, hexp]
    | fNmag_case_1 exponent fraction bounds =>
      change Nat at fraction
      change Int at exponent
      have hm : fraction < 8388608 := by
        norm_num [fun_M, signif] at bounds
        exact bounds.1
      change floatOfBits 32 (fraction) = .POS (.SUBNORM fraction)
      simpa using decodeFieldsPos32 0 fraction (by decide) hm
    | fNmag_case_2 => decide +kernel
    | fNmag_case_3 payload bounds =>
      change Nat at payload
      have hb : 1 ≤ payload ∧ payload < 8388608 := by
        simpa [fun_M, signif] using bounds
      have hn : payload ≠ 0 := by omega
      change floatOfBits 32 (2139095040 + payload) = .POS (.NAN payload)
      simpa [hn] using decodeFieldsPos32 255 payload (by decide) hb.2
  | fN_case_1 mag hm =>
    cases hm with
    | fNmag_case_0 fraction exponent bounds =>
      change Nat at fraction
      change Int at exponent
      have hb : fraction < 8388608 ∧ -126 ≤ exponent ∧ exponent ≤ 127 := by
        exact bounds
      have he : (exponent + 127).toNat < 256 := by omega
      have h0 : (exponent + 127).toNat ≠ 0 := by omega
      have hmax : (exponent + 127).toNat ≠ 255 := by omega
      have hexp : ((exponent + 127).toNat : Int) - 127 = exponent := by omega
      change floatOfBits 32 (2147483648 + ((exponent + 127).toNat * 8388608 + fraction)) = .NEG (.NORM fraction exponent)
      rw [decodeFieldsNeg32 _ _ he hb.1]
      simp only [if_neg h0, if_neg hmax, hexp]
    | fNmag_case_1 exponent fraction bounds =>
      change Nat at fraction
      change Int at exponent
      have hm : fraction < 8388608 := by
        norm_num [fun_M, signif] at bounds
        exact bounds.1
      change floatOfBits 32 (2147483648 + fraction) = .NEG (.SUBNORM fraction)
      simpa using decodeFieldsNeg32 0 fraction (by decide) hm
    | fNmag_case_2 => decide +kernel
    | fNmag_case_3 payload bounds =>
      change Nat at payload
      have hb : 1 ≤ payload ∧ payload < 8388608 := by
        simpa [fun_M, signif] using bounds
      have hn : payload ≠ 0 := by omega
      change floatOfBits 32 (2147483648 + (2139095040 + payload)) = .NEG (.NAN payload)
      simpa [hn] using decodeFieldsNeg32 255 payload (by decide) hb.2

theorem float_roundtrip_64 (value : fN) (h : wf_fN 64 value) :
    floatOfBits 64 (floatBits 64 value) = value := by
  cases h with
  | fN_case_0 mag hm =>
    cases hm with
    | fNmag_case_0 fraction exponent bounds =>
      change Nat at fraction
      change Int at exponent
      have hb : fraction < 4503599627370496 ∧ -1022 ≤ exponent ∧ exponent ≤ 1023 := by
        exact bounds
      have he : (exponent + 1023).toNat < 2048 := by omega
      have h0 : (exponent + 1023).toNat ≠ 0 := by omega
      have hmax : (exponent + 1023).toNat ≠ 2047 := by omega
      have hexp : ((exponent + 1023).toNat : Int) - 1023 = exponent := by omega
      change floatOfBits 64 ((exponent + 1023).toNat * 4503599627370496 + fraction) = .POS (.NORM fraction exponent)
      rw [decodeFieldsPos64 _ _ he hb.1]
      simp only [if_neg h0, if_neg hmax, hexp]
    | fNmag_case_1 exponent fraction bounds =>
      change Nat at fraction
      change Int at exponent
      have hm : fraction < 4503599627370496 := by
        norm_num [fun_M, signif] at bounds
        exact bounds.1
      change floatOfBits 64 (fraction) = .POS (.SUBNORM fraction)
      simpa using decodeFieldsPos64 0 fraction (by decide) hm
    | fNmag_case_2 => decide +kernel
    | fNmag_case_3 payload bounds =>
      change Nat at payload
      have hb : 1 ≤ payload ∧ payload < 4503599627370496 := by
        simpa [fun_M, signif] using bounds
      have hn : payload ≠ 0 := by omega
      change floatOfBits 64 (9218868437227405312 + payload) = .POS (.NAN payload)
      simpa [hn] using decodeFieldsPos64 2047 payload (by decide) hb.2
  | fN_case_1 mag hm =>
    cases hm with
    | fNmag_case_0 fraction exponent bounds =>
      change Nat at fraction
      change Int at exponent
      have hb : fraction < 4503599627370496 ∧ -1022 ≤ exponent ∧ exponent ≤ 1023 := by
        exact bounds
      have he : (exponent + 1023).toNat < 2048 := by omega
      have h0 : (exponent + 1023).toNat ≠ 0 := by omega
      have hmax : (exponent + 1023).toNat ≠ 2047 := by omega
      have hexp : ((exponent + 1023).toNat : Int) - 1023 = exponent := by omega
      change floatOfBits 64 (9223372036854775808 + ((exponent + 1023).toNat * 4503599627370496 + fraction)) = .NEG (.NORM fraction exponent)
      rw [decodeFieldsNeg64 _ _ he hb.1]
      simp only [if_neg h0, if_neg hmax, hexp]
    | fNmag_case_1 exponent fraction bounds =>
      change Nat at fraction
      change Int at exponent
      have hm : fraction < 4503599627370496 := by
        norm_num [fun_M, signif] at bounds
        exact bounds.1
      change floatOfBits 64 (9223372036854775808 + fraction) = .NEG (.SUBNORM fraction)
      simpa using decodeFieldsNeg64 0 fraction (by decide) hm
    | fNmag_case_2 => decide +kernel
    | fNmag_case_3 payload bounds =>
      change Nat at payload
      have hb : 1 ≤ payload ∧ payload < 4503599627370496 := by
        simpa [fun_M, signif] using bounds
      have hn : payload ≠ 0 := by omega
      change floatOfBits 64 (9223372036854775808 + (9218868437227405312 + payload)) = .NEG (.NAN payload)
      simpa [hn] using decodeFieldsNeg64 2047 payload (by decide) hb.2

theorem floatBits_lt_32 (value : fN) (h : wf_fN 32 value) :
    floatBits 32 value < 2 ^ 32 := by
  cases h with
  | fN_case_0 mag hm =>
    cases hm with
    | fNmag_case_0 fraction exponent bounds =>
      change Nat at fraction
      change Int at exponent
      have hb : fraction < 8388608 ∧ -126 ≤ exponent ∧ exponent ≤ 127 := bounds
      change (exponent + 127).toNat * 8388608 + fraction < 4294967296
      omega
    | fNmag_case_1 exponent fraction bounds =>
      change Nat at fraction
      have hb : fraction < 8388608 := bounds.1
      change fraction < 4294967296
      omega
    | fNmag_case_2 => decide +kernel
    | fNmag_case_3 payload bounds =>
      change Nat at payload
      have hb : payload < 8388608 := bounds.2
      change 2139095040 + payload < 4294967296
      omega
  | fN_case_1 mag hm =>
    cases hm with
    | fNmag_case_0 fraction exponent bounds =>
      change Nat at fraction
      change Int at exponent
      have hb : fraction < 8388608 ∧ -126 ≤ exponent ∧ exponent ≤ 127 := bounds
      change 2147483648 + ((exponent + 127).toNat * 8388608 + fraction) < 4294967296
      omega
    | fNmag_case_1 exponent fraction bounds =>
      change Nat at fraction
      have hb : fraction < 8388608 := bounds.1
      change 2147483648 + fraction < 4294967296
      omega
    | fNmag_case_2 => decide +kernel
    | fNmag_case_3 payload bounds =>
      change Nat at payload
      have hb : payload < 8388608 := bounds.2
      change 2147483648 + (2139095040 + payload) < 4294967296
      omega

theorem floatBits_lt_64 (value : fN) (h : wf_fN 64 value) :
    floatBits 64 value < 2 ^ 64 := by
  cases h with
  | fN_case_0 mag hm =>
    cases hm with
    | fNmag_case_0 fraction exponent bounds =>
      change Nat at fraction
      change Int at exponent
      have hb : fraction < 4503599627370496 ∧ -1022 ≤ exponent ∧ exponent ≤ 1023 := bounds
      change (exponent + 1023).toNat * 4503599627370496 + fraction < 18446744073709551616
      omega
    | fNmag_case_1 exponent fraction bounds =>
      change Nat at fraction
      have hb : fraction < 4503599627370496 := bounds.1
      change fraction < 18446744073709551616
      omega
    | fNmag_case_2 => decide +kernel
    | fNmag_case_3 payload bounds =>
      change Nat at payload
      have hb : payload < 4503599627370496 := bounds.2
      change 9218868437227405312 + payload < 18446744073709551616
      omega
  | fN_case_1 mag hm =>
    cases hm with
    | fNmag_case_0 fraction exponent bounds =>
      change Nat at fraction
      change Int at exponent
      have hb : fraction < 4503599627370496 ∧ -1022 ≤ exponent ∧ exponent ≤ 1023 := bounds
      change 9223372036854775808 + ((exponent + 1023).toNat * 4503599627370496 + fraction) < 18446744073709551616
      omega
    | fNmag_case_1 exponent fraction bounds =>
      change Nat at fraction
      have hb : fraction < 4503599627370496 := bounds.1
      change 9223372036854775808 + fraction < 18446744073709551616
      omega
    | fNmag_case_2 => decide +kernel
    | fNmag_case_3 payload bounds =>
      change Nat at payload
      have hb : payload < 4503599627370496 := bounds.2
      change 9223372036854775808 + (9218868437227405312 + payload) < 18446744073709551616
      omega

end SpecExt.Builtins.Float

end

/-! ## Decoding -/

section

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

end

/-! ## Lemmas -/

section

/-! Kernel-checked facts about the specification's NaN choices. In particular,
a wrapper that canonicalizes a permitted arithmetic NaN remains in the result
set; it need not reproduce an implementation-selected payload or sign. -/

namespace SpecExt.Builtins.Float

theorem positive_canonical_mem (width : Nat) :
    fN.POS (.NAN (canon_ width)) ∈ canonicalNaNs width := by
  simp [canonicalNaNs]

theorem negative_canonical_mem (width : Nat) :
    fN.NEG (.NAN (canon_ width)) ∈ canonicalNaNs width := by
  simp [canonicalNaNs]

theorem positive_canonical_mem_arithmetic (width : Nat) (h : 0 < canon_ width) :
    fN.POS (.NAN (canon_ width)) ∈ arithmeticNaNs width := by
  apply List.mem_flatMap.mpr
  exact ⟨0, List.mem_range.mpr h, by simp⟩

theorem negative_canonical_mem_arithmetic (width : Nat) (h : 0 < canon_ width) :
    fN.NEG (.NAN (canon_ width)) ∈ arithmeticNaNs width := by
  apply List.mem_flatMap.mpr
  exact ⟨0, List.mem_range.mpr h, by simp⟩

theorem positive_canonical_mem_nans (width : Nat) (inputs : List fN)
    (h : 0 < canon_ width) : fN.POS (.NAN (canon_ width)) ∈ nans width inputs := by
  unfold nans
  split
  · exact positive_canonical_mem width
  · exact positive_canonical_mem_arithmetic width h

theorem canonical_positive_32 : 0 < canon_ 32 := by decide
theorem canonical_positive_64 : 0 < canon_ 64 := by decide

theorem abs_preserves_payload (width payload : Nat) (sign : Bool) :
    fabs_ width (withSign sign (.NAN payload)) = [.POS (.NAN payload)] := by
  cases sign <;> rfl

theorem copysign_preserves_magnitude (width : Nat) (mag : fNmag) (a b : Bool) :
    fcopysign_ width (withSign a mag) (withSign b (.SUBNORM 0)) = [withSign b mag] := by
  cases a <;> cases b <;> rfl

end SpecExt.Builtins.Float

end

/-! ## RoundingLemmas -/

section

/-! Range facts for rational rounding. The binary search and final adjacent
choice never construct a NaN encoding, independently of rounding accuracy. -/

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem floorEncoding_bound (width : Nat) (square : Bool) (q : Rat)
    (fuel lo hi bound : Nat) (hlo : lo ≤ bound) (hhi : hi ≤ bound) :
    floorEncoding width square q fuel lo hi ≤ bound := by
  induction fuel generalizing lo hi with
  | zero => exact hlo
  | succ fuel ih =>
    simp only [floorEncoding]
    have hm : (lo + hi + 1) / 2 ≤ bound := by omega
    split_ifs <;> first
    | exact ih _ _ hm hhi
    | exact ih _ _ hlo (by omega)

theorem roundMagnitude_noNaN_32 (square : Bool) (q : Rat) :
    isNaN (.POS (roundMagnitude 32 square q)) = false := by
  have hb := floorEncoding_bound 32 square q 32 0 (infinityBits 32 - 1)
    (infinityBits 32 - 1) (Nat.zero_le _) (Nat.le_refl _)
  norm_num [infinityBits, E, fun_M, signif, expon] at hb
  unfold roundMagnitude
  simp only [show infinityBits 32 = 2139095040 from rfl, Nat.reduceSub]
  change isNaN (floatOfBits 32 _) = false
  rw [isNaN_floatOfBits_32]
  split_ifs <;> simp only [decide_eq_false_iff_not, not_lt] <;>
    exact le_trans (Nat.mod_le _ _) (by omega)

theorem roundMagnitude_noNaN_64 (square : Bool) (q : Rat) :
    isNaN (.POS (roundMagnitude 64 square q)) = false := by
  have hb := floorEncoding_bound 64 square q 64 0 (infinityBits 64 - 1)
    (infinityBits 64 - 1) (Nat.zero_le _) (Nat.le_refl _)
  norm_num [infinityBits, E, fun_M, signif, expon] at hb
  unfold roundMagnitude
  simp only [show infinityBits 64 = 9218868437227405312 from rfl, Nat.reduceSub]
  change isNaN (floatOfBits 64 _) = false
  rw [isNaN_floatOfBits_64]
  split_ifs <;> simp only [decide_eq_false_iff_not, not_lt] <;>
    exact le_trans (Nat.mod_le _ _) (by omega)

theorem roundMagnitude_noNaN (width : Nat) (hw : width = 32 ∨ width = 64)
    (square : Bool) (q : Rat) : isNaN (.POS (roundMagnitude width square q)) = false := by
  rcases hw with rfl | rfl
  · exact roundMagnitude_noNaN_32 square q
  · exact roundMagnitude_noNaN_64 square q

theorem round_noNaN (width : Nat) (hw : width = 32 ∨ width = 64)
    (q : Rat) (negativeZero : Bool) : isNaN (round width q negativeZero) = false := by
  unfold round
  split_ifs
  · cases negativeZero <;> rfl
  · change isNaN (.POS (roundMagnitude width false (-q))) = false
    exact roundMagnitude_noNaN width hw false (-q)
  · exact roundMagnitude_noNaN width hw false q

theorem roundSqrt_noNaN (width : Nat) (hw : width = 32 ∨ width = 64)
    (q : Rat) : isNaN (roundSqrt width q) = false :=
  roundMagnitude_noNaN width hw true q

end SpecExt.Builtins.Float

end

/-! ## Canonical -/

section

/-! Arithmetic result sets remain valid after a wrapper replaces a permitted
NaN with the positive canonical NaN. This property is proved from the concrete
builtins; it is not an additional embedding assumption. -/

namespace SpecExt.Builtins.Float

/-- Closure under the interpreter's NaN replacement. -/
def CanonicalClosed (width : Nat) (allowed : List fN) : Prop :=
  (∃ choice ∈ allowed, isNaN choice = true) → .POS (.NAN (canon_ width)) ∈ allowed

theorem canonicalClosed_nans (width : Nat) (inputs : List fN) (h : 0 < canon_ width) :
    CanonicalClosed width (nans width inputs) := by
  intro _
  exact positive_canonical_mem_nans width inputs h

theorem canonicalClosed_singleton (width : Nat) (value : fN)
    (h : isNaN value = false) : CanonicalClosed width [value] := by
  rintro ⟨choice, hc, hn⟩
  simp only [List.mem_singleton] at hc
  subst choice
  simp [h] at hn

theorem canonical_positive (width : Nat) (hw : width = 32 ∨ width = 64) :
    0 < canon_ width := by
  rcases hw with rfl | rfl
  · exact canonical_positive_32
  · exact canonical_positive_64

theorem withSign_INF_noNaN (sign : Bool) : isNaN (withSign sign .INF) = false := by
  cases sign <;> rfl

theorem withSign_zero_noNaN (sign : Bool) : isNaN (withSign sign (.SUBNORM 0)) = false := by
  cases sign <;> rfl

theorem canonicalClosed_add (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN) :
    CanonicalClosed width (fadd_ width a b) := by
  unfold fadd_
  split_ifs with hn
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · apply canonicalClosed_singleton
    simp_all
  · apply canonicalClosed_singleton
    simp_all
  · exact canonicalClosed_singleton _ _ (round_noNaN width hw _ _)

theorem canonicalClosed_sub (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN) :
    CanonicalClosed width (fsub_ width a b) := by
  unfold fsub_
  split
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_add width hw _ _

theorem canonicalClosed_mul (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN) :
    CanonicalClosed width (fmul_ width a b) := by
  unfold fmul_
  split_ifs
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_singleton _ _ (withSign_INF_noNaN _)
  · exact canonicalClosed_singleton _ _ (round_noNaN width hw _ _)

theorem canonicalClosed_div (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN) :
    CanonicalClosed width (fdiv_ width a b) := by
  unfold fdiv_
  split_ifs
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_singleton _ _ (withSign_INF_noNaN _)
  · exact canonicalClosed_singleton _ _ (withSign_zero_noNaN _)
  · exact canonicalClosed_singleton _ _ (round_noNaN width hw _ _)

theorem canonicalClosed_sqrt (width : Nat) (hw : width = 32 ∨ width = 64) (a : fN) :
    CanonicalClosed width (fsqrt_ width a) := by
  unfold fsqrt_
  split_ifs with hn
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_singleton _ _ (Bool.eq_false_iff.mpr hn)
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_singleton _ _ (Bool.eq_false_iff.mpr hn)
  · exact canonicalClosed_singleton _ _ (roundSqrt_noNaN width hw _)

theorem canonicalClosed_integral (width : Nat) (hw : width = 32 ∨ width = 64)
    (op : Rat → Int) (a : fN) : CanonicalClosed width (integral op width a) := by
  unfold integral
  split_ifs with hn
  · exact canonicalClosed_nans _ _ (canonical_positive width hw)
  · exact canonicalClosed_singleton _ _ (Bool.eq_false_iff.mpr hn)
  · exact canonicalClosed_singleton _ _ (round_noNaN width hw _ _)

theorem canonicalClosed_convert (source target : Nat) (hw : target = 32 ∨ target = 64)
    (sign : sx) (a : iN) : CanonicalClosed target [convert__ source target sign a] := by
  exact canonicalClosed_singleton _ _ (round_noNaN target hw _ _)

theorem canonicalClosed_demote (source target : Nat) (hw : target = 32 ∨ target = 64)
    (a : fN) : CanonicalClosed target (demote__ source target a) := by
  unfold demote__
  split_ifs with hn
  · intro _; exact positive_canonical_mem target
  · intro _; exact positive_canonical_mem_arithmetic target (canonical_positive target hw)
  · exact canonicalClosed_singleton _ _ (Bool.eq_false_iff.mpr hn)
  · exact canonicalClosed_singleton _ _ (round_noNaN target hw _ _)

end SpecExt.Builtins.Float

end

/-! ## Wf -/

section

/-! Well-formedness of the complete arithmetic result sets, including every
permitted sign and payload of a nondeterministic NaN result. -/

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem magnitude_wf {width : Nat} {value : fN} (h : wf_fN width value) :
    wf_fNmag width (magnitude value) := by
  cases h <;> assumption

theorem withSign_wf {width : Nat} {value : fNmag} (h : wf_fNmag width value)
    (sign : Bool) : wf_fN width (withSign sign value) := by
  cases sign
  · exact .fN_case_0 _ _ h
  · exact .fN_case_1 _ _ h

theorem zero_wf (width : Nat) : wf_fNmag width (.SUBNORM 0) :=
  .fNmag_case_1 width _ 0 ⟨Nat.two_pow_pos _, rfl⟩

theorem roundMagnitude_wf (width : Nat) (hw : width = 32 ∨ width = 64)
    (square : Bool) (q : Rat) : wf_fNmag width (roundMagnitude width square q) := by
  unfold roundMagnitude
  exact magnitude_wf (floatOfBits_wf width hw _)

theorem round_wf (width : Nat) (hw : width = 32 ∨ width = 64)
    (q : Rat) (negativeZero : Bool) : wf_fN width (round width q negativeZero) := by
  unfold round
  split_ifs
  · exact withSign_wf (zero_wf width) _
  · exact .fN_case_1 _ _ (roundMagnitude_wf width hw _ _)
  · exact .fN_case_0 _ _ (roundMagnitude_wf width hw _ _)

theorem roundSqrt_wf (width : Nat) (hw : width = 32 ∨ width = 64)
    (q : Rat) : wf_fN width (roundSqrt width q) :=
  .fN_case_0 _ _ (roundMagnitude_wf width hw _ _)

theorem nan_payload_wf (width : Nat) (hw : width = 32 ∨ width = 64)
    (offset : Nat) (h : offset < canon_ width) :
    wf_fNmag width (.NAN (canon_ width + offset)) := by
  apply wf_fNmag.fNmag_case_3
  rcases hw with rfl | rfl
  · change offset < 4194304 at h
    change 1 ≤ 4194304 + offset ∧ 4194304 + offset < 8388608
    omega
  · change offset < 2251799813685248 at h
    change 1 ≤ 2251799813685248 + offset ∧ 2251799813685248 + offset < 4503599627370496
    omega

theorem canonicalNaNs_wf (width : Nat) (hw : width = 32 ∨ width = 64) :
    Forall (wf_fN width) (canonicalNaNs width) := by
  intro value hv
  have hn : wf_fNmag width (.NAN (canon_ width)) := by
    simpa using nan_payload_wf width hw 0 (canonical_positive width hw)
  simp only [canonicalNaNs, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact .fN_case_0 _ _ hn
  · exact .fN_case_1 _ _ hn

theorem arithmeticNaNs_wf (width : Nat) (hw : width = 32 ∨ width = 64) :
    Forall (wf_fN width) (arithmeticNaNs width) := by
  intro value hv
  obtain ⟨offset, ho, hv⟩ := List.mem_flatMap.mp hv
  have hn := nan_payload_wf width hw offset (List.mem_range.mp ho)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact .fN_case_0 _ _ hn
  · exact .fN_case_1 _ _ hn

theorem nans_wf (width : Nat) (hw : width = 32 ∨ width = 64) (inputs : List fN) :
    Forall (wf_fN width) (nans width inputs) := by
  unfold nans
  split
  · exact canonicalNaNs_wf width hw
  · exact arithmeticNaNs_wf width hw

theorem singleton_wf {width : Nat} {value : fN} (h : wf_fN width value) :
    Forall (wf_fN width) [value] := by
  intro v hv
  simpa only [List.mem_singleton.mp hv] using h

theorem add_wf (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN)
    (ha : wf_fN width a) (hb : wf_fN width b) :
    Forall (wf_fN width) (fadd_ width a b) := by
  unfold fadd_
  split_ifs
  · exact nans_wf width hw _
  · exact nans_wf width hw _
  · exact singleton_wf ha
  · exact singleton_wf hb
  · exact singleton_wf (round_wf width hw _ _)

theorem sub_wf (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN)
    (ha : wf_fN width a) (hb : wf_fN width b) :
    Forall (wf_fN width) (fsub_ width a b) := by
  unfold fsub_
  split
  · exact nans_wf width hw _
  · exact add_wf width hw _ _ ha (withSign_wf (magnitude_wf hb) _)

theorem mul_wf (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN) :
    Forall (wf_fN width) (fmul_ width a b) := by
  unfold fmul_
  split_ifs
  · exact nans_wf width hw _
  · exact nans_wf width hw _
  · exact singleton_wf (withSign_wf (.fNmag_case_2 width) _)
  · exact singleton_wf (round_wf width hw _ _)

theorem div_wf (width : Nat) (hw : width = 32 ∨ width = 64) (a b : fN) :
    Forall (wf_fN width) (fdiv_ width a b) := by
  unfold fdiv_
  split_ifs
  · exact nans_wf width hw _
  · exact nans_wf width hw _
  · exact singleton_wf (withSign_wf (.fNmag_case_2 width) _)
  · exact singleton_wf (withSign_wf (zero_wf width) _)
  · exact singleton_wf (round_wf width hw _ _)

theorem sqrt_wf (width : Nat) (hw : width = 32 ∨ width = 64) (a : fN)
    (ha : wf_fN width a) : Forall (wf_fN width) (fsqrt_ width a) := by
  unfold fsqrt_
  split_ifs
  · exact nans_wf width hw _
  · exact singleton_wf ha
  · exact nans_wf width hw _
  · exact singleton_wf ha
  · exact singleton_wf (roundSqrt_wf width hw _)

theorem integral_wf (width : Nat) (hw : width = 32 ∨ width = 64)
    (op : Rat → Int) (a : fN) (ha : wf_fN width a) :
    Forall (wf_fN width) (integral op width a) := by
  unfold integral
  split_ifs
  · exact nans_wf width hw _
  · exact singleton_wf ha
  · exact singleton_wf (round_wf width hw _ _)

end SpecExt.Builtins.Float

end

/-! ## Sign -/

section

/-! Raw sign-bit operations preserve every magnitude bit, including NaN payloads. -/
namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem floatOfBits_abs32 (bits : Nat) :
    floatOfBits 32 (bits % 2147483648) = .POS (magnitude (floatOfBits 32 bits)) := by
  have he : (bits % 2147483648) / 8388608 % 256 = bits / 8388608 % 256 := by omega
  have hm : bits % 2147483648 % 8388608 = bits % 8388608 := by omega
  have hs : (bits % 2147483648) / 2147483648 % 2 = 0 := by omega
  simp only [floatOfBits, show fun_M 32 = 23 from rfl, show E 32 = 8 from rfl,
    floatBias, Nat.reduceSub, Nat.reducePow]
  simp only [he, hm, hs, if_true]
  split_ifs <;> simp_all [magnitude]

theorem floatOfBits_abs64 (bits : Nat) :
    floatOfBits 64 (bits % 9223372036854775808) = .POS (magnitude (floatOfBits 64 bits)) := by
  have he : (bits % 9223372036854775808) / 4503599627370496 % 2048 = bits / 4503599627370496 % 2048 := by omega
  have hm : bits % 9223372036854775808 % 4503599627370496 = bits % 4503599627370496 := by omega
  have hs : (bits % 9223372036854775808) / 9223372036854775808 % 2 = 0 := by omega
  simp only [floatOfBits, show fun_M 64 = 52 from rfl, show E 64 = 11 from rfl,
    floatBias, Nat.reduceSub, Nat.reducePow]
  simp only [he, hm, hs, if_true]
  split_ifs <;> simp_all [magnitude]

theorem floatOfBits_neg32 (bits : Nat) :
    floatOfBits 32 (bits ^^^ 2147483648) =
      withSign (!negative (floatOfBits 32 bits)) (magnitude (floatOfBits 32 bits)) := by
  have hm : (bits ^^^ 2147483648) % 8388608 = bits % 8388608 := by
    change (bits ^^^ 2 ^ 31) % 2 ^ 23 = bits % 2 ^ 23
    rw [Nat.xor_mod_two_pow]
    norm_num
  have he : (bits ^^^ 2147483648) / 8388608 % 256 = bits / 8388608 % 256 := by
    change (bits ^^^ 2 ^ 31) / 2 ^ 23 % 2 ^ 8 = bits / 2 ^ 23 % 2 ^ 8
    rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow]
    norm_num
  have hs : (bits ^^^ 2147483648) / 2147483648 % 2 = (bits / 2147483648 % 2) ^^^ 1 := by
    change (bits ^^^ 2 ^ 31) / 2 ^ 31 % 2 ^ 1 = _
    rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow]
    norm_num
  have hz : bits / 2147483648 % 2 = 0 ∨ bits / 2147483648 % 2 = 1 := by omega
  simp only [floatOfBits, show fun_M 32 = 23 from rfl, show E 32 = 8 from rfl,
    floatBias, Nat.reduceSub, Nat.reducePow]
  rw [hm, he, hs]
  rcases hz with hz | hz <;> simp [hz, negative, magnitude, withSign]

theorem floatOfBits_neg64 (bits : Nat) :
    floatOfBits 64 (bits ^^^ 9223372036854775808) =
      withSign (!negative (floatOfBits 64 bits)) (magnitude (floatOfBits 64 bits)) := by
  have hm : (bits ^^^ 9223372036854775808) % 4503599627370496 = bits % 4503599627370496 := by
    change (bits ^^^ 2 ^ 63) % 2 ^ 52 = bits % 2 ^ 52
    rw [Nat.xor_mod_two_pow]
    norm_num
  have he : (bits ^^^ 9223372036854775808) / 4503599627370496 % 2048 = bits / 4503599627370496 % 2048 := by
    change (bits ^^^ 2 ^ 63) / 2 ^ 52 % 2 ^ 11 = bits / 2 ^ 52 % 2 ^ 11
    rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow]
    norm_num
  have hs : (bits ^^^ 9223372036854775808) / 9223372036854775808 % 2 = (bits / 9223372036854775808 % 2) ^^^ 1 := by
    change (bits ^^^ 2 ^ 63) / 2 ^ 63 % 2 ^ 1 = _
    rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow]
    norm_num
  have hz : bits / 9223372036854775808 % 2 = 0 ∨ bits / 9223372036854775808 % 2 = 1 := by omega
  simp only [floatOfBits, show fun_M 64 = 52 from rfl, show E 64 = 11 from rfl,
    floatBias, Nat.reduceSub, Nat.reducePow]
  rw [hm, he, hs]
  rcases hz with hz | hz <;> simp [hz, negative, magnitude, withSign]

theorem floatOfBits_copysign32 (a b : Nat) :
    floatOfBits 32 ((a &&& 2147483647) ||| (b &&& 2147483648)) =
      withSign (negative (floatOfBits 32 b)) (magnitude (floatOfBits 32 a)) := by
  have hm : ((a &&& 2147483647) ||| (b &&& 2147483648)) % 8388608 = a % 8388608 := by
    change ((a &&& 2147483647) ||| (b &&& 2147483648)) % 2 ^ 23 = _
    rw [Nat.or_mod_two_pow, Nat.and_mod_two_pow, Nat.and_mod_two_pow]
    norm_num
    change (a % 8388608 &&& (2 ^ 23 - 1)) = a % 8388608
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  have he : ((a &&& 2147483647) ||| (b &&& 2147483648)) / 8388608 % 256 = a / 8388608 % 256 := by
    change ((a &&& 2147483647) ||| (b &&& 2147483648)) / 2 ^ 23 % 2 ^ 8 = _
    rw [Nat.or_div_two_pow, Nat.and_div_two_pow, Nat.and_div_two_pow,
      Nat.or_mod_two_pow, Nat.and_mod_two_pow, Nat.and_mod_two_pow]
    norm_num
    change (a / 8388608 % 256 &&& (2 ^ 8 - 1)) = a / 8388608 % 256
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  have hs : ((a &&& 2147483647) ||| (b &&& 2147483648)) / 2147483648 % 2 = b / 2147483648 % 2 := by
    change ((a &&& 2147483647) ||| (b &&& 2147483648)) / 2 ^ 31 % 2 = _
    rw [Nat.or_div_two_pow, Nat.and_div_two_pow, Nat.and_div_two_pow]
    norm_num
  simp only [floatOfBits, show fun_M 32 = 23 from rfl, show E 32 = 8 from rfl,
    floatBias, Nat.reduceSub, Nat.reducePow]
  rw [hm, he, hs]
  split_ifs <;> simp_all [negative, magnitude, withSign]

theorem floatOfBits_copysign64 (a b : Nat) :
    floatOfBits 64 ((a &&& 9223372036854775807) ||| (b &&& 9223372036854775808)) =
      withSign (negative (floatOfBits 64 b)) (magnitude (floatOfBits 64 a)) := by
  have hm : ((a &&& 9223372036854775807) ||| (b &&& 9223372036854775808)) % 4503599627370496 = a % 4503599627370496 := by
    change ((a &&& 9223372036854775807) ||| (b &&& 9223372036854775808)) % 2 ^ 52 = _
    rw [Nat.or_mod_two_pow, Nat.and_mod_two_pow, Nat.and_mod_two_pow]
    norm_num
    change (a % 4503599627370496 &&& (2 ^ 52 - 1)) = a % 4503599627370496
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  have he : ((a &&& 9223372036854775807) ||| (b &&& 9223372036854775808)) / 4503599627370496 % 2048 = a / 4503599627370496 % 2048 := by
    change ((a &&& 9223372036854775807) ||| (b &&& 9223372036854775808)) / 2 ^ 52 % 2 ^ 11 = _
    rw [Nat.or_div_two_pow, Nat.and_div_two_pow, Nat.and_div_two_pow,
      Nat.or_mod_two_pow, Nat.and_mod_two_pow, Nat.and_mod_two_pow]
    norm_num
    change (a / 4503599627370496 % 2048 &&& (2 ^ 11 - 1)) = a / 4503599627370496 % 2048
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  have hs : ((a &&& 9223372036854775807) ||| (b &&& 9223372036854775808)) / 9223372036854775808 % 2 = b / 9223372036854775808 % 2 := by
    change ((a &&& 9223372036854775807) ||| (b &&& 9223372036854775808)) / 2 ^ 63 % 2 = _
    rw [Nat.or_div_two_pow, Nat.and_div_two_pow, Nat.and_div_two_pow]
    norm_num
  simp only [floatOfBits, show fun_M 64 = 52 from rfl, show E 64 = 11 from rfl,
    floatBias, Nat.reduceSub, Nat.reducePow]
  rw [hm, he, hs]
  split_ifs <;> simp_all [negative, magnitude, withSign]

end SpecExt.Builtins.Float

end

import SpecExt.Builtins.Float.Repr
import Mathlib.Tactic

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

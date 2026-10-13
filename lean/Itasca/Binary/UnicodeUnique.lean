import Itasca.Binary.Unicode

/-!
# Uniqueness of decoded names

Shows that `decodeChars` is injective on bytes accepted by `Utf8`, by re-encoding scalars
canonically (`Utf8.roundtrip`). `Utf8.nameOfBytes_injective` transports the validator's
duplicate-name check on raw bytes to equality of Unicode names.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- The shortest UTF-8 encoding of a scalar, as natural numbers. -/
def encodeChar : char → List Nat
  | .mk_char n =>
      if n < 128 then [n]
      else if n < 2048 then [192 + n / 64, 128 + n % 64]
      else if n < 65536 then [224 + n / 4096, 128 + n / 64 % 64, 128 + n % 64]
      else [240 + n / 262144, 128 + n / 4096 % 64, 128 + n / 64 % 64, 128 + n % 64]

private theorem encode_two (a b : Nat) (ha : 194 ≤ a) (ha' : a ≤ 223)
    (hb : 128 ≤ b) (hb' : b ≤ 191) :
    encodeChar (.mk_char (64 * (a - 192) + (b - 128))) = [a, b] := by
  have hlo : ¬64 * (a - 192) + (b - 128) < 128 := by omega
  have hhi : 64 * (a - 192) + (b - 128) < 2048 := by omega
  simp [encodeChar, hlo, hhi]
  omega

private theorem encode_three (a b c : Nat)
    (ha : (a = 224 ∧ 160 ≤ b ∧ b ≤ 191) ∨
      (225 ≤ a ∧ a ≤ 236 ∧ 128 ≤ b ∧ b ≤ 191) ∨
      (a = 237 ∧ 128 ≤ b ∧ b ≤ 159) ∨
      (238 ≤ a ∧ a ≤ 239 ∧ 128 ≤ b ∧ b ≤ 191))
    (hc : 128 ≤ c) (hc' : c ≤ 191) :
    encodeChar (.mk_char (4096 * (a - 224) + 64 * (b - 128) + (c - 128))) = [a, b, c] := by
  have hlo : ¬4096 * (a - 224) + 64 * (b - 128) + (c - 128) < 128 := by omega
  have hlo' : ¬4096 * (a - 224) + 64 * (b - 128) + (c - 128) < 2048 := by omega
  have hhi : 4096 * (a - 224) + 64 * (b - 128) + (c - 128) < 65536 := by omega
  simp [encodeChar, hlo, hlo', hhi]
  omega

private theorem encode_four (a b c d : Nat)
    (ha : (a = 240 ∧ 144 ≤ b ∧ b ≤ 191) ∨
      (241 ≤ a ∧ a ≤ 243 ∧ 128 ≤ b ∧ b ≤ 191) ∨
      (a = 244 ∧ 128 ≤ b ∧ b ≤ 143))
    (hc : 128 ≤ c) (hc' : c ≤ 191) (hd : 128 ≤ d) (hd' : d ≤ 191) :
    encodeChar (.mk_char (262144 * (a - 240) + 4096 * (b - 128) +
      64 * (c - 128) + (d - 128))) = [a, b, c, d] := by
  have hlo : ¬262144 * (a - 240) + 4096 * (b - 128) + 64 * (c - 128) + (d - 128) < 128 := by omega
  have hlo' : ¬262144 * (a - 240) + 4096 * (b - 128) + 64 * (c - 128) + (d - 128) < 2048 := by omega
  have hlo'' : ¬262144 * (a - 240) + 4096 * (b - 128) + 64 * (c - 128) + (d - 128) < 65536 := by omega
  simp [encodeChar, hlo, hlo', hlo'']
  omega

/-- Decoding a `Utf8Char` sequence and re-encoding the scalar recovers its bytes. -/
theorem Utf8Char.roundtrip {bytes} (h : Utf8Char bytes) (rest : List U8) :
    (decodeChars (bytes ++ rest)).flatMap encodeChar =
      bytes.map UScalar.val ++ (decodeChars rest).flatMap encodeChar := by
  cases h with
  | one a ha =>
      rcases rest with _ | ⟨x, (_ | ⟨y, (_ | ⟨z, tail⟩)⟩)⟩ <;>
        simp [decodeChars, show a.val < 128 by omega, encodeChar]
  | two a b ha ha' hb hb' =>
      have he := encode_two a.val b.val ha ha' hb hb'
      rcases rest with _ | ⟨x, (_ | ⟨y, tail⟩)⟩ <;>
        simp [decodeChars, show ¬a.val < 128 by omega, show a.val < 224 by omega, he]
  | three a b c ha hc hc' =>
      have he := encode_three a.val b.val c.val ha hc hc'
      rcases rest with _ | ⟨x, tail⟩ <;>
        simp [decodeChars, show ¬a.val < 128 by omega, show ¬a.val < 224 by omega,
          show a.val < 240 by omega, he]
  | four a b c d ha hc hc' hd hd' =>
      have he := encode_four a.val b.val c.val d.val ha hc hc' hd hd'
      simp [decodeChars, show ¬a.val < 128 by omega, show ¬a.val < 224 by omega,
        show ¬a.val < 240 by omega, he]

/-- Decoding accepted UTF-8 and re-encoding each scalar recovers the original bytes. -/
theorem Utf8.roundtrip {bytes} (h : Utf8 bytes) :
    (decodeChars bytes).flatMap encodeChar = bytes.map UScalar.val := by
  induction h with
  | nil => rfl
  | cons hc _ ih => rw [hc.roundtrip, ih, List.map_append]

/-- `decodeChars` is injective on accepted UTF-8. -/
theorem Utf8.decodeChars_injective {first rest} (h : Utf8 first) (h' : Utf8 rest)
    (heq : decodeChars first = decodeChars rest) : first = rest := by
  have hbytes : first.map UScalar.val = rest.map UScalar.val := by
    rw [← h.roundtrip, heq, h'.roundtrip]
  clear h h' heq
  induction first generalizing rest with
  | nil => cases rest <;> simp_all
  | cons a first ih =>
      cases rest with
      | nil => simp at hbytes
      | cons b rest =>
          obtain ⟨ha, ht⟩ := List.cons.inj hbytes
          rw [UScalar.eq_of_val_eq ha, ih ht]

/-- For names the binary grammar accepts, equal Unicode names have equal bytes. -/
theorem Utf8.nameOfBytes_injective {first rest} (h : Utf8 first) (h' : Utf8 rest)
    (heq : nameOfBytes first = nameOfBytes rest) : first = rest := by
  exact h.decodeChars_injective h' («name».mk_name.inj heq)

end Itasca.ModuleBinary

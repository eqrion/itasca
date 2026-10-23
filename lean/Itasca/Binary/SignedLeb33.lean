import Itasca.Binary.SignedLeb

/-!
# Signed 33-bit LEB128

Instantiates `SignedLeb` for the extracted `reader.read_s33_leb`: `SignedLeb33.format` has
range [-2^32, 2^32 - 1] and at most 5 bytes. The `reader.read_s33_leb` lemmas
(`spec`, `total`, `sound`, `complete`, `rejected`, `success_span`) state that it is total,
returns exactly the `SignedLeb33.Decoded` spans and rejects the `SignedLeb33.Rejected` inputs.
-/

open Aeneas Aeneas.Std

namespace Itasca.SignedLeb33

/-- The signed 33-bit specialization of the shared decoder proof. -/
def format : SignedLeb.Format := ⟨4#u32, (-4294967296)#i128, 4294967295#i128, by decide⟩

/-- Signed 33-bit LEB128 bytes, permitting nonminimal sign extension. -/
abbrev Encoding := SignedLeb.Encoding format

/-- The consumed encoding and untouched input suffix determine a successful read. -/
abbrev Decoded := SignedLeb.Decoded format

/-- Malformed or truncated input for the signed 33-bit reader. -/
abbrev Rejected := SignedLeb.Rejected format

/-- The result of the signed 33-bit reader. -/
abbrev Post := SignedLeb.Post format

/-- The shared `I128` loop specialized to this format. -/
theorem spec128 (data : Slice U8) (start : Usize) :
    reader.read_sn_leb data start 4#u32 (-4294967296)#i128 4294967295#i128 ⦃ Post data start ⦄ :=
  SignedLeb.spec128 format data start

/-- A successful decoding consumes between one and 5 bytes within the input. -/
theorem Decoded.span (data : Slice U8) (start : Usize) (value : Int) (next : Usize)
    (h : Decoded data start value next) :
    start.val < next.val ∧ next.val ≤ start.val + 5 ∧ next.val ≤ data.length :=
  SignedLeb.Decoded.span format data start value next h

/-- A decoded value lies within the signed 33-bit range. -/
theorem Decoded.range (data : Slice U8) (start : Usize) (value : Int) (next : Usize)
    (h : Decoded data start value next) : -4294967296 ≤ value ∧ value ≤ 4294967295 :=
  SignedLeb.Decoded.range format data start value next h

/-- Two encodings that are prefixes of the same byte string are equal and have equal values. -/
theorem Encoding.prefix_unique {xs ys : List U8} {x y : Int} {leftTail rightTail : List U8}
    (hx : Encoding xs x) (hy : Encoding ys y) (he : xs ++ leftTail = ys ++ rightTail) :
    xs = ys ∧ x = y :=
  SignedLeb.Encoding.prefix_unique format hx hy he

/-- Byte descriptions determine both the value and the ending cursor. -/
theorem Decoded.deterministic (data : Slice U8) (start : Usize)
    (v₁ v₂ : Int) (q₁ q₂ : Usize)
    (h₁ : Decoded data start v₁ q₁) (h₂ : Decoded data start v₂ q₂) :
    v₁ = v₂ ∧ q₁ = q₂ :=
  SignedLeb.Decoded.deterministic format data start v₁ v₂ q₁ q₂ h₁ h₂

private theorem decoded_not_rejected (data : Slice U8) (start : Usize)
    (value : Int) (next : Usize) (e : error.OpError)
    (hd : Decoded data start value next) (hr : Rejected data start e) : False :=
  SignedLeb.decoded_not_rejected format data start value next e hd hr

end Itasca.SignedLeb33

namespace Itasca

/-- Signed 33-bit decoding into `I64` is total, preserves the signed value during the I128-to-I64
cast, and reports exact consumed bytes or a malformed-input description. -/
@[step]
theorem reader.read_s33_leb.spec (data : Slice U8) (start : Usize) :
    reader.read_s33_leb data start ⦃ SignedLeb33.Post data start ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (SignedLeb33.spec128 data start)
  simp only [reader.read_s33_leb, hr, bind_ok]
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, SignedLeb.Post]
    exact hp
  | Ok r =>
    rcases r with ⟨v, p⟩
    have hb := SignedLeb33.Decoded.range data start v.val p hp
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with IScalar.cast_inBounds_spec .I64 v (by scalar_tac) as ⟨x, hx⟩
    simpa [SignedLeb.Post, hx] using hp

end Itasca

namespace Itasca

/-- Every signed 33-bit byte encoding is accepted, including nonminimal sign extension. -/
theorem reader.read_s33_leb.complete (data : Slice U8) (start : Usize)
    (value : I64) (next : Usize) (h : SignedLeb33.Decoded data start value.val next) :
    reader.read_s33_leb data start = .ok (.Ok (value, next)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_s33_leb.spec data start)
  cases r with
  | Ok r =>
    obtain ⟨v, q⟩ := r
    obtain ⟨hv, rfl⟩ := SignedLeb33.Decoded.deterministic data start v.val value.val q next hp h
    have heq : v = value := IScalar.eq_of_val_eq hv
    simpa [heq] using hr
  | Err e => exact False.elim (SignedLeb33.decoded_not_rejected data start value.val next e h hp)

end Itasca

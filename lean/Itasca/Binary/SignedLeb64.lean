import Itasca.Binary.SignedLeb

open Aeneas Aeneas.Std

namespace Itasca.SignedLeb64

/-- The signed 64-bit specialization of the shared decoder proof. -/
def format : SignedLeb.Format := ⟨9#u32, (-9223372036854775808)#i128, 9223372036854775807#i128, by decide⟩

/-- Signed 64-bit LEB128 bytes, permitting nonminimal sign extension. -/
abbrev Encoding := SignedLeb.Encoding format

/-- The consumed encoding and untouched input suffix determine a successful read. -/
abbrev Decoded := SignedLeb.Decoded format

abbrev Rejected := SignedLeb.Rejected format

abbrev Post := SignedLeb.Post format

theorem spec128 (data : Slice U8) (start : Usize) :
    reader.read_sn_leb data start 9#u32 (-9223372036854775808)#i128 9223372036854775807#i128 ⦃ Post data start ⦄ :=
  SignedLeb.spec128 format data start

theorem Decoded.span (data : Slice U8) (start : Usize) (value : Int) (next : Usize)
    (h : Decoded data start value next) :
    start.val < next.val ∧ next.val ≤ start.val + 10 ∧ next.val ≤ data.length :=
  SignedLeb.Decoded.span format data start value next h

theorem Decoded.range (data : Slice U8) (start : Usize) (value : Int) (next : Usize)
    (h : Decoded data start value next) : -9223372036854775808 ≤ value ∧ value ≤ 9223372036854775807 :=
  SignedLeb.Decoded.range format data start value next h

theorem Rejected.kind {data : Slice U8} {start : Usize} {e : error.OpError}
    (h : Rejected data start e) : e = .UnexpectedEof ∨ e = .LebTooLong :=
  SignedLeb.Rejected.kind format h

theorem Encoding.prefix_unique {xs ys : List U8} {x y : Int} {leftTail rightTail : List U8}
    (hx : Encoding xs x) (hy : Encoding ys y) (he : xs ++ leftTail = ys ++ rightTail) :
    xs = ys ∧ x = y :=
  SignedLeb.Encoding.prefix_unique format hx hy he

theorem Decoded.deterministic (data : Slice U8) (start : Usize)
    (v₁ v₂ : Int) (q₁ q₂ : Usize)
    (h₁ : Decoded data start v₁ q₁) (h₂ : Decoded data start v₂ q₂) :
    v₁ = v₂ ∧ q₁ = q₂ :=
  SignedLeb.Decoded.deterministic format data start v₁ v₂ q₁ q₂ h₁ h₂

private theorem decoded_not_rejected (data : Slice U8) (start : Usize)
    (value : Int) (next : Usize) (e : error.OpError)
    (hd : Decoded data start value next) (hr : Rejected data start e) : False :=
  SignedLeb.decoded_not_rejected format data start value next e hd hr

end Itasca.SignedLeb64

namespace Itasca

/-- Signed I64 decoding is total, preserves the signed value during the I128-to-I64
cast, and reports exact consumed bytes or a malformed-input description. -/
@[step]
theorem reader.read_s64_leb.spec (data : Slice U8) (start : Usize) :
    reader.read_s64_leb data start ⦃ SignedLeb64.Post data start ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (SignedLeb64.spec128 data start)
  simp only [reader.read_s64_leb, hr, bind_ok]
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, SignedLeb.Post]
    exact hp
  | Ok r =>
    rcases r with ⟨v, p⟩
    have hb := SignedLeb64.Decoded.range data start v.val p hp
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with IScalar.cast_inBounds_spec .I64 v (by scalar_tac) as ⟨x, hx⟩
    simpa [SignedLeb.Post, hx] using hp

theorem reader.read_s64_leb.total (data : Slice U8) (start : Usize) :
    ∃ r, reader.read_s64_leb data start = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (reader.read_s64_leb.spec data start)
  exact ⟨r, hr⟩

theorem reader.read_s64_leb.sound (data : Slice U8) (start : Usize)
    (value : I64) (next : Usize)
    (h : reader.read_s64_leb data start = .ok (.Ok (value, next))) :
    SignedLeb64.Decoded data start value.val next := by
  have hs := reader.read_s64_leb.spec data start
  simpa [h, SignedLeb.Post] using hs

theorem reader.read_s64_leb.success_span (data : Slice U8) (start : Usize)
    (value : I64) (next : Usize)
    (h : reader.read_s64_leb data start = .ok (.Ok (value, next))) :
    start.val < next.val ∧ next.val ≤ start.val + 10 ∧ next.val ≤ data.length :=
  SignedLeb64.Decoded.span data start value.val next (reader.read_s64_leb.sound data start value next h)

theorem reader.read_s64_leb.rejected (data : Slice U8) (start : Usize)
    (e : error.OpError) (h : reader.read_s64_leb data start = .ok (.Err e)) :
    SignedLeb64.Rejected data start e := by
  have hs := reader.read_s64_leb.spec data start
  simpa [h, SignedLeb.Post] using hs

end Itasca

namespace Itasca

/-- Every signed I64 byte encoding is accepted, including nonminimal sign extension. -/
theorem reader.read_s64_leb.complete (data : Slice U8) (start : Usize)
    (value : I64) (next : Usize) (h : SignedLeb64.Decoded data start value.val next) :
    reader.read_s64_leb data start = .ok (.Ok (value, next)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_s64_leb.spec data start)
  cases r with
  | Ok r =>
    obtain ⟨v, q⟩ := r
    obtain ⟨hv, rfl⟩ := SignedLeb64.Decoded.deterministic data start v.val value.val q next hp h
    have heq : v = value := IScalar.eq_of_val_eq hv
    simpa [heq] using hr
  | Err e => exact False.elim (SignedLeb64.decoded_not_rejected data start value.val next e h hp)

end Itasca

import Itasca.Binary.SignedLebGeneric

open Aeneas Aeneas.Std

namespace Itasca.SignedLeb33

/-- The signed 33-bit specialization of the shared decoder proof. -/
def format : SignedLebGeneric.Format := ⟨4#u32, (-4294967296)#i128, 4294967295#i128, by decide⟩

def finalValue (acc mult : Int) (last : U8) : Int :=
  acc + (last.val : Int) * mult - if 64 ≤ last.val then 128 * mult else 0

/-- Signed 33-bit LEB128 bytes, permitting nonminimal sign extension. -/
def Encoding (bytes : List U8) (value : Int) : Prop :=
  ∃ before last, bytes = before ++ [last] ∧ before.length ≤ 4 ∧
    (∀ b ∈ before, 128 ≤ b.val) ∧ last.val < 128 ∧
    value = finalValue (Leb128.payload before) (128 ^ before.length) last ∧
    -4294967296 ≤ value ∧ value ≤ 4294967295

/-- The consumed encoding and untouched input suffix determine a successful read. -/
def Decoded (data : Slice U8) (start : Usize) (value : Int) (next : Usize) : Prop :=
  ∃ bytes, data.val.drop start.val = bytes ++ data.val.drop next.val ∧
    next.val = start.val + bytes.length ∧ next.val ≤ data.length ∧ Encoding bytes value

abbrev Rejected := SignedLebGeneric.Rejected format

def Post (data : Slice U8) (start : Usize) {ty : IScalarTy} :
    core.result.Result (IScalar ty × Usize) error.OpError → Prop
  | .Ok (value, next) => Decoded data start value.val next
  | .Err e => Rejected data start e

theorem spec128 (data : Slice U8) (start : Usize) :
    reader.read_sn_leb data start 4#u32 (-4294967296)#i128 4294967295#i128 ⦃ Post data start ⦄ :=
  SignedLebGeneric.spec128 format data start

theorem Decoded.span (data : Slice U8) (start : Usize) (value : Int) (next : Usize)
    (h : Decoded data start value next) :
    start.val < next.val ∧ next.val ≤ start.val + 5 ∧ next.val ≤ data.length :=
  SignedLebGeneric.Decoded.span format data start value next h

theorem Decoded.range (data : Slice U8) (start : Usize) (value : Int) (next : Usize)
    (h : Decoded data start value next) : -4294967296 ≤ value ∧ value ≤ 4294967295 :=
  SignedLebGeneric.Decoded.range format data start value next h

theorem Rejected.kind {data : Slice U8} {start : Usize} {e : error.OpError}
    (h : Rejected data start e) : e = .UnexpectedEof ∨ e = .LebTooLong :=
  SignedLebGeneric.Rejected.kind format h

theorem Encoding.prefix_unique {xs ys : List U8} {x y : Int} {leftTail rightTail : List U8}
    (hx : Encoding xs x) (hy : Encoding ys y) (he : xs ++ leftTail = ys ++ rightTail) :
    xs = ys ∧ x = y :=
  SignedLebGeneric.Encoding.prefix_unique format hx hy he

theorem Decoded.deterministic (data : Slice U8) (start : Usize)
    (v₁ v₂ : Int) (q₁ q₂ : Usize)
    (h₁ : Decoded data start v₁ q₁) (h₂ : Decoded data start v₂ q₂) :
    v₁ = v₂ ∧ q₁ = q₂ :=
  SignedLebGeneric.Decoded.deterministic format data start v₁ v₂ q₁ q₂ h₁ h₂

private theorem decoded_not_rejected (data : Slice U8) (start : Usize)
    (value : Int) (next : Usize) (e : error.OpError)
    (hd : Decoded data start value next) (hr : Rejected data start e) : False :=
  SignedLebGeneric.decoded_not_rejected format data start value next e hd hr

end Itasca.SignedLeb33

namespace Itasca

/-- Signed I64 decoding is total, preserves the signed value during the I128-to-I64
cast, and reports exact consumed bytes or a malformed-input description. -/
@[step]
theorem reader.read_s33_leb.spec (data : Slice U8) (start : Usize) :
    reader.read_s33_leb data start ⦃ SignedLeb33.Post data start ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (SignedLeb33.spec128 data start)
  simp only [reader.read_s33_leb, hr, bind_ok]
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, SignedLeb33.Post]
    exact hp
  | Ok r =>
    rcases r with ⟨v, p⟩
    have hb := SignedLeb33.Decoded.range data start v.val p hp
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with IScalar.cast_inBounds_spec .I64 v (by scalar_tac)
    simpa [SignedLeb33.Post, *] using hp

theorem reader.read_s33_leb.total (data : Slice U8) (start : Usize) :
    ∃ r, reader.read_s33_leb data start = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (reader.read_s33_leb.spec data start)
  exact ⟨r, hr⟩

theorem reader.read_s33_leb.sound (data : Slice U8) (start : Usize)
    (value : I64) (next : Usize)
    (h : reader.read_s33_leb data start = .ok (.Ok (value, next))) :
    SignedLeb33.Decoded data start value.val next := by
  have hs := reader.read_s33_leb.spec data start
  simpa [h, SignedLeb33.Post] using hs

theorem reader.read_s33_leb.success_span (data : Slice U8) (start : Usize)
    (value : I64) (next : Usize)
    (h : reader.read_s33_leb data start = .ok (.Ok (value, next))) :
    start.val < next.val ∧ next.val ≤ start.val + 5 ∧ next.val ≤ data.length :=
  SignedLeb33.Decoded.span data start value.val next (reader.read_s33_leb.sound data start value next h)

theorem reader.read_s33_leb.rejected (data : Slice U8) (start : Usize)
    (e : error.OpError) (h : reader.read_s33_leb data start = .ok (.Err e)) :
    SignedLeb33.Rejected data start e := by
  have hs := reader.read_s33_leb.spec data start
  simpa [h, SignedLeb33.Post] using hs

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

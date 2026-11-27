import WebAssembly.Binary.LebUnique
import Itasca.Binary.Definitions
import Itasca.Results.Definitions.Binary
import Itasca.Support.Translation

/-!
Proofs for Binary.

This module collects Leb128, SignedLeb, LebReaders.
Each section documents its contracts and consumers.
-/

/-! ## Leb128 -/

section

/-! ## ReadByte -/

section

/-!
# Single-byte reads

Specifications of the extracted `reader.read_byte` and of `code.read_op`, which reads one
opcode byte. Both return the byte at the cursor and advance it by one, or return
`UnexpectedEof` at the end of the input. These are the base case for the LEB128 and
instruction-level reader lemmas.
-/

open Aeneas Aeneas.Std Aeneas.Std.WP

namespace Itasca

/-- Reading within a slice returns its byte and advances the cursor exactly once. -/
@[step]
theorem reader.read_byte.spec (data : Slice U8) (pos : Usize)
    (h : pos.val < data.length) :
    reader.read_byte data pos ⦃ (r : core.result.Result (U8 × Usize) error.OpError) =>
      ∃ next, r = .Ok (data.val[pos.val], next) ∧ next.val = pos.val + 1 ⦄ := by
  unfold reader.read_byte
  step*
  exact ⟨i1, by rw [b_post], i1_post⟩

/-- Reading at or past the end of the slice returns the `UnexpectedEof` validation error. -/
theorem reader.read_byte.eof (data : Slice U8) (pos : Usize)
    (h : data.length ≤ pos.val) :
    reader.read_byte data pos = .ok (.Err .UnexpectedEof) := by
  unfold reader.read_byte
  have hb : pos ≥ Slice.len data := by scalar_tac
  simp only [hb, ↓reduceIte]

end Itasca

end

/-! ## Leb128 -/

section

/-!
# Unsigned 32-bit LEB128

Relates the extracted unsigned 32-bit LEB reader to the public `Binary.Leb128.Encoding`
and `Binary.Leb128.Decoded` predicates, with rejection and loop invariants defined here.
The `spec`, `total`, `complete` and `reject_complete` contracts retain normal return
and exact byte behavior.
`Binary.Leb128.Encoding.prefix_unique` shows that an encoding is determined by its leading bytes.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary.Leb128

/-- The accumulated payload occupies exactly the places below `mult`. -/
private def Invariant (acc mult i : U32) : Prop :=
  i.val ≤ 4 ∧ mult.val = 128 ^ i.val ∧ acc.val < mult.val

private def BytePost (acc mult i : U32) (p : Usize) (b : U8) :
    ControlFlow (U32 × U32 × Usize × U32)
      (core.result.Result (U32 × Usize) error.OpError) → Prop
  | .done (.Err e) => e = .LebTooLong ∧ i.val = 4 ∧ 16 ≤ b.val
  | .done (.Ok (v, q)) => q.val = p.val + 1 ∧
      v.val = acc.val + (b.val % 128) * mult.val ∧ b.val < 128 ∧
      (i.val = 4 → b.val < 16)
  | .cont (a, m, q, j) => Invariant a m j ∧ j.val = i.val + 1 ∧
      q.val = p.val + 1 ∧ a.val = acc.val + (b.val % 128) * mult.val ∧
      128 ≤ b.val

private theorem byte_spec (data : Slice U8) (p : Usize) (acc mult i : U32)
    (hp : p.val < data.length) (hinv : Invariant acc mult i) :
    reader.read_u32_leb_loop.body data acc mult p i ⦃
      BytePost acc mult i p data.val[p.val] ⦄ := by
  rcases hinv with ⟨hi, hm, ha⟩
  unfold reader.read_u32_leb_loop.body
  have h0 : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
  rcases h0 with hi | hi | hi | hi | hi <;>
    simp only [hi] at hm <;> norm_num at hm <;>
    step* <;> simp_all [BytePost, Invariant] <;> scalar_tac

end Itasca.Binary.Leb128

namespace Itasca.Binary.Leb128

private theorem payload_append (xs ys : List U8) :
    payload (xs ++ ys) = payload xs + 128 ^ xs.length * payload ys := by
  induction xs with
  | nil => simp [payload_nil, payload_cons]
  | cons b xs ih => simp [payload_nil, payload_cons, ih, pow_succ]; ring

/-- Rejections describe malformed or truncated bytes rather than runtime failures. -/
inductive Rejected (data : Slice U8) (start : Usize) : error.OpError → Prop where
  | eof (before : List U8)
      (bytes : data.val.drop start.val = before)
      (length : before.length ≤ 4)
      (continuations : ∀ b ∈ before, 128 ≤ b.val) :
      Rejected data start .UnexpectedEof
  | overlong (before : List U8) (last : U8) (after : List U8)
      (bytes : data.val.drop start.val = before ++ last :: after)
      (length : before.length = 4)
      (continuations : ∀ b ∈ before, 128 ≤ b.val)
      (last_invalid : 16 ≤ last.val) :
      Rejected data start .LebTooLong

/-- The result of `reader.read_u32_leb`: a `Decoded` span on success and a `Rejected` description
on failure. -/
def Post (data : Slice U8) (start : Usize) :
    core.result.Result (U32 × Usize) error.OpError → Prop
  | .Ok (value, next) => Decoded data start value next
  | .Err e => Rejected data start e

private def LoopInvariant (data : Slice U8) (start : Usize)
    (s : U32 × U32 × Usize × U32) : Prop :=
  Invariant s.1 s.2.1 s.2.2.2 ∧ s.2.2.1.val = start.val + s.2.2.2.val ∧
  ∃ before : List U8, before.length = s.2.2.2.val ∧
    data.val.drop start.val = before ++ data.val.drop s.2.2.1.val ∧
    s.1.val = payload before ∧ (∀ b ∈ before, 128 ≤ b.val)

/-- The decoder always terminates without a modeled panic. On success it reads
exactly an unsigned LEB128 encoding; rejection is EOF or an overlong encoding. -/
theorem spec (data : Slice U8) (start : Usize) :
    reader.read_u32_leb data start ⦃ Post data start ⦄ := by
  unfold reader.read_u32_leb reader.read_u32_leb_loop
  apply loop.spec_decr_nat (fun s => 5 - s.2.2.2.val) (LoopInvariant data start)
  · rintro ⟨acc, mult, p, i⟩ ⟨hinv, hpos, before, hlen, hbytes, hacc, hmore⟩
    dsimp only at *
    by_cases hp : p.val < data.length
    · apply WP.spec_mono (byte_spec data p acc mult i hp hinv)
      intro r hr
      have hdrop := List.drop_eq_getElem_cons hp
      cases r with
      | done r =>
        cases r with
        | Err e =>
          rcases hr with ⟨rfl, hi, hb⟩
          apply Rejected.overlong before data.val[p.val] (data.val.drop (p.val + 1))
          · rw [hbytes, hdrop]
          · omega
          · exact hmore
          · exact hb
        | Ok r =>
          rcases r with ⟨value, next⟩
          rcases hr with ⟨hq, hv, hb, hlast⟩
          refine ⟨before ++ [data.val[p.val]], ?_, ?_, by omega, ?_⟩
          · rw [hbytes, hdrop, hq]
            simp
          · simp [hpos, hlen, hq, Nat.add_assoc]
          · refine ⟨before, data.val[p.val], rfl, ?_, hmore, hb, ?_, ?_⟩
            · simpa [hlen] using hinv.1
            · simpa [hlen] using hlast
            · rw [payload_append, hlen, ← hinv.2.1, payload, payload]
              simp only [mul_zero, add_zero]
              rw [hv, hacc]
              ring
      | cont s =>
        rcases s with ⟨a, m, q, j⟩
        rcases hr with ⟨hnew, hj, hq, ha, hb⟩
        dsimp only [LoopInvariant]
        refine ⟨⟨hnew, by omega, before ++ [data.val[p.val]], ?_, ?_, ?_, ?_⟩, ?_⟩
        · simp [hlen, hj]
        · rw [hbytes, hdrop, hq]
          simp
        · rw [payload_append, hlen, ← hinv.2.1, payload, payload]
          simp only [mul_zero, add_zero]
          rw [ha, hacc]
          ring
        · intro b hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact hmore b hmem
          · simpa using (List.mem_singleton.mp hmem) ▸ hb
        · have := hnew.1
          omega
    · have hp' : p ≥ Slice.len data := by scalar_tac
      simp only [reader.read_u32_leb_loop.body, hp', ↓reduceIte, WP.spec_ok]
      apply Rejected.eof before
      · simpa [List.drop_eq_nil_of_le (by scalar_tac : data.val.length ≤ p.val)] using hbytes
      · simpa [hlen] using hinv.1
      · exact hmore
  · dsimp only [LoopInvariant, Invariant]
    exact ⟨⟨by decide, rfl, by decide⟩, by simp, [], by simp, by simp, rfl, by simp⟩

end Itasca.Binary.Leb128

namespace Itasca.Binary.Leb128

theorem Encoding.prefix_unique {xs ys : List U8} {x y : Nat} {leftTail bs : List U8}
    (hx : Encoding xs x) (hy : Encoding ys y) (heq : xs ++ leftTail = ys ++ bs) :
    xs = ys ∧ x = y :=
  WebAssembly.Binary.Leb128.UnsignedForm.prefix_unique hx hy heq

private theorem decoded_not_rejected (data : Slice U8) (start : Usize)
    (value : U32) (next : Usize) (e : error.OpError)
    (hd : Decoded data start value next) (hr : Rejected data start e) : False := by
  rcases hd with ⟨bytes, hbytes, hpos, hbound, before, last, rfl,
    hlen, hmore, hlast, hfifth, hvalue⟩
  simp only [List.append_assoc, List.singleton_append] at hbytes
  cases hr with
  | eof bs hbs hbslen hbscont =>
    have hmem : last ∈ bs := by rw [← hbs, hbytes]; simp
    have := hbscont last hmem
    omega
  | overlong bs b after hbs hbslen hbscont hb =>
    have heq : before ++ last :: data.val.drop next.val = bs ++ b :: after := hbytes.symm.trans hbs
    have hle := WebAssembly.Binary.Leb128.continuation_prefix_le UScalar.val before bs last (data.val.drop next.val)
      (b :: after) hmore hbscont hlast heq
    have hlen' : before.length = 4 := by omega
    have hfirst : before = bs := by
      have := congrArg (List.take before.length) heq
      simpa [List.take_append, hlen', hbslen] using this
    subst bs
    have hlb : last = b := (List.cons.inj (List.append_cancel_left heq)).1
    subst b
    have := hfifth hlen'
    omega

/-- The byte description fixes both the decoded value and the ending cursor. -/
theorem Decoded.deterministic (data : Slice U8) (start : Usize)
    (v₁ v₂ : U32) (q₁ q₂ : Usize)
    (h₁ : Decoded data start v₁ q₁) (h₂ : Decoded data start v₂ q₂) :
    v₁ = v₂ ∧ q₁ = q₂ := by
  rcases h₁ with ⟨bs₁, heq₁, hq₁, _, henc₁⟩
  rcases h₂ with ⟨bs₂, heq₂, hq₂, _, henc₂⟩
  obtain ⟨hbs, hv⟩ := Encoding.prefix_unique henc₁ henc₂ (heq₁.symm.trans heq₂)
  constructor
  · exact UScalar.eq_of_val_eq hv
  · apply UScalar.eq_of_val_eq
    rw [hbs] at hq₁
    exact hq₁.trans hq₂.symm

/-- A successful decoding consumes between one and five bytes within the input. -/
theorem Decoded.span (data : Slice U8) (start : Usize) (value : U32) (next : Usize)
    (h : Decoded data start value next) :
    start.val < next.val ∧ next.val ≤ start.val + 5 ∧ next.val ≤ data.length := by
  rcases h with ⟨bs, _, hq, hbound, before, last, rfl, hlen, _⟩
  simp only [List.length_append, List.length_singleton] at hq
  omega

end Itasca.Binary.Leb128

namespace Itasca

/-- Total unsigned LEB128 decoding, including malformed input and exact byte spans. -/
@[step]
theorem reader.read_u32_leb.spec (data : Slice U8) (start : Usize) :
    reader.read_u32_leb data start ⦃ Binary.Leb128.Post data start ⦄ := Binary.Leb128.spec data start

/-- `reader.read_u32_leb` never panics. -/
theorem reader.read_u32_leb.total (data : Slice U8) (start : Usize) :
    ∃ r, reader.read_u32_leb data start = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  exact ⟨r, hr⟩

/-- Every encoding described by `Decoded` is accepted, including non-minimal encodings. -/
theorem reader.read_u32_leb.complete (data : Slice U8) (start : Usize)
    (value : U32) (next : Usize) (h : Binary.Leb128.Decoded data start value next) :
    reader.read_u32_leb data start = .ok (.Ok (value, next)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Ok r =>
    obtain ⟨v, q⟩ := r
    obtain ⟨rfl, rfl⟩ := Binary.Leb128.Decoded.deterministic data start v value q next hp h
    exact hr
  | Err e => exact False.elim (Binary.Leb128.decoded_not_rejected data start value next e h hp)

end Itasca

namespace Itasca.Binary.Leb128

private theorem payload_lt (bs : List U8) : payload bs < 128 ^ bs.length := by
  induction bs with
  | nil => simp [payload_nil, payload_cons]
  | cons b bs ih =>
    have hm : b.val % 128 < 128 := Nat.mod_lt _ (by decide)
    simp only [payload_nil, payload_cons, List.length_cons, pow_succ]
    omega

/-- The byte-level relation itself enforces the U32 range. -/
theorem Encoding.value_lt {bytes : List U8} {value : Nat} (h : Encoding bytes value) :
    value < 2 ^ 32 := by
  rcases h with ⟨before, last, rfl, hlen, _, hlast, hfifth, rfl⟩
  rw [payload_append]
  simp only [payload_nil, payload_cons, mul_zero, add_zero, Nat.mod_eq_of_lt hlast]
  have hp := payload_lt before
  have hcases : before.length = 0 ∨ before.length = 1 ∨ before.length = 2 ∨
      before.length = 3 ∨ before.length = 4 := by omega
  rcases hcases with h | h | h | h | h <;>
    simp only [h] at hp hfifth ⊢ <;> norm_num at hp hfifth ⊢ <;> omega

private theorem rejected_unique {data : Slice U8} {start : Usize} {e₁ e₂ : error.OpError}
    (h₁ : Rejected data start e₁) (h₂ : Rejected data start e₂) : e₁ = e₂ := by
  cases h₁ <;> cases h₂
  · rfl
  · rename_i before hbytes hlen _ bs b after hbytes' hlen' _ _
    have := congrArg List.length (hbytes.symm.trans hbytes')
    simp only [List.length_append, List.length_cons] at this
    omega
  · rename_i before last after hbytes hlen _ _ bs hbytes' hlen' _
    have := congrArg List.length (hbytes.symm.trans hbytes')
    simp only [List.length_append, List.length_cons] at this
    omega
  · rfl

end Itasca.Binary.Leb128

namespace Itasca

/-- Every `Binary.Leb128.Rejected` description is the result of `reader.read_u32_leb`. -/
theorem reader.read_u32_leb.reject_complete (data : Slice U8) (start : Usize)
    (e : error.OpError) (h : Binary.Leb128.Rejected data start e) :
    reader.read_u32_leb data start = .ok (.Err e) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Ok r => exact False.elim (Binary.Leb128.decoded_not_rejected data start r.1 r.2 e hp h)
  | Err e' =>
    have heq := Binary.Leb128.rejected_unique hp h
    simpa [heq] using hr

end Itasca

end

end

/-! ## SignedLeb -/

section

/-!
# Shared signed LEB reader proofs

The parameterized signed decoder supplies interval, range, rejection and prefix-uniqueness
facts. Its signed 33-bit specialization handles block signatures; the 32-bit and 64-bit
readers use the same foundation.
-/

/-! ## SignedLeb -/

section

/-!
# Signed LEB128, shared decoder

Describes signed LEB128 byte strings parameterized by a `Binary.SignedLeb.Format` (maximum length and
value range) and proves that the extracted `reader.read_sn_leb` loop, which computes in `I128`,
is total and agrees with the description (`Binary.SignedLeb.spec128`). The 32-, 33- and 64-bit readers
in `Binary/ScalarReaders`, `Binary/Binary.SignedLeb` and `Binary/Binary.SignedLeb64` instantiate it.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary.SignedLeb

variable (format : Format)

private def Invariant (acc mult : I128) (i : U32) : Prop :=
  i.val ≤ format.last.val ∧ mult.val = 128 ^ i.val ∧ 0 ≤ acc.val ∧ acc.val < mult.val

private def BytePost (acc mult : I128) (i : U32) (p : Usize) (b : U8) :
    ControlFlow (I128 × I128 × Usize × U32)
      (core.result.Result (I128 × Usize) error.OpError) → Prop
  | .done (.Err e) => e = .LebTooLong ∧
      ((128 ≤ b.val ∧ i.val = format.last.val) ∨
        (b.val < 128 ∧ (finalValue acc.val mult.val b < format.lower.val ∨
          format.upper.val < finalValue acc.val mult.val b)))
  | .done (.Ok (v, q)) => q.val = p.val + 1 ∧
      v.val = finalValue acc.val mult.val b ∧ b.val < 128 ∧
      format.lower.val ≤ v.val ∧ v.val ≤ format.upper.val
  | .cont (a, m, q, j) => Invariant format a m j ∧ j.val = i.val + 1 ∧
      q.val = p.val + 1 ∧ a.val = acc.val + (b.val % 128 : Nat) * mult.val ∧
      128 ≤ b.val

@[step] private theorem byte_cast_spec (b : U8) :
    lift (UScalar.hcast .I128 b) ⦃ r => r.val = (b.val : Int) ⦄ :=
  UScalar.hcast_inBounds_spec .I128 b (by scalar_tac)

-- Bound the shared arithmetic once instead of replaying the reader for ten positions.
set_option maxHeartbeats 600000 in
private theorem byte_spec (data : Slice U8) (p : Usize) (acc mult : I128) (i : U32)
    (hp : p.val < data.length) (hinv : Invariant format acc mult i) :
    reader.read_sn_leb_loop.body data format.last format.lower format.upper
      acc mult p i ⦃ BytePost format acc mult i p data.val[p.val] ⦄ := by
  rcases hinv with ⟨hi, hm, ha0, ha⟩
  unfold reader.read_sn_leb_loop.body
  have hmax : i.val ≤ 9 := hi.trans format.last_le
  have multPositive : 0 < mult.val := by rw [hm]; positivity
  have multBound : mult.val ≤ 128 ^ 9 := by
    rw [hm]
    exact pow_le_pow_right₀ (by norm_num : (1 : Int) ≤ 128) hmax
  norm_num at multBound
  have payloadNonnegative : 0 ≤ (data.val[p.val].val : Int) % 128 :=
    Int.emod_nonneg _ (by decide)
  have payloadBound : (data.val[p.val].val : Int) % 128 ≤ 127 := by
    have bound := Int.emod_lt_of_pos (data.val[p.val].val : Int) (by decide : (0 : Int) < 128)
    omega
  have productNonnegative : 0 ≤ ((data.val[p.val].val : Int) % 128) * mult.val :=
    mul_nonneg payloadNonnegative multPositive.le
  have productBound : ((data.val[p.val].val : Int) % 128) * mult.val ≤ 127 * mult.val :=
    mul_le_mul_of_nonneg_right payloadBound multPositive.le
  have terminatingPayload (h : data.val[p.val].val < 128) :
      (data.val[p.val].val : Int) % 128 = data.val[p.val].val := by
    apply Int.emod_eq_of_lt <;> omega
  step* <;> try (simp only [BytePost, Invariant, finalValue] at *; scalar_tac)
  all_goals
    (try split) <;> step* <;> simp [BytePost, finalValue] at * <;>
      (try split_ifs) <;>
      simp_all [mul_comm] <;>
      scalar_tac_preprocess <;> nlinarith


end Itasca.Binary.SignedLeb

namespace Itasca.Binary.SignedLeb

variable (format : Format)

private theorem payload_append (xs ys : List U8) :
    Binary.Leb128.payload (xs ++ ys) = Binary.Leb128.payload xs + 128 ^ xs.length * Binary.Leb128.payload ys := by
  induction xs with
  | nil => simp [Binary.Leb128.payload_nil, Binary.Leb128.payload_cons]
  | cons b xs ih => simp [Binary.Leb128.payload_nil, Binary.Leb128.payload_cons, ih, pow_succ]; ring

/-- A successful read consumes an `Encoding` of the value and leaves the input suffix untouched. -/
def Decoded (data : Slice U8) (start : Usize) (value : Int) (next : Usize) : Prop :=
  ∃ bytes, data.val.drop start.val = bytes ++ data.val.drop next.val ∧
    next.val = start.val + bytes.length ∧ next.val ≤ data.length ∧ Encoding format bytes value

/-- Malformed or truncated input for the signed reader: end of input, an overlong encoding, or a
value outside the format's range. -/
inductive Rejected (format : Format) (data : Slice U8) (start : Usize) : error.OpError → Prop where
  | eof (before : List U8)
      (bytes : data.val.drop start.val = before) (length : before.length ≤ format.last.val)
      (continuations : ∀ b ∈ before, 128 ≤ b.val) :
      Rejected format data start .UnexpectedEof
  | continued (before : List U8) (last : U8) (after : List U8)
      (bytes : data.val.drop start.val = before ++ last :: after)
      (length : before.length = format.last.val) (continuations : ∀ b ∈ before, 128 ≤ b.val)
      (last_continues : 128 ≤ last.val) : Rejected format data start .LebTooLong
  | range (before : List U8) (last : U8) (after : List U8)
      (bytes : data.val.drop start.val = before ++ last :: after)
      (length : before.length ≤ format.last.val) (continuations : ∀ b ∈ before, 128 ≤ b.val)
      (last_terminates : last.val < 128)
      (outside : finalValue (Binary.Leb128.payload before) (128 ^ before.length) last < format.lower.val ∨
        format.upper.val < finalValue (Binary.Leb128.payload before) (128 ^ before.length) last) :
      Rejected format data start .LebTooLong

/-- The result of the signed readers: a `Decoded` span on success and a `Rejected` description on
failure. -/
def Post (data : Slice U8) (start : Usize) {ty : IScalarTy} :
    core.result.Result (IScalar ty × Usize) error.OpError → Prop
  | .Ok (value, next) => Decoded format data start value.val next
  | .Err e => Rejected format data start e

private def LoopInvariant (data : Slice U8) (start : Usize)
    (s : I128 × I128 × Usize × U32) : Prop :=
  Invariant format s.1 s.2.1 s.2.2.2 ∧ s.2.2.1.val = start.val + s.2.2.2.val ∧
  ∃ before : List U8, before.length = s.2.2.2.val ∧
    data.val.drop start.val = before ++ data.val.drop s.2.2.1.val ∧
    s.1.val = Binary.Leb128.payload before ∧ (∀ b ∈ before, 128 ≤ b.val)

/-- `reader.read_sn_leb` is total and its result satisfies `Post`. -/
theorem spec128 (data : Slice U8) (start : Usize) :
    reader.read_sn_leb data start format.last format.lower format.upper ⦃ Post format data start ⦄ := by
  unfold reader.read_sn_leb reader.read_sn_leb_loop
  apply loop.spec_decr_nat (fun s => (format.last.val + 1) - s.2.2.2.val) (LoopInvariant format data start)
  · rintro ⟨acc, mult, p, i⟩ ⟨hinv, hpos, before, hlen, hbytes, hacc, hmore⟩
    dsimp only at *
    by_cases hp : p.val < data.length
    · apply WP.spec_mono (byte_spec format data p acc mult i hp hinv)
      intro r hr
      have hdrop := List.drop_eq_getElem_cons hp
      have hvalue : finalValue acc.val mult.val data.val[p.val] =
          finalValue (Binary.Leb128.payload before) (128 ^ before.length) data.val[p.val] := by
        rw [hacc, hlen, hinv.2.1]
      cases r with
      | done r =>
        cases r with
        | Err e =>
          rcases hr with ⟨rfl, hcont | hout⟩
          · apply Rejected.continued before data.val[p.val] (data.val.drop (p.val + 1))
            · rw [hbytes, hdrop]
            · omega
            · exact hmore
            · exact hcont.1
          · apply Rejected.range before data.val[p.val] (data.val.drop (p.val + 1))
            · rw [hbytes, hdrop]
            · simpa [hlen] using hinv.1
            · exact hmore
            · exact hout.1
            · simpa [hvalue] using hout.2
        | Ok r =>
          rcases r with ⟨value, next⟩
          rcases hr with ⟨hq, hv, hb, hlo, hhi⟩
          refine ⟨before ++ [data.val[p.val]], ?_, ?_, by omega, ?_⟩
          · rw [hbytes, hdrop, hq]; simp
          · simp [hpos, hlen, hq, Nat.add_assoc]
          · exact ⟨before, data.val[p.val], rfl, by simpa [hlen] using hinv.1,
              hmore, hb, hv.trans hvalue, hlo, hhi⟩
      | cont s =>
        rcases s with ⟨a, m, q, j⟩
        rcases hr with ⟨hnew, hj, hq, ha, hb⟩
        dsimp only [LoopInvariant]
        refine ⟨⟨hnew, by omega, before ++ [data.val[p.val]], ?_, ?_, ?_, ?_⟩, ?_⟩
        · simp [hlen, hj]
        · rw [hbytes, hdrop, hq]; simp
        · rw [payload_append, Binary.Leb128.payload, Binary.Leb128.payload]
          push_cast
          rw [ha, hacc, hlen, hinv.2.1]
          push_cast
          ring
        · intro b hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact hmore b hmem
          · simpa using (List.mem_singleton.mp hmem) ▸ hb
        · have := hnew.1
          omega
    · have hp' : p ≥ Slice.len data := by scalar_tac
      simp only [reader.read_sn_leb_loop.body, hp', ↓reduceIte, WP.spec_ok]
      apply Rejected.eof before
      · simpa [List.drop_eq_nil_of_le (by scalar_tac : data.val.length ≤ p.val)] using hbytes
      · simpa [hlen] using hinv.1
      · exact hmore
  · dsimp only [LoopInvariant, Invariant]
    exact ⟨⟨by simp, rfl, by decide, by decide⟩, by simp,
      [], by simp, by simp, rfl, by simp⟩

/-- A successful decoding consumes between one and `format.last + 1` bytes within the input. -/
theorem Decoded.span (data : Slice U8) (start : Usize) (value : Int) (next : Usize)
    (h : Decoded format data start value next) :
    start.val < next.val ∧ next.val ≤ start.val + (format.last.val + 1) ∧ next.val ≤ data.length := by
  rcases h with ⟨bs, _, hq, hbound, before, last, rfl, hlen, _⟩
  simp only [List.length_append, List.length_singleton] at hq
  omega

/-- A decoded value lies within the format's range. -/
theorem Decoded.range (data : Slice U8) (start : Usize) (value : Int) (next : Usize)
    (h : Decoded format data start value next) : format.lower.val ≤ value ∧ value ≤ format.upper.val := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hbounds⟩
  exact hbounds

end Itasca.Binary.SignedLeb

namespace Itasca.Binary.SignedLeb

variable (format : Format)

theorem Encoding.prefix_unique {xs ys : List U8} {x y : Int} {leftTail rightTail : List U8}
    (hx : Encoding format xs x) (hy : Encoding format ys y) (heq : xs ++ leftTail = ys ++ rightTail) :
    xs = ys ∧ x = y :=
  WebAssembly.Binary.Leb128.SignedForm.prefix_unique hx hy heq

/-- A successful decoding and a rejection of the same input cannot both hold. -/
theorem decoded_not_rejected (data : Slice U8) (start : Usize)
    (value : Int) (next : Usize) (e : error.OpError)
    (hd : Decoded format data start value next) (hr : Rejected format data start e) : False := by
  rcases hd with ⟨bytes, hbytes, hpos, hbound, before, last, rfl,
    hlen, hmore, hlast, hvalue, hlo, hhi⟩
  simp only [List.append_assoc, List.singleton_append] at hbytes
  cases hr with
  | eof bs hbs hbslen hbscont =>
    have hmem : last ∈ bs := by rw [← hbs, hbytes]; simp
    have := hbscont last hmem
    omega
  | continued bs b after hbs hbslen hbscont hb =>
    have heq : before ++ last :: data.val.drop next.val = bs ++ b :: after := hbytes.symm.trans hbs
    have hle := WebAssembly.Binary.Leb128.continuation_prefix_le UScalar.val before bs last (data.val.drop next.val)
      (b :: after) hmore hbscont hlast heq
    have hlen' : before.length = format.last.val := by omega
    have hfirst : before = bs := by
      have := congrArg (List.take before.length) heq
      simpa [List.take_append, hlen', hbslen] using this
    subst bs
    have hlb : last = b := (List.cons.inj (List.append_cancel_left heq)).1
    subst b
    omega
  | range bs b after hbs _ hbscont hb hout =>
    obtain ⟨rfl, rfl⟩ := WebAssembly.Binary.Leb128.terminated_unique UScalar.val before bs last b (data.val.drop next.val) after
      hmore hbscont hlast hb (hbytes.symm.trans hbs)
    omega

/-- Signed byte descriptions determine both the value and ending cursor. -/
theorem Decoded.deterministic (data : Slice U8) (start : Usize)
    (v₁ v₂ : Int) (q₁ q₂ : Usize)
    (h₁ : Decoded format data start v₁ q₁) (h₂ : Decoded format data start v₂ q₂) :
    v₁ = v₂ ∧ q₁ = q₂ := by
  rcases h₁ with ⟨bs₁, heq₁, hq₁, _, henc₁⟩
  rcases h₂ with ⟨bs₂, heq₂, hq₂, _, henc₂⟩
  obtain ⟨hbs, hv⟩ := Encoding.prefix_unique format henc₁ henc₂ (heq₁.symm.trans heq₂)
  refine ⟨hv, UScalar.eq_of_val_eq ?_⟩
  rw [hbs] at hq₁
  exact hq₁.trans hq₂.symm

end Itasca.Binary.SignedLeb

end

/-! ## SignedLeb33 -/

section

/-!
# Signed 33-bit LEB128

Instantiates `Binary.SignedLeb` for the extracted `reader.read_s33_leb`: `Binary.SignedLeb33.format` has
range [-2^32, 2^32 - 1] and at most 5 bytes. The `reader.read_s33_leb` lemmas
`spec` and `complete` establish normal return and acceptance: the reader
returns exactly the `Binary.SignedLeb33.Decoded` spans and rejects the `Binary.SignedLeb33.Rejected` inputs.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary.SignedLeb33

/-- The consumed encoding and untouched input suffix determine a successful read. -/
abbrev Decoded := Binary.SignedLeb.Decoded format

/-- Malformed or truncated input for the signed 33-bit reader. -/
abbrev Rejected := Binary.SignedLeb.Rejected format

/-- The result of the signed 33-bit reader. -/
abbrev Post := Binary.SignedLeb.Post format

/-- The shared `I128` loop specialized to this format. -/
theorem spec128 (data : Slice U8) (start : Usize) :
    reader.read_sn_leb data start 4#u32 (-4294967296)#i128 4294967295#i128 ⦃ Post data start ⦄ :=
  Binary.SignedLeb.spec128 format data start

/-- A successful decoding consumes between one and 5 bytes within the input. -/
theorem Decoded.span (data : Slice U8) (start : Usize) (value : Int) (next : Usize)
    (h : Decoded data start value next) :
    start.val < next.val ∧ next.val ≤ start.val + 5 ∧ next.val ≤ data.length :=
  Binary.SignedLeb.Decoded.span format data start value next h

/-- A decoded value lies within the signed 33-bit range. -/
theorem Decoded.range (data : Slice U8) (start : Usize) (value : Int) (next : Usize)
    (h : Decoded data start value next) : -4294967296 ≤ value ∧ value ≤ 4294967295 :=
  Binary.SignedLeb.Decoded.range format data start value next h

/-- Two encodings that are prefixes of the same byte string are equal and have equal values. -/
theorem Encoding.prefix_unique {xs ys : List U8} {x y : Int} {leftTail rightTail : List U8}
    (hx : Encoding xs x) (hy : Encoding ys y) (he : xs ++ leftTail = ys ++ rightTail) :
    xs = ys ∧ x = y :=
  Binary.SignedLeb.Encoding.prefix_unique format hx hy he

/-- Byte descriptions determine both the value and the ending cursor. -/
theorem Decoded.deterministic (data : Slice U8) (start : Usize)
    (v₁ v₂ : Int) (q₁ q₂ : Usize)
    (h₁ : Decoded data start v₁ q₁) (h₂ : Decoded data start v₂ q₂) :
    v₁ = v₂ ∧ q₁ = q₂ :=
  Binary.SignedLeb.Decoded.deterministic format data start v₁ v₂ q₁ q₂ h₁ h₂

private theorem decoded_not_rejected (data : Slice U8) (start : Usize)
    (value : Int) (next : Usize) (e : error.OpError)
    (hd : Decoded data start value next) (hr : Rejected data start e) : False :=
  Binary.SignedLeb.decoded_not_rejected format data start value next e hd hr

end Itasca.Binary.SignedLeb33

namespace Itasca

/-- Signed 33-bit decoding into `I64` is total, preserves the signed value during the I128-to-I64
cast, and reports exact consumed bytes or a malformed-input description. -/
@[step]
theorem reader.read_s33_leb.spec (data : Slice U8) (start : Usize) :
    reader.read_s33_leb data start ⦃ Binary.SignedLeb33.Post data start ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (Binary.SignedLeb33.spec128 data start)
  simp only [reader.read_s33_leb, hr, bind_ok]
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Binary.SignedLeb.Post]
    exact hp
  | Ok r =>
    rcases r with ⟨v, p⟩
    have hb := Binary.SignedLeb33.Decoded.range data start v.val p hp
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with IScalar.cast_inBounds_spec .I64 v (by scalar_tac) as ⟨x, hx⟩
    simpa [Binary.SignedLeb.Post, hx] using hp

end Itasca

namespace Itasca

/-- Every signed 33-bit byte encoding is accepted, including nonminimal sign extension. -/
theorem reader.read_s33_leb.complete (data : Slice U8) (start : Usize)
    (value : I64) (next : Usize) (h : Binary.SignedLeb33.Decoded data start value.val next) :
    reader.read_s33_leb data start = .ok (.Ok (value, next)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_s33_leb.spec data start)
  cases r with
  | Ok r =>
    obtain ⟨v, q⟩ := r
    obtain ⟨hv, rfl⟩ := Binary.SignedLeb33.Decoded.deterministic data start v.val value.val q next hp h
    have heq : v = value := IScalar.eq_of_val_eq hv
    simpa [heq] using hr
  | Err e => exact False.elim (Binary.SignedLeb33.decoded_not_rejected data start value.val next e h hp)

end Itasca

end

end

/-! ## LebReaders -/

section

/-!
Proofs for Binary.

This module collects SignedLeb64, ScalarReaders.
Each section documents its contracts and consumers.
-/

/-! ## SignedLeb64 -/

section

/-!
# Signed 64-bit LEB128

Instantiates `Binary.SignedLeb` for the extracted `reader.read_s64_leb`: `Binary.SignedLeb64.format` has
range [-2^63, 2^63 - 1] and at most 10 bytes. The `reader.read_s64_leb` lemmas
`spec` and `complete` establish normal return and acceptance: the reader
returns exactly the `Binary.SignedLeb64.Decoded` spans and rejects the `Binary.SignedLeb64.Rejected` inputs.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary.SignedLeb64

/-- The consumed encoding and untouched input suffix determine a successful read. -/
abbrev Decoded := Binary.SignedLeb.Decoded format

/-- Malformed or truncated input for the signed 64-bit reader. -/
abbrev Rejected := Binary.SignedLeb.Rejected format

/-- The result of the signed 64-bit reader. -/
abbrev Post := Binary.SignedLeb.Post format

/-- The shared `I128` loop specialized to this format. -/
theorem spec128 (data : Slice U8) (start : Usize) :
    reader.read_sn_leb data start 9#u32 (-9223372036854775808)#i128 9223372036854775807#i128 ⦃ Post data start ⦄ :=
  Binary.SignedLeb.spec128 format data start

/-- A successful decoding consumes between one and 10 bytes within the input. -/
theorem Decoded.span (data : Slice U8) (start : Usize) (value : Int) (next : Usize)
    (h : Decoded data start value next) :
    start.val < next.val ∧ next.val ≤ start.val + 10 ∧ next.val ≤ data.length :=
  Binary.SignedLeb.Decoded.span format data start value next h

/-- A decoded value lies within the signed 64-bit range. -/
theorem Decoded.range (data : Slice U8) (start : Usize) (value : Int) (next : Usize)
    (h : Decoded data start value next) : -9223372036854775808 ≤ value ∧ value ≤ 9223372036854775807 :=
  Binary.SignedLeb.Decoded.range format data start value next h

/-- Two encodings that are prefixes of the same byte string are equal and have equal values. -/
theorem Encoding.prefix_unique {xs ys : List U8} {x y : Int} {leftTail rightTail : List U8}
    (hx : Encoding xs x) (hy : Encoding ys y) (he : xs ++ leftTail = ys ++ rightTail) :
    xs = ys ∧ x = y :=
  Binary.SignedLeb.Encoding.prefix_unique format hx hy he

/-- Byte descriptions determine both the value and the ending cursor. -/
theorem Decoded.deterministic (data : Slice U8) (start : Usize)
    (v₁ v₂ : Int) (q₁ q₂ : Usize)
    (h₁ : Decoded data start v₁ q₁) (h₂ : Decoded data start v₂ q₂) :
    v₁ = v₂ ∧ q₁ = q₂ :=
  Binary.SignedLeb.Decoded.deterministic format data start v₁ v₂ q₁ q₂ h₁ h₂

private theorem decoded_not_rejected (data : Slice U8) (start : Usize)
    (value : Int) (next : Usize) (e : error.OpError)
    (hd : Decoded data start value next) (hr : Rejected data start e) : False :=
  Binary.SignedLeb.decoded_not_rejected format data start value next e hd hr

end Itasca.Binary.SignedLeb64

namespace Itasca

/-- Signed I64 decoding is total, preserves the signed value during the I128-to-I64
cast, and reports exact consumed bytes or a malformed-input description. -/
@[step]
theorem reader.read_s64_leb.spec (data : Slice U8) (start : Usize) :
    reader.read_s64_leb data start ⦃ Binary.SignedLeb64.Post data start ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (Binary.SignedLeb64.spec128 data start)
  simp only [reader.read_s64_leb, hr, bind_ok]
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Binary.SignedLeb.Post]
    exact hp
  | Ok r =>
    rcases r with ⟨v, p⟩
    have hb := Binary.SignedLeb64.Decoded.range data start v.val p hp
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with IScalar.cast_inBounds_spec .I64 v (by scalar_tac) as ⟨x, hx⟩
    simpa [Binary.SignedLeb.Post, hx] using hp

end Itasca

namespace Itasca

/-- Every signed I64 byte encoding is accepted, including nonminimal sign extension. -/
theorem reader.read_s64_leb.complete (data : Slice U8) (start : Usize)
    (value : I64) (next : Usize) (h : Binary.SignedLeb64.Decoded data start value.val next) :
    reader.read_s64_leb data start = .ok (.Ok (value, next)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_s64_leb.spec data start)
  cases r with
  | Ok r =>
    obtain ⟨v, q⟩ := r
    obtain ⟨hv, rfl⟩ := Binary.SignedLeb64.Decoded.deterministic data start v.val value.val q next hp h
    have heq : v = value := IScalar.eq_of_val_eq hv
    simpa [heq] using hr
  | Err e => exact False.elim (Binary.SignedLeb64.decoded_not_rejected data start value.val next e h hp)

end Itasca

end

/-! ## ScalarReaders -/

section

/-!
# Fixed-width bits and signed integer readers

Float-bit spans and signed 32-bit LEB encodings are related to the extracted readers.
Normal-return, acceptance and uniqueness facts preserve the exact consumed byte interval.
-/

/-! ## FloatBits -/

section

/-!
# Fixed-width float bit patterns

Describes little-endian fixed-width byte spans (`Binary.FloatBits.Encoding`, `Decoded`, `Rejected`) and
proves that the extracted `reader.read_f32_bits` and `reader.read_f64_bits` are total and agree
with them through their `spec` and `complete` contracts. The only rejection is truncated input.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary.FloatBits

private theorem payload_append (xs ys : List U8) :
    payload (xs ++ ys) = payload xs + 256 ^ xs.length * payload ys := by
  induction xs with
  | nil => simp [payload_nil, payload_cons]
  | cons b xs ih => simp [payload_nil, payload_cons, ih, pow_succ]; ring

/-- The value of a byte list is below `256 ^ length`. -/
theorem payload_lt (bs : List U8) : payload bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [payload_nil, payload_cons]
  | cons b bs ih =>
    have hb : b.val < 256 := by scalar_tac
    simp only [payload_nil, payload_cons, List.length_cons, pow_succ]
    omega

/-- A successful read consumes `n` bytes that form an `Encoding` and leaves the suffix untouched. -/
def Decoded (n : Nat) (data : Slice U8) (start : Usize) (bits : Nat) (next : Usize) : Prop :=
  ∃ bytes, data.val.drop start.val = bytes ++ data.val.drop next.val ∧
    next.val = start.val + n ∧ next.val ≤ data.length ∧ Encoding n bytes bits

/-- Fixed-width bit readers reject only truncated input. -/
def Rejected (n : Nat) (data : Slice U8) (start : Usize) (e : error.OpError) : Prop :=
  e = .UnexpectedEof ∧ data.length < start.val + n

/-- The result of the fixed-width readers: a `Decoded` span on success and `Rejected` on failure. -/
def Post (n : Nat) (data : Slice U8) (start : Usize) {ty : UScalarTy} :
    core.result.Result (UScalar ty × Usize) error.OpError → Prop
  | .Ok (bits, next) => Decoded n data start bits.val next
  | .Err e => Rejected n data start e

private def Invariant (n : U32) (acc mult : U64) (i : U32) : Prop :=
  i.val < n.val ∧ n.val ≤ 8 ∧ mult.val = 256 ^ i.val ∧ acc.val < mult.val

private def BytePost (n : U32) (acc mult : U64) (i : U32) (p : Usize) (b : U8) :
    ControlFlow (U64 × U64 × Usize × U32)
      (core.result.Result (U64 × Usize) error.OpError) → Prop
  | .done (.Err _) => False
  | .done (.Ok (v, q)) => q.val = p.val + 1 ∧
      v.val = acc.val + b.val * mult.val ∧ i.val + 1 = n.val
  | .cont (a, m, q, j) => Invariant n a m j ∧ j.val = i.val + 1 ∧
      q.val = p.val + 1 ∧ a.val = acc.val + b.val * mult.val

@[step] private theorem byte_cast_spec (b : U8) :
    lift (UScalar.cast .U64 b) ⦃ r => r.val = b.val ⦄ :=
  UScalar.cast_inBounds_spec .U64 b (by scalar_tac)

set_option maxHeartbeats 1000000 in
private theorem byte_spec (data : Slice U8) (n : U32) (p : Usize) (acc mult : U64) (i : U32)
    (hp : p.val < data.length) (hinv : Invariant n acc mult i) :
    reader.read_fn_bits_loop.body data n acc mult p i ⦃ BytePost n acc mult i p data.val[p.val] ⦄ := by
  rcases hinv with ⟨hi, hn, hm, ha⟩
  unfold reader.read_fn_bits_loop.body
  have hne : i ≠ n := by scalar_tac
  simp only [hne, ↓reduceIte]
  have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
      i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 := by omega
  rcases hcases with hi | hi | hi | hi | hi | hi | hi | hi <;>
    simp only [hi] at hm <;> norm_num at hm <;>
    step* <;> simp_all [BytePost, Invariant] <;> scalar_tac

private def LoopInvariant (n : U32) (data : Slice U8) (start : Usize)
    (s : U64 × U64 × Usize × U32) : Prop :=
  Invariant n s.1 s.2.1 s.2.2.2 ∧ s.2.2.1.val = start.val + s.2.2.2.val ∧
  ∃ before : List U8, before.length = s.2.2.2.val ∧
    data.val.drop start.val = before ++ data.val.drop s.2.2.1.val ∧ s.1.val = payload before

/-- `reader.read_fn_bits` is total for widths one through eight and its result satisfies `Post`. -/
theorem spec64 (n : U32) (hn : 0 < n.val ∧ n.val ≤ 8) (data : Slice U8) (start : Usize) :
    reader.read_fn_bits data start n ⦃ Post n.val data start ⦄ := by
  unfold reader.read_fn_bits reader.read_fn_bits_loop
  apply loop.spec_decr_nat (fun s => n.val - s.2.2.2.val) (LoopInvariant n data start)
  · rintro ⟨acc, mult, p, i⟩ ⟨hinv, hpos, before, hlen, hbytes, hacc⟩
    dsimp only at *
    by_cases hp : p.val < data.length
    · apply WP.spec_mono (byte_spec data n p acc mult i hp hinv)
      intro r hr
      have hdrop := List.drop_eq_getElem_cons hp
      cases r with
      | done r =>
        cases r with
        | Err e => exact False.elim hr
        | Ok r =>
          rcases r with ⟨value, next⟩
          rcases hr with ⟨hq, hv, hn⟩
          refine ⟨before ++ [data.val[p.val]], ?_, by omega, by omega, ?_, ?_⟩
          · rw [hbytes, hdrop, hq]; simp
          · simp [hlen, hn]
          · rw [payload_append, payload, payload, hv, hacc, hinv.2.2.1, hlen]
            ring
      | cont s =>
        rcases s with ⟨a, m, q, j⟩
        rcases hr with ⟨hnew, hj, hq, ha⟩
        dsimp only [LoopInvariant]
        refine ⟨⟨hnew, by omega, before ++ [data.val[p.val]], ?_, ?_, ?_⟩, ?_⟩
        · simp [hlen, hj]
        · rw [hbytes, hdrop, hq]; simp
        · rw [payload_append, payload, payload, ha, hacc, hinv.2.2.1, hlen]
          ring
        · have := hnew.1
          omega
    · have hp' : p ≥ Slice.len data := by scalar_tac
      have hne : i ≠ n := by have := hinv.1; scalar_tac
      simp only [reader.read_fn_bits_loop.body, hne, hp', ↓reduceIte, WP.spec_ok]
      exact ⟨rfl, by have := hinv.1; omega⟩
  · dsimp only [LoopInvariant, Invariant]
    exact ⟨⟨hn.1, hn.2, rfl, by decide⟩, by simp, [], by simp, by simp, rfl⟩

/-- A successful read ends exactly `n` bytes after the start, within the input. -/
theorem Decoded.span (n : Nat) (data : Slice U8) (start : Usize) (bits : Nat) (next : Usize)
    (h : Decoded n data start bits next) : next.val = start.val + n ∧ next.val ≤ data.length := by
  rcases h with ⟨_, _, hpos, hbound, _⟩
  exact ⟨hpos, hbound⟩

/-- The decoded bit pattern fits in `n` bytes. -/
theorem Decoded.range (n : Nat) (data : Slice U8) (start : Usize) (bits : Nat) (next : Usize)
    (h : Decoded n data start bits next) : bits < 256 ^ n := by
  rcases h with ⟨bs, _, _, _, hlen, rfl⟩
  simpa [hlen] using payload_lt bs

end Itasca.Binary.FloatBits

namespace Itasca

/-- `reader.read_f32_bits` is total and its result satisfies `Binary.FloatBits.Post 4`. -/
@[step] theorem reader.read_f32_bits.spec (data : Slice U8) (start : Usize) :
    reader.read_f32_bits data start ⦃ Binary.FloatBits.Post 4 data start ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (Binary.FloatBits.spec64 4#u32 (by decide) data start)
  simp only [reader.read_f32_bits, hr, bind_ok]
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Binary.FloatBits.Post]
    exact hp
  | Ok r =>
    rcases r with ⟨v, p⟩
    have hb := Binary.FloatBits.Decoded.range 4 data start v.val p hp
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with UScalar.cast_inBounds_spec .U32 v (by scalar_tac)
    simpa [Binary.FloatBits.Post, *] using hp

/-- `reader.read_f64_bits` is total and its result satisfies `Binary.FloatBits.Post 8`. -/
@[step] theorem reader.read_f64_bits.spec (data : Slice U8) (start : Usize) :
    reader.read_f64_bits data start ⦃ Binary.FloatBits.Post 8 data start ⦄ :=
  Binary.FloatBits.spec64 8#u32 (by decide) data start

end Itasca

namespace Itasca.Binary.FloatBits

/-- A fixed-width byte span determines its bit pattern and ending cursor. -/
theorem Decoded.deterministic (n : Nat) (data : Slice U8) (start : Usize)
    (v₁ v₂ : Nat) (q₁ q₂ : Usize)
    (h₁ : Decoded n data start v₁ q₁) (h₂ : Decoded n data start v₂ q₂) :
    v₁ = v₂ ∧ q₁ = q₂ := by
  rcases h₁ with ⟨bs₁, heq₁, hq₁, _, hlen₁, rfl⟩
  rcases h₂ with ⟨bs₂, heq₂, hq₂, _, hlen₂, rfl⟩
  have hbs : bs₁ = bs₂ := by
    have := congrArg (List.take n) (heq₁.symm.trans heq₂)
    simpa [List.take_append, hlen₁, hlen₂] using this
  exact ⟨congrArg payload hbs, UScalar.eq_of_val_eq (hq₁.trans hq₂.symm)⟩

end Itasca.Binary.FloatBits

namespace Itasca

/-- Every four-byte `Decoded` span is accepted by `reader.read_f32_bits`. -/
theorem reader.read_f32_bits.complete (data : Slice U8) (start : Usize)
    (bits : U32) (next : Usize) (h : Binary.FloatBits.Decoded 4 data start bits.val next) :
    reader.read_f32_bits data start = .ok (.Ok (bits, next)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_f32_bits.spec data start)
  cases r with
  | Ok r =>
    obtain ⟨v, q⟩ := r
    obtain ⟨hv, rfl⟩ := Binary.FloatBits.Decoded.deterministic 4 data start v.val bits.val q next hp h
    have heq : v = bits := UScalar.eq_of_val_eq hv
    simpa [heq] using hr
  | Err e =>
    have := Binary.FloatBits.Decoded.span 4 data start bits.val next h
    have := hp.2
    omega

/-- Every eight-byte `Decoded` span is accepted by `reader.read_f64_bits`. -/
theorem reader.read_f64_bits.complete (data : Slice U8) (start : Usize)
    (bits : U64) (next : Usize) (h : Binary.FloatBits.Decoded 8 data start bits.val next) :
    reader.read_f64_bits data start = .ok (.Ok (bits, next)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_f64_bits.spec data start)
  cases r with
  | Ok r =>
    obtain ⟨v, q⟩ := r
    obtain ⟨hv, rfl⟩ := Binary.FloatBits.Decoded.deterministic 8 data start v.val bits.val q next hp h
    have heq : v = bits := UScalar.eq_of_val_eq hv
    simpa [heq] using hr
  | Err e =>
    have := Binary.FloatBits.Decoded.span 8 data start bits.val next h
    have := hp.2
    omega

end Itasca

end

/-! ## SignedLeb32 -/

section

/-!
# Signed 32-bit LEB128

Instantiates `Binary.SignedLeb` for the extracted `reader.read_s32_leb`: `Binary.SignedLeb32.format` has
range [-2^31, 2^31 - 1] and at most 5 bytes. The `reader.read_s32_leb` lemmas
`spec` and `complete` establish normal return and acceptance: the reader
returns exactly the `Binary.SignedLeb32.Decoded` spans and rejects the `Binary.SignedLeb32.Rejected` inputs.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary.SignedLeb32

/-- The consumed encoding and untouched input suffix determine a successful read. -/
abbrev Decoded := Binary.SignedLeb.Decoded format

/-- Malformed or truncated input for the signed 32-bit reader. -/
abbrev Rejected := Binary.SignedLeb.Rejected format

/-- The result of the signed 32-bit reader. -/
abbrev Post := Binary.SignedLeb.Post format

/-- The shared `I128` loop specialized to this format. -/
theorem spec128 (data : Slice U8) (start : Usize) :
    reader.read_sn_leb data start 4#u32 (-2147483648)#i128 2147483647#i128 ⦃ Post data start ⦄ :=
  Binary.SignedLeb.spec128 format data start

/-- A successful decoding consumes between one and 5 bytes within the input. -/
theorem Decoded.span (data : Slice U8) (start : Usize) (value : Int) (next : Usize)
    (h : Decoded data start value next) :
    start.val < next.val ∧ next.val ≤ start.val + 5 ∧ next.val ≤ data.length :=
  Binary.SignedLeb.Decoded.span format data start value next h

/-- A decoded value lies within the signed 32-bit range. -/
theorem Decoded.range (data : Slice U8) (start : Usize) (value : Int) (next : Usize)
    (h : Decoded data start value next) : -2147483648 ≤ value ∧ value ≤ 2147483647 :=
  Binary.SignedLeb.Decoded.range format data start value next h

/-- Two encodings that are prefixes of the same byte string are equal and have equal values. -/
theorem Encoding.prefix_unique {xs ys : List U8} {x y : Int} {leftTail rightTail : List U8}
    (hx : Encoding xs x) (hy : Encoding ys y) (he : xs ++ leftTail = ys ++ rightTail) :
    xs = ys ∧ x = y :=
  Binary.SignedLeb.Encoding.prefix_unique format hx hy he

/-- Byte descriptions determine both the value and the ending cursor. -/
theorem Decoded.deterministic (data : Slice U8) (start : Usize)
    (v₁ v₂ : Int) (q₁ q₂ : Usize)
    (h₁ : Decoded data start v₁ q₁) (h₂ : Decoded data start v₂ q₂) :
    v₁ = v₂ ∧ q₁ = q₂ :=
  Binary.SignedLeb.Decoded.deterministic format data start v₁ v₂ q₁ q₂ h₁ h₂

private theorem decoded_not_rejected (data : Slice U8) (start : Usize)
    (value : Int) (next : Usize) (e : error.OpError)
    (hd : Decoded data start value next) (hr : Rejected data start e) : False :=
  Binary.SignedLeb.decoded_not_rejected format data start value next e hd hr

end Itasca.Binary.SignedLeb32

namespace Itasca

/-- Signed I32 decoding is total, preserves the signed value during the I128-to-I32
cast, and reports exact consumed bytes or a malformed-input description. -/
@[step]
theorem reader.read_s32_leb.spec (data : Slice U8) (start : Usize) :
    reader.read_s32_leb data start ⦃ Binary.SignedLeb32.Post data start ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (Binary.SignedLeb32.spec128 data start)
  simp only [reader.read_s32_leb, hr, bind_ok]
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Binary.SignedLeb.Post]
    exact hp
  | Ok r =>
    rcases r with ⟨v, p⟩
    have hb := Binary.SignedLeb32.Decoded.range data start v.val p hp
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with IScalar.cast_inBounds_spec .I32 v (by scalar_tac) as ⟨x, hx⟩
    simpa [Binary.SignedLeb.Post, hx] using hp

end Itasca

namespace Itasca

/-- Every signed I32 byte encoding is accepted, including nonminimal sign extension. -/
theorem reader.read_s32_leb.complete (data : Slice U8) (start : Usize)
    (value : I32) (next : Usize) (h : Binary.SignedLeb32.Decoded data start value.val next) :
    reader.read_s32_leb data start = .ok (.Ok (value, next)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_s32_leb.spec data start)
  cases r with
  | Ok r =>
    obtain ⟨v, q⟩ := r
    obtain ⟨hv, rfl⟩ := Binary.SignedLeb32.Decoded.deterministic data start v.val value.val q next hp h
    have heq : v = value := IScalar.eq_of_val_eq hv
    simpa [heq] using hr
  | Err e => exact False.elim (Binary.SignedLeb32.decoded_not_rejected data start value.val next e h hp)

end Itasca

end

end

end

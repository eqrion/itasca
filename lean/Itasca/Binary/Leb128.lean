import Itasca.Binary.ReadByte

/-!
# Unsigned 32-bit LEB128

Defines the byte-level description of unsigned 32-bit LEB128 (`Leb128.Encoding`,
`Leb128.Decoded`, `Leb128.Rejected`) and proves that the extracted `reader.read_u32_leb` is total
and agrees with it (`reader.read_u32_leb.spec`, `.sound`, `.complete`, `.reject_complete`).
`Leb128.Encoding.prefix_unique` shows that an encoding is determined by its leading bytes.
-/

open Aeneas Aeneas.Std

namespace Itasca

private theorem leb_first_byte (data : Slice U8) (pos : Usize)
    (h : pos.val < data.length) (hbyte : (data.val[pos.val]).val < 128) :
    reader.read_u32_leb_loop.body data 0#u32 1#u32 pos 0#u32 ⦃ r =>
      ∃ value next, r = .done (.Ok (value, next)) ∧
        value.val = (data.val[pos.val]).val ∧ next.val = pos.val + 1 ⦄ := by
  unfold reader.read_u32_leb_loop.body
  step*

/-- A single byte below 128 decodes to its own value and advances the cursor by one. -/
theorem reader.read_u32_leb.single_byte (data : Slice U8) (pos : Usize)
    (h : pos.val < data.length) (hbyte : (data.val[pos.val]).val < 128) :
    ∃ value next, reader.read_u32_leb data pos = .ok (.Ok (value, next)) ∧
      value.val = (data.val[pos.val]).val ∧ next.val = pos.val + 1 := by
  obtain ⟨_, hr, value, next, rfl, hv, hp⟩ := WP.spec_imp_exists (leb_first_byte data pos h hbyte)
  refine ⟨value, next, ?_, hv, hp⟩
  unfold reader.read_u32_leb reader.read_u32_leb_loop
  rw [loop]
  simp [hr]

end Itasca

namespace Itasca.Leb128

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

end Itasca.Leb128

namespace Itasca.Leb128

/-- Little-endian base-128 payload, independent of the implementation's scalars. -/
def payload : List U8 → Nat
  | [] => 0
  | b :: bs => b.val % 128 + 128 * payload bs

private theorem payload_append (xs ys : List U8) :
    payload (xs ++ ys) = payload xs + 128 ^ xs.length * payload ys := by
  induction xs with
  | nil => simp [payload]
  | cons b xs ih => simp [payload, ih, pow_succ]; ring

/-- An unsigned 32-bit binary encoding, including permitted non-minimal encodings.
The first four bytes may carry seven bits each; a fifth carries only four. -/
def Encoding (bytes : List U8) (value : Nat) : Prop :=
  ∃ before last, bytes = before ++ [last] ∧ before.length ≤ 4 ∧
    (∀ b ∈ before, 128 ≤ b.val) ∧ last.val < 128 ∧
    (before.length = 4 → last.val < 16) ∧ value = payload bytes

/-- A successful decoding identifies both the consumed bytes and the untouched suffix. -/
def Decoded (data : Slice U8) (start : Usize) (value : U32) (next : Usize) : Prop :=
  ∃ bytes, data.val.drop start.val = bytes ++ data.val.drop next.val ∧
    next.val = start.val + bytes.length ∧ next.val ≤ data.length ∧
    Encoding bytes value.val

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

end Itasca.Leb128

namespace Itasca.Leb128

/-- A continuation-byte prefix cannot pass an encoding's terminating byte. -/
private theorem continuation_prefix_le (xs ys : List U8) (a : U8) (leftTail bs : List U8)
    (hx : ∀ b ∈ xs, 128 ≤ b.val) (hy : ∀ b ∈ ys, 128 ≤ b.val)
    (ha : a.val < 128) (heq : xs ++ a :: leftTail = ys ++ bs) :
    ys.length ≤ xs.length := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp
    | cons y ys =>
      have hay : a = y := (List.cons.inj heq).1
      have := hy y (by simp)
      subst y
      omega
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      obtain ⟨hxy, htail⟩ := List.cons.inj heq
      have hxs : ∀ b ∈ xs, 128 ≤ b.val := by intros b hb; exact hx b (by simp [hb])
      have hys : ∀ b ∈ ys, 128 ≤ b.val := by intros b hb; exact hy b (by simp [hb])
      simpa using ih ys hxs hys htail

/-- Two encodings that are prefixes of the same byte string are equal and have equal values. -/
theorem Encoding.prefix_unique {xs ys : List U8} {x y : Nat} {leftTail bs : List U8}
    (hx : Encoding xs x) (hy : Encoding ys y) (heq : xs ++ leftTail = ys ++ bs) :
    xs = ys ∧ x = y := by
  rcases hx with ⟨xs', a, rfl, hxlen, hxmore, ha, hlast, rfl⟩
  rcases hy with ⟨ys', b, rfl, hylen, hymore, hb, hlast', rfl⟩
  simp only [List.append_assoc, List.singleton_append] at heq
  have hxy := continuation_prefix_le xs' ys' a leftTail (b :: bs) hxmore hymore ha heq
  have hyx := continuation_prefix_le ys' xs' b bs (a :: leftTail) hymore hxmore hb heq.symm
  have hlen : xs'.length = ys'.length := by omega
  have hfirst : xs' = ys' := by
    have := congrArg (List.take xs'.length) heq
    simpa [List.take_append, hlen] using this
  subst ys'
  have hab : a = b := (List.cons.inj (List.append_cancel_left heq)).1
  subst b
  exact ⟨rfl, rfl⟩

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
    have hle := continuation_prefix_le before bs last (data.val.drop next.val)
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

end Itasca.Leb128

namespace Itasca

/-- Total unsigned LEB128 decoding, including malformed input and exact byte spans. -/
@[step]
theorem reader.read_u32_leb.spec (data : Slice U8) (start : Usize) :
    reader.read_u32_leb data start ⦃ Leb128.Post data start ⦄ := Leb128.spec data start

/-- `reader.read_u32_leb` never panics. -/
theorem reader.read_u32_leb.total (data : Slice U8) (start : Usize) :
    ∃ r, reader.read_u32_leb data start = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  exact ⟨r, hr⟩

/-- A successful `reader.read_u32_leb` result is a `Decoded` span. -/
theorem reader.read_u32_leb.sound (data : Slice U8) (start : Usize)
    (value : U32) (next : Usize)
    (h : reader.read_u32_leb data start = .ok (.Ok (value, next))) :
    Leb128.Decoded data start value next := by
  have hs := reader.read_u32_leb.spec data start
  simpa [h, Leb128.Post] using hs

/-- Every encoding described by `Decoded` is accepted, including non-minimal encodings. -/
theorem reader.read_u32_leb.complete (data : Slice U8) (start : Usize)
    (value : U32) (next : Usize) (h : Leb128.Decoded data start value next) :
    reader.read_u32_leb data start = .ok (.Ok (value, next)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Ok r =>
    obtain ⟨v, q⟩ := r
    obtain ⟨rfl, rfl⟩ := Leb128.Decoded.deterministic data start v value q next hp h
    exact hr
  | Err e => exact False.elim (Leb128.decoded_not_rejected data start value next e h hp)

/-- A successful `reader.read_u32_leb` consumes between one and five bytes within the input. -/
theorem reader.read_u32_leb.success_span (data : Slice U8) (start : Usize)
    (value : U32) (next : Usize)
    (h : reader.read_u32_leb data start = .ok (.Ok (value, next))) :
    start.val < next.val ∧ next.val ≤ start.val + 5 ∧ next.val ≤ data.length :=
  Leb128.Decoded.span data start value next (reader.read_u32_leb.sound data start value next h)

/-- A rejected `reader.read_u32_leb` result satisfies `Leb128.Rejected`. -/
theorem reader.read_u32_leb.rejected (data : Slice U8) (start : Usize)
    (e : error.OpError) (h : reader.read_u32_leb data start = .ok (.Err e)) :
    Leb128.Rejected data start e := by
  have hs := reader.read_u32_leb.spec data start
  simpa [h, Leb128.Post] using hs

end Itasca

namespace Itasca.Leb128

private theorem payload_lt (bs : List U8) : payload bs < 128 ^ bs.length := by
  induction bs with
  | nil => simp [payload]
  | cons b bs ih =>
    have hm : b.val % 128 < 128 := Nat.mod_lt _ (by decide)
    simp only [payload, List.length_cons, pow_succ]
    omega

/-- The byte-level relation itself enforces the U32 range. -/
theorem Encoding.value_lt {bytes : List U8} {value : Nat} (h : Encoding bytes value) :
    value < 2 ^ 32 := by
  rcases h with ⟨before, last, rfl, hlen, _, hlast, hfifth, rfl⟩
  rw [payload_append]
  simp only [payload, mul_zero, add_zero, Nat.mod_eq_of_lt hlast]
  have hp := payload_lt before
  have hcases : before.length = 0 ∨ before.length = 1 ∨ before.length = 2 ∨
      before.length = 3 ∨ before.length = 4 := by omega
  rcases hcases with h | h | h | h | h <;>
    simp only [h] at hp hfifth ⊢ <;> norm_num at hp hfifth ⊢ <;> omega

/-- Unsigned LEB128 rejections are `UnexpectedEof` or `LebTooLong`. -/
theorem Rejected.kind {data : Slice U8} {start : Usize} {e : error.OpError}
    (h : Rejected data start e) : e = .UnexpectedEof ∨ e = .LebTooLong := by
  cases h <;> simp

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

end Itasca.Leb128

namespace Itasca

/-- Every `Leb128.Rejected` description is the result of `reader.read_u32_leb`. -/
theorem reader.read_u32_leb.reject_complete (data : Slice U8) (start : Usize)
    (e : error.OpError) (h : Leb128.Rejected data start e) :
    reader.read_u32_leb data start = .ok (.Err e) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Ok r => exact False.elim (Leb128.decoded_not_rejected data start r.1 r.2 e hp h)
  | Err e' =>
    have heq := Leb128.rejected_unique hp h
    simpa [heq] using hr

end Itasca

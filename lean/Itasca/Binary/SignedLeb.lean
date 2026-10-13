import Itasca.Binary.Leb128

/-!
# Signed LEB128, shared decoder

Describes signed LEB128 byte strings parameterized by a `SignedLeb.Format` (maximum length and
value range) and proves that the extracted `reader.read_sn_leb` loop, which computes in `I128`,
is total and agrees with the description (`SignedLeb.spec128`). The 32-, 33- and 64-bit readers
in `Binary/SignedLeb32`, `Binary/SignedLeb33` and `Binary/SignedLeb64` instantiate it.
-/

open Aeneas Aeneas.Std

namespace Itasca.SignedLeb

/-- Parameters of the shared `I128` signed decoder: the index of the last permitted byte and the
inclusive value range. The bound `last ≤ 9` keeps every intermediate operation within `I128`. -/
structure Format where
  last : U32
  lower : I128
  upper : I128
  last_le : last.val ≤ 9

variable (format : Format)

/-- The contribution of the terminating signed byte, including sign extension. -/
def finalValue (acc mult : Int) (last : U8) : Int :=
  acc + (last.val : Int) * mult - if 64 ≤ last.val then 128 * mult else 0

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

set_option maxHeartbeats 2000000 in
private theorem byte_spec (data : Slice U8) (p : Usize) (acc mult : I128) (i : U32)
    (hp : p.val < data.length) (hinv : Invariant format acc mult i) :
    reader.read_sn_leb_loop.body data format.last format.lower format.upper
      acc mult p i ⦃ BytePost format acc mult i p data.val[p.val] ⦄ := by
  rcases hinv with ⟨hi, hm, ha0, ha⟩
  unfold reader.read_sn_leb_loop.body
  have hmax : i.val ≤ 9 := hi.trans format.last_le
  have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
      i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 := by omega
  rcases hcases with hi | hi | hi | hi | hi | hi | hi | hi | hi | hi <;>
    simp only [hi] at hm <;> norm_num at hm <;>
    step* <;> try (simp_all [BytePost, Invariant, finalValue]; scalar_tac)
  all_goals
    (try split) <;> step* <;> simp_all [BytePost, finalValue] <;> split_ifs <;> scalar_tac

end Itasca.SignedLeb

namespace Itasca.SignedLeb

variable (format : Format)

private theorem payload_append (xs ys : List U8) :
    Leb128.payload (xs ++ ys) = Leb128.payload xs + 128 ^ xs.length * Leb128.payload ys := by
  induction xs with
  | nil => simp [Leb128.payload]
  | cons b xs ih => simp [Leb128.payload, ih, pow_succ]; ring

/-- Signed LEB128 bytes within the format's length and value bounds, permitting non-minimal sign
extension. -/
def Encoding (bytes : List U8) (value : Int) : Prop :=
  ∃ before last, bytes = before ++ [last] ∧ before.length ≤ format.last.val ∧
    (∀ b ∈ before, 128 ≤ b.val) ∧ last.val < 128 ∧
    value = finalValue (Leb128.payload before) (128 ^ before.length) last ∧
    format.lower.val ≤ value ∧ value ≤ format.upper.val

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
      (outside : finalValue (Leb128.payload before) (128 ^ before.length) last < format.lower.val ∨
        format.upper.val < finalValue (Leb128.payload before) (128 ^ before.length) last) :
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
    s.1.val = Leb128.payload before ∧ (∀ b ∈ before, 128 ≤ b.val)

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
          finalValue (Leb128.payload before) (128 ^ before.length) data.val[p.val] := by
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
        · rw [payload_append, Leb128.payload, Leb128.payload]
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

/-- Signed LEB128 rejections are `UnexpectedEof` or `LebTooLong`. -/
theorem Rejected.kind {data : Slice U8} {start : Usize} {e : error.OpError}
    (h : Rejected format data start e) : e = .UnexpectedEof ∨ e = .LebTooLong := by
  cases h <;> simp

end Itasca.SignedLeb

namespace Itasca.SignedLeb

variable (format : Format)

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

private theorem terminated_unique (xs ys : List U8) (a b : U8) (leftTail rightTail : List U8)
    (hx : ∀ c ∈ xs, 128 ≤ c.val) (hy : ∀ c ∈ ys, 128 ≤ c.val)
    (ha : a.val < 128) (hb : b.val < 128)
    (heq : xs ++ a :: leftTail = ys ++ b :: rightTail) : xs = ys ∧ a = b := by
  have hxy := continuation_prefix_le xs ys a leftTail (b :: rightTail) hx hy ha heq
  have hyx := continuation_prefix_le ys xs b rightTail (a :: leftTail) hy hx hb heq.symm
  have hlen : xs.length = ys.length := by omega
  have hfirst : xs = ys := by
    have := congrArg (List.take xs.length) heq
    simpa [List.take_append, hlen] using this
  subst ys
  exact ⟨rfl, (List.cons.inj (List.append_cancel_left heq)).1⟩

/-- Two encodings that are prefixes of the same byte string are equal and have equal values. -/
theorem Encoding.prefix_unique {xs ys : List U8} {x y : Int} {leftTail rightTail : List U8}
    (hx : Encoding format xs x) (hy : Encoding format ys y) (heq : xs ++ leftTail = ys ++ rightTail) :
    xs = ys ∧ x = y := by
  rcases hx with ⟨xs', a, rfl, _, hxmore, ha, rfl, _⟩
  rcases hy with ⟨ys', b, rfl, _, hymore, hb, rfl, _⟩
  simp only [List.append_assoc, List.singleton_append] at heq
  obtain ⟨rfl, rfl⟩ := terminated_unique xs' ys' a b leftTail rightTail hxmore hymore ha hb heq
  exact ⟨rfl, rfl⟩

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
    have hle := continuation_prefix_le before bs last (data.val.drop next.val)
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
    obtain ⟨rfl, rfl⟩ := terminated_unique before bs last b (data.val.drop next.val) after
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

end Itasca.SignedLeb

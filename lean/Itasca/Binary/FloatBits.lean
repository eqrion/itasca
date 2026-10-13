import Itasca.Binary.Leb128

/-!
# Fixed-width float bit patterns

Describes little-endian fixed-width byte spans (`FloatBits.Encoding`, `Decoded`, `Rejected`) and
proves that the extracted `reader.read_f32_bits` and `reader.read_f64_bits` are total and agree
with them (`spec`, `sound`, `complete`, `rejected`). The only rejection is truncated input.
-/

open Aeneas Aeneas.Std

namespace Itasca.FloatBits

/-- Little-endian value of a byte list, using every bit of each byte. -/
def payload : List U8 → Nat
  | [] => 0
  | b :: bs => b.val + 256 * payload bs

private theorem payload_append (xs ys : List U8) :
    payload (xs ++ ys) = payload xs + 256 ^ xs.length * payload ys := by
  induction xs with
  | nil => simp [payload]
  | cons b xs ih => simp [payload, ih, pow_succ]; ring

/-- The value of a byte list is below `256 ^ length`. -/
theorem payload_lt (bs : List U8) : payload bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [payload]
  | cons b bs ih =>
    have hb : b.val < 256 := by scalar_tac
    simp only [payload, List.length_cons, pow_succ]
    omega

/-- Exactly `n` bytes whose little-endian value is the bit pattern. -/
def Encoding (n : Nat) (bytes : List U8) (bits : Nat) : Prop :=
  bytes.length = n ∧ bits = payload bytes

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

end Itasca.FloatBits

namespace Itasca

/-- `reader.read_f32_bits` is total and its result satisfies `FloatBits.Post 4`. -/
@[step] theorem reader.read_f32_bits.spec (data : Slice U8) (start : Usize) :
    reader.read_f32_bits data start ⦃ FloatBits.Post 4 data start ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (FloatBits.spec64 4#u32 (by decide) data start)
  simp only [reader.read_f32_bits, hr, bind_ok]
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, FloatBits.Post]
    exact hp
  | Ok r =>
    rcases r with ⟨v, p⟩
    have hb := FloatBits.Decoded.range 4 data start v.val p hp
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with UScalar.cast_inBounds_spec .U32 v (by scalar_tac)
    simpa [FloatBits.Post, *] using hp

/-- `reader.read_f64_bits` is total and its result satisfies `FloatBits.Post 8`. -/
@[step] theorem reader.read_f64_bits.spec (data : Slice U8) (start : Usize) :
    reader.read_f64_bits data start ⦃ FloatBits.Post 8 data start ⦄ :=
  FloatBits.spec64 8#u32 (by decide) data start

end Itasca

namespace Itasca.FloatBits

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

end Itasca.FloatBits

namespace Itasca

/-- `reader.read_f32_bits` never panics. -/
theorem reader.read_f32_bits.total (data : Slice U8) (start : Usize) :
    ∃ r, reader.read_f32_bits data start = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (reader.read_f32_bits.spec data start)
  exact ⟨r, hr⟩

/-- A successful `reader.read_f32_bits` result is a four-byte `Decoded` span. -/
theorem reader.read_f32_bits.sound (data : Slice U8) (start : Usize)
    (bits : U32) (next : Usize)
    (h : reader.read_f32_bits data start = .ok (.Ok (bits, next))) :
    FloatBits.Decoded 4 data start bits.val next := by
  have hs := reader.read_f32_bits.spec data start
  simpa [h, FloatBits.Post] using hs

/-- A rejected `reader.read_f32_bits` result is `UnexpectedEof` on truncated input. -/
theorem reader.read_f32_bits.rejected (data : Slice U8) (start : Usize)
    (e : error.OpError) (h : reader.read_f32_bits data start = .ok (.Err e)) :
    FloatBits.Rejected 4 data start e := by
  have hs := reader.read_f32_bits.spec data start
  simpa [h, FloatBits.Post] using hs

/-- Every four-byte `Decoded` span is accepted by `reader.read_f32_bits`. -/
theorem reader.read_f32_bits.complete (data : Slice U8) (start : Usize)
    (bits : U32) (next : Usize) (h : FloatBits.Decoded 4 data start bits.val next) :
    reader.read_f32_bits data start = .ok (.Ok (bits, next)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_f32_bits.spec data start)
  cases r with
  | Ok r =>
    obtain ⟨v, q⟩ := r
    obtain ⟨hv, rfl⟩ := FloatBits.Decoded.deterministic 4 data start v.val bits.val q next hp h
    have heq : v = bits := UScalar.eq_of_val_eq hv
    simpa [heq] using hr
  | Err e =>
    have := FloatBits.Decoded.span 4 data start bits.val next h
    have := hp.2
    omega

/-- `reader.read_f64_bits` never panics. -/
theorem reader.read_f64_bits.total (data : Slice U8) (start : Usize) :
    ∃ r, reader.read_f64_bits data start = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (reader.read_f64_bits.spec data start)
  exact ⟨r, hr⟩

/-- A successful `reader.read_f64_bits` result is an eight-byte `Decoded` span. -/
theorem reader.read_f64_bits.sound (data : Slice U8) (start : Usize)
    (bits : U64) (next : Usize)
    (h : reader.read_f64_bits data start = .ok (.Ok (bits, next))) :
    FloatBits.Decoded 8 data start bits.val next := by
  have hs := reader.read_f64_bits.spec data start
  simpa [h, FloatBits.Post] using hs

/-- A rejected `reader.read_f64_bits` result is `UnexpectedEof` on truncated input. -/
theorem reader.read_f64_bits.rejected (data : Slice U8) (start : Usize)
    (e : error.OpError) (h : reader.read_f64_bits data start = .ok (.Err e)) :
    FloatBits.Rejected 8 data start e := by
  have hs := reader.read_f64_bits.spec data start
  simpa [h, FloatBits.Post] using hs

/-- Every eight-byte `Decoded` span is accepted by `reader.read_f64_bits`. -/
theorem reader.read_f64_bits.complete (data : Slice U8) (start : Usize)
    (bits : U64) (next : Usize) (h : FloatBits.Decoded 8 data start bits.val next) :
    reader.read_f64_bits data start = .ok (.Ok (bits, next)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_f64_bits.spec data start)
  cases r with
  | Ok r =>
    obtain ⟨v, q⟩ := r
    obtain ⟨hv, rfl⟩ := FloatBits.Decoded.deterministic 8 data start v.val bits.val q next hp h
    have heq : v = bits := UScalar.eq_of_val_eq hv
    simpa [heq] using hr
  | Err e =>
    have := FloatBits.Decoded.span 8 data start bits.val next h
    have := hp.2
    omega

end Itasca

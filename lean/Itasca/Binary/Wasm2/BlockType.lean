import Itasca.Binary.SignedLeb33

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

def valueByte : types.ValueType → U8
  | .I32 => 127#u8
  | .I64 => 126#u8
  | .F32 => 125#u8
  | .F64 => 124#u8
  | .V128 => 123#u8
  | .FuncRef => 112#u8
  | .ExternRef => 111#u8

theorem valueByte_injective : Function.Injective valueByte := by
  intro a b h
  cases a <;> cases b <;> simp_all [valueByte]

/-- Inline value tags are negative one-byte signed integers, so they cannot
    be confused with a nonnegative type index. -/
theorem valueByte_negative (t : types.ValueType) :
    64 ≤ (valueByte t).val ∧ (valueByte t).val < 128 := by
  cases t <;> decide

/-- Binary block grammar: singleton literal tags or nonnegative signed s33.
    In particular, a padded negative s33 is not an inline result type. -/
def BlockDecoded (data : Slice U8) (pos : Usize) (bt : signature.BlockType) (next : Usize) : Prop :=
  match bt with
  | .Empty => ∃ h : pos.val < data.length,
      data.val[pos.val] = 64#u8 ∧ next.val = pos.val + 1
  | .Value t => ∃ h : pos.val < data.length,
      data.val[pos.val] = valueByte t ∧ next.val = pos.val + 1
  | .TypeIndex index => SignedLeb33.Decoded data pos (index.val : Int) next

theorem BlockDecoded.span {data : Slice U8} {pos next : Usize} {bt : signature.BlockType}
    (h : BlockDecoded data pos bt next) : pos.val < next.val ∧ next.val ≤ data.length := by
  cases bt with
  | Empty => obtain ⟨hp, _, hn⟩ := h; omega
  | Value t => obtain ⟨hp, _, hn⟩ := h; omega
  | TypeIndex i =>
    have hs := SignedLeb33.Decoded.span data pos i.val next h
    exact ⟨hs.1, hs.2.2⟩

private theorem indexed_first_not_negative_tag (data : Slice U8) (pos : Usize)
    (index : U32) (next : Usize)
    (h : SignedLeb33.Decoded data pos (index.val : Int) next)
    (hp : pos.val < data.length) :
    ¬ (64 ≤ data.val[pos.val].val ∧ data.val[pos.val].val < 128) := by
  intro ⟨hlo, hhi⟩
  obtain ⟨bytes, hbytes, _, _, before, last, rfl, _, hbefore, _, hv, _⟩ := h
  have hh := congrArg List.head? hbytes
  cases before with
  | nil =>
    simp only [List.drop_eq_getElem_cons hp, List.nil_append, List.singleton_append,
      List.head?_cons, Option.some.injEq] at hh
    subst last
    simp [SignedLeb.finalValue, Leb128.payload, hlo] at hv
    omega
  | cons b bs =>
    simp only [List.drop_eq_getElem_cons hp, List.cons_append,
      List.head?_cons, Option.some.injEq] at hh
    have hb := hbefore b (by simp)
    rw [← hh] at hb
    omega

end Itasca.Wasm2

namespace Itasca

/-- Exact decoding on success, and ordinary return on every malformed input. -/
@[step]
theorem signature.read_block_type.spec (data : Slice U8) (pos : Usize) :
    signature.read_block_type data pos ⦃ r =>
      match r with
      | .Ok (bt, next) => Wasm2.BlockDecoded data pos bt next
      | .Err _ => True ⦄ := by
  by_cases hp : pos.val < data.length
  · obtain ⟨_, hr, next, rfl, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hp)
    rw [signature.read_block_type, hr]
    simp [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    split <;> try solve | simp_all [Wasm2.BlockDecoded, Wasm2.valueByte,
      U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]
    obtain ⟨r, hs, hd⟩ := WP.spec_imp_exists (reader.read_s33_leb.spec data pos)
    rw [hs]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨v, endpos⟩ := pair
      have hb := SignedLeb33.Decoded.range data pos v.val endpos hd
      simp [bind_ok]
      split
      · simp
      · step with IScalar.hcast_inBounds_spec .U32 v (by scalar_tac)
        simp only [Wasm2.BlockDecoded]
        convert (show SignedLeb33.Decoded data pos v.val endpos from hd) using 1
  · simp [signature.read_block_type, reader.read_byte.eof data pos (by omega),
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Every independent multi-value block encoding is accepted, including
    nonminimal nonnegative s33 indices. -/
theorem signature.read_block_type.complete (data : Slice U8) (pos : Usize)
    (bt : signature.BlockType) (next : Usize)
    (h : Wasm2.BlockDecoded data pos bt next) :
    signature.read_block_type data pos = .ok (.Ok (bt, next)) := by
  cases bt with
  | Empty =>
    obtain ⟨hp, hb, hn⟩ := h
    obtain ⟨_, hr, q, rfl, hq⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hp)
    have heq : q = next := by scalar_tac
    simp [signature.read_block_type, hr, hb, heq, core.result.Result.Insts.CoreOpsTry.branch]
  | Value t =>
    obtain ⟨hp, hb, hn⟩ := h
    obtain ⟨_, hr, q, rfl, hq⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hp)
    have heq : q = next := by scalar_tac
    cases t <;> simp [signature.read_block_type, hr, hb, heq, Wasm2.valueByte,
      core.result.Result.Insts.CoreOpsTry.branch]
  | TypeIndex index =>
    have hspan := SignedLeb33.Decoded.span data pos (index.val : Int) next h
    have hp : pos.val < data.length := by omega
    have htag := Wasm2.indexed_first_not_negative_tag data pos index next h hp
    obtain ⟨_, hr, q, rfl, _⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hp)
    obtain ⟨v, _, hv⟩ := WP.spec_imp_exists (UScalar.hcast_inBounds_spec .I64 index (by scalar_tac))
    have hd : SignedLeb33.Decoded data pos v.val next := by simpa only [hv, Wasm2.BlockDecoded] using h
    have hs := reader.read_s33_leb.complete data pos v next hd
    simp [signature.read_block_type, hr, core.result.Result.Insts.CoreOpsTry.branch]
    split <;> try (rename_i _ he; exact False.elim (htag (by rw [he]; decide)))
    obtain ⟨u, hu, huv⟩ := WP.spec_imp_exists (IScalar.hcast_inBounds_spec .U32 v (by scalar_tac))
    have hui : u = index := by scalar_tac
    simp [hs, hv, hu, hui]

end Itasca

namespace Itasca.Wasm2

/-- Independent block bytes determine both the signature and its end cursor,
    including reference/vector tags and nonminimal positive type indices. -/
theorem BlockDecoded.unique {data pos first second next last}
    (hfirst : BlockDecoded data pos first next)
    (hsecond : BlockDecoded data pos second last) :
    first = second ∧ next = last := by
  have h := (signature.read_block_type.complete data pos first next hfirst).symm.trans
    (signature.read_block_type.complete data pos second last hsecond)
  simpa using h

end Itasca.Wasm2

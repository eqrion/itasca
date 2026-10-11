import Itasca.Binary.SignedLeb33

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

def valueByte : types.ValueType → U8
  | .I32 => 127#u8
  | .I64 => 126#u8
  | .F32 => 125#u8
  | .F64 => 124#u8

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
    simp [SignedLeb33.finalValue, Leb128.payload, hlo] at hv
    omega
  | cons b bs =>
    simp only [List.drop_eq_getElem_cons hp, List.cons_append,
      List.head?_cons, Option.some.injEq] at hh
    have hb := hbefore b (by simp)
    rw [← hh] at hb
    omega

end Itasca.MultiValue

namespace Itasca

/-- Exact decoding on success, and ordinary return on every malformed input. -/
@[step]
theorem signature.read_block_type.spec (data : Slice U8) (pos : Usize) :
    signature.read_block_type data pos ⦃ r =>
      match r with
      | .Ok (bt, next) => MultiValue.BlockDecoded data pos bt next
      | .Err _ => True ⦄ := by
  by_cases hp : pos.val < data.length
  · obtain ⟨_, hr, next, rfl, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hp)
    rw [signature.read_block_type, hr]
    simp [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    split <;> try solve | simp_all [MultiValue.BlockDecoded, MultiValue.valueByte,
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
        simp only [MultiValue.BlockDecoded]
        convert (show SignedLeb33.Decoded data pos v.val endpos from hd) using 1
  · simp [signature.read_block_type, reader.read_byte.eof data pos (by omega),
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Every independent multi-value block encoding is accepted, including
    nonminimal nonnegative s33 indices. -/
theorem signature.read_block_type.complete (data : Slice U8) (pos : Usize)
    (bt : signature.BlockType) (next : Usize)
    (h : MultiValue.BlockDecoded data pos bt next) :
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
    cases t <;> simp [signature.read_block_type, hr, hb, heq, MultiValue.valueByte,
      core.result.Result.Insts.CoreOpsTry.branch]
  | TypeIndex index =>
    have hspan := SignedLeb33.Decoded.span data pos (index.val : Int) next h
    have hp : pos.val < data.length := by omega
    have htag := MultiValue.indexed_first_not_negative_tag data pos index next h hp
    obtain ⟨_, hr, q, rfl, _⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hp)
    obtain ⟨v, _, hv⟩ := WP.spec_imp_exists (UScalar.hcast_inBounds_spec .I64 index (by scalar_tac))
    have hd : SignedLeb33.Decoded data pos v.val next := by simpa only [hv, MultiValue.BlockDecoded] using h
    have hs := reader.read_s33_leb.complete data pos v next hd
    simp [signature.read_block_type, hr, core.result.Result.Insts.CoreOpsTry.branch]
    split <;> try (rename_i _ he; exact False.elim (htag (by rw [he]; decide)))
    obtain ⟨u, hu, huv⟩ := WP.spec_imp_exists (IScalar.hcast_inBounds_spec .U32 v (by scalar_tac))
    have hui : u = index := by scalar_tac
    simp [hs, hv, hu, hui]

end Itasca

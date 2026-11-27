import Itasca.Binary.Definitions
import Itasca.Results.Definitions.Binary
import Itasca.Support.Translation
import Itasca.Binary.LebReaders

open WebAssembly

/-!
Proofs for Binary / Body.

This module collects Syntax, BlockType.
Each section documents its contracts and consumers.
-/

/-! ## Syntax -/

section

/-!
# Wasm 2.0 instruction syntax

The instruction syntax: flat tokens (`Token`) whose block types are
`signature.BlockType` values, the relation `Emits` between tokens and the structured SpecTec
instructions they spell, and `BodyTokens` for a function body with its final `end`.
`Emits.well_formed` shows that the emitted instructions satisfy `wf_instr`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- A plain token spells a well-formed instruction. -/
theorem Simple.well_formed {token : Token} {op : instr} (h : Simple token op) :
    wf_instr op := by
  cases h with
  | plain _ hwf => exact hwf

/-- `Emits` is closed under concatenation. -/
theorem Emits.append {xs ys : List Token} {is js : List instr}
    (hx : Emits xs is) (hy : Emits ys js) : Emits (xs ++ ys) (is ++ js) := by
  induction hy with
  | nil => simpa using hx
  | simple _ hop ih => simpa [List.append_assoc] using WebAssembly.Binary.EmitsWith.simple (toSpec := Itasca.Body.blockType) ih hop
  | block bt _ hb ih _ => simpa [List.append_assoc] using WebAssembly.Binary.EmitsWith.block (toSpec := Itasca.Body.blockType) bt ih hb
  | loop bt _ hb ih _ => simpa [List.append_assoc] using WebAssembly.Binary.EmitsWith.loop (toSpec := Itasca.Body.blockType) bt ih hb
  | ifElse bt _ ht he ih _ _ =>
      simpa [List.append_assoc] using WebAssembly.Binary.EmitsWith.ifElse (toSpec := Itasca.Body.blockType) bt ih ht he
  | ifEnd bt _ hb ih _ => simpa [List.append_assoc] using WebAssembly.Binary.EmitsWith.ifEnd (toSpec := Itasca.Body.blockType) bt ih hb

/-- Emitted instructions are well formed. -/
theorem Emits.well_formed {tokens : List Token} {ops : List instr}
    (h : Emits tokens ops) : Forall wf_instr ops := by
  induction h with
  | nil => simp [Forall]
  | simple _ hs ih => simpa [Forall, or_imp, forall_and] using And.intro ih (Simple.well_formed hs)
  | block bt _ _ ih hb =>
      simpa [Forall, or_imp, forall_and] using And.intro ih (wf_instr.instr_case_4 _ _ (block_type_wf bt) hb)
  | loop bt _ _ ih hb =>
      simpa [Forall, or_imp, forall_and] using And.intro ih (wf_instr.instr_case_5 _ _ (block_type_wf bt) hb)
  | ifElse bt _ _ _ ih ht he =>
      simpa [Forall, or_imp, forall_and] using And.intro ih (wf_instr.instr_case_6 _ _ _ (block_type_wf bt) ht he)
  | ifEnd bt _ _ ih hb =>
      simpa [Forall, or_imp, forall_and] using And.intro ih (wf_instr.instr_case_6 _ _ [] (block_type_wf bt) hb (by simp [Forall]))

end Itasca.Body

end

/-! ## BlockType -/

section

/-!
# Wasm 2.0 block types

Block types as the extracted `signature.read_block_type` reads them. `Body.BlockDecoded` is the
byte-level grammar: the empty tag `0x40`, a value type tag, or a nonnegative signed 33-bit type
index. `signature.read_block_type.spec` and `.complete` show that the reader accepts exactly
these, and `BlockDecoded.unique` shows that the bytes determine the block type.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- Distinct value types have distinct bytes. -/
theorem value_byte_injective : Function.Injective Itasca.Binary.valueByte := by
  intro a b h
  cases a <;> cases b <;> first | rfl | contradiction

/-- Value type bytes are negative one-byte signed integers, so they cannot be confused with a
nonnegative type index. -/
theorem value_byte_negative (t : wasm_types.ValueType) :
    64 ≤ (Itasca.Binary.valueByte t).val ∧ (Itasca.Binary.valueByte t).val < 128 := by
  cases t <;> decide

/-- A block type read at a cursor: a literal tag byte or a nonnegative signed 33-bit index. A padded
negative index is not a value type. -/
def BlockDecoded (data : Slice U8) (pos : Usize) (bt : signature.BlockType) (next : Usize) : Prop :=
  match bt with
  | .Empty => ∃ h : pos.val < data.length,
      data.val[pos.val] = 64#u8 ∧ next.val = pos.val + 1
  | .Value t => ∃ h : pos.val < data.length,
      data.val[pos.val] = Itasca.Binary.valueByte t ∧ next.val = pos.val + 1
  | .TypeIndex index => Binary.SignedLeb33.Decoded data pos (index.val : Int) next

/-- A decoded block type is nonempty and within the input. -/
theorem BlockDecoded.span {data : Slice U8} {pos next : Usize} {bt : signature.BlockType}
    (h : BlockDecoded data pos bt next) : pos.val < next.val ∧ next.val ≤ data.length := by
  cases bt with
  | Empty => obtain ⟨hp, _, hn⟩ := h; omega
  | Value t => obtain ⟨hp, _, hn⟩ := h; omega
  | TypeIndex i =>
    have hs := Binary.SignedLeb33.Decoded.span data pos i.val next h
    exact ⟨hs.1, hs.2.2⟩

private theorem indexed_first_not_negative_tag (data : Slice U8) (pos : Usize)
    (index : U32) (next : Usize)
    (h : Binary.SignedLeb33.Decoded data pos (index.val : Int) next)
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
    simp [Binary.SignedLeb.finalValue, Binary.Leb128.payload_nil, Binary.Leb128.payload_cons, hlo] at hv
    omega
  | cons b bs =>
    simp only [List.drop_eq_getElem_cons hp, List.cons_append,
      List.head?_cons, Option.some.injEq] at hh
    have hb := hbefore b (by simp)
    rw [← hh] at hb
    omega

end Itasca.Body

namespace Itasca

/-- `signature.read_block_type` decodes exactly `BlockDecoded` on success and never panics. -/
@[step]
theorem signature.read_block_type.spec (data : Slice U8) (pos : Usize) :
    signature.read_block_type data pos ⦃ r =>
      match r with
      | .Ok (bt, next) => Body.BlockDecoded data pos bt next
      | .Err _ => True ⦄ := by
  by_cases hp : pos.val < data.length
  · obtain ⟨_, hr, next, rfl, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hp)
    rw [signature.read_block_type, hr]
    simp [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    split <;> try solve | simp_all [Body.BlockDecoded, Itasca.Binary.valueByte, Itasca.Binary.Source.valueType, WebAssembly.Binary.valueByte, Itasca.Binary.Source.readerByte,
      U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]
    obtain ⟨r, hs, hd⟩ := WP.spec_imp_exists (reader.read_s33_leb.spec data pos)
    rw [hs]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨v, endpos⟩ := pair
      have hb := Binary.SignedLeb33.Decoded.range data pos v.val endpos hd
      simp [bind_ok]
      split
      · simp
      · step with IScalar.hcast_inBounds_spec .U32 v (by scalar_tac)
        simp only [Body.BlockDecoded]
        convert (show Binary.SignedLeb33.Decoded data pos v.val endpos from hd) using 1
  · simp [signature.read_block_type, reader.read_byte.eof data pos (by omega),
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Every `BlockDecoded` block type is accepted by `signature.read_block_type`, including
non-minimal nonnegative indices. -/
theorem signature.read_block_type.complete (data : Slice U8) (pos : Usize)
    (bt : signature.BlockType) (next : Usize)
    (h : Body.BlockDecoded data pos bt next) :
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
    cases t <;> simp [signature.read_block_type, hr, hb, heq, Itasca.Binary.valueByte, Itasca.Binary.Source.valueType, WebAssembly.Binary.valueByte, Itasca.Binary.Source.readerByte,
      core.result.Result.Insts.CoreOpsTry.branch]
  | TypeIndex index =>
    have hspan := Binary.SignedLeb33.Decoded.span data pos (index.val : Int) next h
    have hp : pos.val < data.length := by omega
    have htag := Body.indexed_first_not_negative_tag data pos index next h hp
    obtain ⟨_, hr, q, rfl, _⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hp)
    obtain ⟨v, _, hv⟩ := WP.spec_imp_exists (UScalar.hcast_inBounds_spec .I64 index (by scalar_tac))
    have hd : Binary.SignedLeb33.Decoded data pos v.val next := by simpa only [hv, Body.BlockDecoded] using h
    have hs := reader.read_s33_leb.complete data pos v next hd
    simp [signature.read_block_type, hr, core.result.Result.Insts.CoreOpsTry.branch]
    split <;> try (rename_i _ he; exact False.elim (htag (by rw [he]; decide)))
    obtain ⟨u, hu, huv⟩ := WP.spec_imp_exists (IScalar.hcast_inBounds_spec .U32 v (by scalar_tac))
    have hui : u = index := by scalar_tac
    simp [hs, hv, hu, hui]

end Itasca

namespace Itasca.Body

/-- Block bytes determine both the block type and the end cursor. -/
theorem BlockDecoded.unique {data pos first second next last}
    (hfirst : BlockDecoded data pos first next)
    (hsecond : BlockDecoded data pos second last) :
    first = second ∧ next = last := by
  have h := (signature.read_block_type.complete data pos first next hfirst).symm.trans
    (signature.read_block_type.complete data pos second last hsecond)
  simpa using h

end Itasca.Body

end

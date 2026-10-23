import Itasca.Binary.Wasm2.Encoding

/-!
# Wasm 1.0 tokens inside the Wasm 2.0 grammar

The Wasm 1.0 grammar is the Wasm 2.0 grammar without the extension opcodes, with one-byte block
types and with a literal zero table byte in `call_indirect`. `Immediate.of_wasm2` and
`At.of_wasm2` recover a Wasm 1.0 token from a Wasm 2.0 one under the first two restrictions, and
`At.call_indirect` builds the `call_indirect` token from its decoded index and zero byte.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

/-- The opcodes the Wasm 2.0 extensions add to the single-byte opcode space. -/
def extensionOpcodes : List Nat :=
  [0x1c, 0x25, 0x26, 0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xd0, 0xd1, 0xd2, 0xfc, 0xfd]

/-- The block type of a structured instruction header has a one-byte Wasm 1.0 spelling. -/
def BlockTokenOk : Token → Prop
  | .block bt | .loop bt | .if_ bt => ∃ b, ScalarBlockByte bt b
  | _ => True

theorem ScalarBlockByte.encoding {bt b bytes} (h : ScalarBlockByte bt b)
    (he : Wasm2.BlockEncoding bt bytes) : bytes = [b] := by
  cases h <;> simpa [Wasm2.BlockEncoding, Wasm2.valueByte] using he

theorem signMeaning_extension {opcode : U8} {op : Numeric.Operation}
    (h : Wasm2.NumericExtensions.signMeaning opcode = some op) : opcode.val ∈ extensionOpcodes := by
  unfold Wasm2.NumericExtensions.signMeaning at h
  split at h <;> simp_all [extensionOpcodes]

private theorem reference_extension {opcode : U8} {op : instr} {bytes : List U8}
    (h : Wasm2.ReferencesBinary.Immediate opcode op bytes) (hindirect : opcode ≠ 0x11#u8) :
    opcode.val ∈ extensionOpcodes := by
  cases h <;> first | exact absurd rfl hindirect | decide

/-- A Wasm 2.0 immediate outside the extension opcodes and `call_indirect`, with a one-byte block
type, is a Wasm 1.0 immediate. -/
theorem Immediate.of_wasm2 {opcode : U8} {token : Token} {bytes : List U8}
    (h : Wasm2.Immediate opcode token bytes) (hop : opcode.val ∉ extensionOpcodes)
    (hindirect : opcode ≠ 0x11#u8) (hblock : BlockTokenOk token) :
    Immediate opcode token bytes := by
  cases h with
  | plain h => exact h
  | signExtension _ _ hm => exact absurd (signMeaning_extension hm) hop
  | saturating => exact absurd (by decide) hop
  | reference h => exact absurd (reference_extension h hindirect) hop
  | bulk => exact absurd (by decide) hop
  | simd => exact absurd (by decide) hop
  | block he =>
    obtain ⟨b, hb⟩ := hblock
    rw [hb.encoding he]
    exact .block hb
  | loop he =>
    obtain ⟨b, hb⟩ := hblock
    rw [hb.encoding he]
    exact .loop hb
  | if_ he =>
    obtain ⟨b, hb⟩ := hblock
    rw [hb.encoding he]
    exact .if_ hb
  | else_ => exact .else_
  | end_ => exact .end_

/-- A Wasm 2.0 token outside the extension opcodes and `call_indirect`, with a one-byte block
type, is a Wasm 1.0 token. -/
theorem At.of_wasm2 {data start token next} (h : Wasm2.At data start token next)
    (hp : start.val < data.length) (hop : (data.val[start.val]'hp).val ∉ extensionOpcodes)
    (hindirect : data.val[start.val]'hp ≠ 0x11#u8) (hblock : BlockTokenOk token) :
    At data start token next := by
  obtain ⟨_, ⟨opcode, imm, rfl, hi⟩, hs⟩ := h
  have hb := hs.suffix
  rw [List.drop_eq_getElem_cons hp] at hb
  have he : data.val[start.val] = opcode := (List.cons.inj hb).1
  subst he
  exact ⟨_, ⟨_, imm, rfl, Immediate.of_wasm2 hi hop hindirect hblock⟩, hs⟩

/-- An unsigned LEB128 encoding that starts with a zero byte is that byte alone. -/
theorem _root_.Itasca.Leb128.Encoding.zero_head {rest : List U8} {value : Nat}
    (h : Leb128.Encoding (0#u8 :: rest) value) : rest = [] ∧ value = 0 := by
  obtain ⟨before, last, he, _, hhigh, _, _, hv⟩ := h
  cases before with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp [hv, Leb128.payload]
  | cons b before =>
    simp only [List.cons_append, List.cons.injEq] at he
    have := hhigh b (by simp)
    rw [← he.1] at this
    simp at this

/-- `call_indirect` with a decoded type index followed by a zero table byte is a Wasm 1.0 token. -/
theorem At.call_indirect {data start pos middle next} (idx table : U32)
    (hp : start.val < data.length) (hbyte : data.val[start.val] = 0x11#u8)
    (hpos : pos.val = start.val + 1) (hd : Leb128.Decoded data pos idx middle)
    (hm : middle.val < data.length) (hzero : data.val[middle.val] = 0#u8)
    (htable : Leb128.Decoded data middle table next) :
    table = 0#u32 ∧ At data start (.plain (.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val))) next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hd
  obtain ⟨tbytes, ts, tl, tb, te⟩ := htable
  cases tbytes with
  | nil =>
    obtain ⟨before, last, he, _⟩ := te
    simp at he
  | cons b rest =>
    have ts' := ts
    rw [List.drop_eq_getElem_cons hm, hzero, List.cons_append] at ts'
    obtain ⟨rfl, -⟩ := List.cons.inj ts'
    obtain ⟨rfl, hv⟩ := te.zero_head
    have ht : table = 0#u32 := UScalar.eq_of_val_eq (by simpa using hv)
    subst ht
    refine ⟨rfl, .of_immediate hp hbyte hpos (.callIndirect idx he) ?_⟩
    exact (show BytesAt data pos bytes middle from ⟨hs, hl, by omega⟩).append ⟨ts, tl, tb⟩

end Itasca.Wasm1

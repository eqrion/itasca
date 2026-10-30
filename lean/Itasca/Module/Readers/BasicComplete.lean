import Itasca.Module.Readers.Types
import Itasca.Binary.Wasm1.EncodingComplete

/-!
# Completeness of the primitive readers

Inversion lemmas for `At` over index, byte, repetition and vector encodings, and acceptance
(`.complete`) of `metadata.decode_value_type` and `metadata.decode_elem_type` from independent
encodings that the profile allows. The matching soundness specs are in `Module/Readers/Basic`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- An `IndexEncoding` span is a decoded `u32`. -/
theorem At.index_decoded {data pos idx next} (h : At IndexEncoding data pos idx next) :
    Leb128.Decoded data pos idx next := by
  obtain ⟨bytes, he, hs⟩ := h
  exact hs.u32_decoded idx he

/-- `reader.read_u32_leb` reads an `IndexEncoding` span. -/
theorem At.read_index {data pos idx next} (h : At IndexEncoding data pos idx next) :
    reader.read_u32_leb data pos = .ok (.Ok (idx, next)) :=
  reader.read_u32_leb.complete data pos idx next h.index_decoded

/-- `reader.read_byte` reads a `ByteEncoding` span. -/
theorem At.read_byte {data pos byte next} (h : At ByteEncoding data pos byte next) :
    reader.read_byte data pos = .ok (.Ok (byte, next)) := h.byte.read_byte

/-- An empty repetition consumes nothing. -/
theorem At.rep_nil {α : Type} {R : α → List U8 → Prop} {data pos next}
    (h : At (Rep R) data pos [] next) : next = pos := by
  obtain ⟨bytes, he, hs⟩ := h
  cases he
  exact hs.empty

/-- A nonempty repetition splits into its first element and the rest. -/
theorem At.rep_cons {α : Type} {R : α → List U8 → Prop} {data pos value values next}
    (h : At (Rep R) data pos (value :: values) next) :
    ∃ middle, At R data pos value middle ∧ At (Rep R) data middle values next := by
  obtain ⟨bytes, he, hs⟩ := h
  cases he with
  | cons hfirst hrest =>
      obtain ⟨middle, hf, ht⟩ := hs.split
      exact ⟨middle, ⟨_, hfirst, hf⟩, ⟨_, hrest, ht⟩⟩

/-- A vector encoding splits into a decoded `u32` count equal to the length and the repeated
elements. The count's LEB encoding fits in a `u32`, and nonminimal encodings are admitted. -/
theorem At.vector_split {α : Type} {R : α → List U8 → Prop} {data pos values next}
    (h : At (VecEncoding R) data pos values next) :
    ∃ count middle, count.val = values.length ∧ Leb128.Decoded data pos count middle ∧
      At (Rep R) data middle values next := by
  obtain ⟨bytes, ⟨countBytes, entries, hc, he, rfl⟩, hs⟩ := h
  let count : U32 := U32.ofNatCore values.length (by have := hc.value_lt; scalar_tac)
  have hcount : count.val = values.length := by simp [count]
  obtain ⟨middle, hf, ht⟩ := hs.split
  exact ⟨count, middle, hcount, hf.u32_decoded count (by simpa [hcount] using hc), ⟨entries, he, ht⟩⟩

end Itasca.ModuleBinary

namespace Itasca

open ModuleBinary

/-- `metadata.decode_value_type` accepts an independently encoded value type that the profile
allows. -/
theorem metadata.decode_value_type.complete (data : Slice U8) (pos : Usize)
    (ty : wasm_types.ValueType) (next : Usize) (h : At ValueTypeEncoding data pos ty next)
    (profile : ValidationProfile) (hallowed : ValueTypeAllowed profile ty) :
    metadata.decode_value_type data pos profile = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, rfl, hs⟩ := h
  have hr := hs.read_byte
  cases profile <;> cases ty <;>
    simp_all [metadata.decode_value_type, valueByte, ValueTypeAllowed,
      core.result.Result.Insts.CoreOpsTry.branch]

/-- `metadata.decode_elem_type` accepts an independently encoded element type that the profile
allows. -/
theorem metadata.decode_elem_type.complete (data : Slice U8) (pos : Usize)
    (ty : wasm_types.ElemType) (next : Usize) (h : At ElemTypeEncoding data pos ty next)
    (profile : ValidationProfile) (hallowed : ElemTypeAllowed profile ty) :
    metadata.decode_elem_type data pos profile = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, rfl, hs⟩ := h
  have hr := hs.read_byte
  cases profile <;> cases ty <;>
    simp_all [metadata.decode_elem_type, elemByte, ElemTypeAllowed,
      core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

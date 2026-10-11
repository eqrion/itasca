import Itasca.Module.ModuleTypes
import Itasca.Binary.WasmBinaryComplete

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

theorem At.index_decoded {data pos idx next} (h : At IndexEncoding data pos idx next) :
    Leb128.Decoded data pos idx next := by
  obtain ⟨bytes, he, hs⟩ := h
  exact hs.u32_decoded idx he

theorem At.read_index {data pos idx next} (h : At IndexEncoding data pos idx next) :
    reader.read_u32_leb data pos = .ok (.Ok (idx, next)) :=
  reader.read_u32_leb.complete data pos idx next h.index_decoded

theorem At.read_byte {data pos byte next} (h : At ByteEncoding data pos byte next) :
    reader.read_byte data pos = .ok (.Ok (byte, next)) := h.byte.read_byte

theorem At.rep_nil {α : Type} {R : α → List U8 → Prop} {data pos next}
    (h : At (Rep R) data pos [] next) : next = pos := by
  obtain ⟨bytes, he, hs⟩ := h
  cases he
  exact hs.empty

theorem At.rep_cons {α : Type} {R : α → List U8 → Prop} {data pos value values next}
    (h : At (Rep R) data pos (value :: values) next) :
    ∃ middle, At R data pos value middle ∧ At (Rep R) data middle values next := by
  obtain ⟨bytes, he, hs⟩ := h
  cases he with
  | cons hfirst hrest =>
      obtain ⟨middle, hf, ht⟩ := hs.split
      exact ⟨middle, ⟨_, hfirst, hf⟩, ⟨_, hrest, ht⟩⟩

/-- A vector count is bounded by its own LEB encoding and therefore has an
actual U32 representation. Nonminimal encodings remain admitted. -/
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

theorem module.decode_value_type.complete (data : Slice U8) (pos : Usize)
    (ty : types.ValueType) (next : Usize) (h : At ValueTypeEncoding data pos ty next)
    (profile : ValidationProfile) (hallowed : ValueTypeAllowed profile ty) :
    module.decode_value_type data pos profile = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, rfl, hs⟩ := h
  have hr := hs.read_byte
  cases profile <;> cases ty <;>
    simp_all [module.decode_value_type, hr, valueByte, ValueTypeAllowed,
      core.result.Result.Insts.CoreOpsTry.branch]

theorem module.decode_elem_type.complete (data : Slice U8) (pos : Usize)
    (ty : types.ElemType) (next : Usize) (h : At ElemTypeEncoding data pos ty next)
    (profile : ValidationProfile) (hallowed : ElemTypeAllowed profile ty) :
    module.decode_elem_type data pos profile = .ok (.Ok (ty, next)) := by
  obtain ⟨bytes, rfl, hs⟩ := h
  have hr := hs.read_byte
  cases profile <;> cases ty <;>
    simp_all [module.decode_elem_type, hr, elemByte, ElemTypeAllowed,
      core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

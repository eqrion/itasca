import Itasca.Binary.InstructionSource
import Itasca.Binary.ReaderIndex

namespace Itasca.Binary.Source
open Aeneas.Std WebAssembly

theorem readerS32 {bs n} (h : WebAssembly.Binary.Leb128.S32Encoding bs n) :
    ∃ i : I32, i.val = n ∧ SignedLeb32.Encoding (readerBytes bs) i.val := by
  have e := (SignedLeb32.encoding_iff (readerBytes bs) n).mpr (by simpa only [bytes_readerBytes] using h)
  obtain ⟨_, _, _, _, _, _, _, lo, hi⟩ := h
  let i := I32.ofInt n ⟨lo, hi⟩
  have eq : i.val = n := by simp [i]
  exact ⟨i, eq, eq.symm ▸ e⟩

theorem readerS64 {bs n} (h : WebAssembly.Binary.Leb128.S64Encoding bs n) :
    ∃ i : I64, i.val = n ∧ SignedLeb64.Encoding (readerBytes bs) i.val := by
  have e := (SignedLeb64.encoding_iff (readerBytes bs) n).mpr (by simpa only [bytes_readerBytes] using h)
  obtain ⟨_, _, _, _, _, _, _, lo, hi⟩ := h
  let i := I64.ofInt n ⟨lo, hi⟩
  have eq : i.val = n := by simp [i]
  exact ⟨i, eq, eq.symm ▸ e⟩

theorem readerFloat32 {bs n} (h : WebAssembly.Binary.FloatBits.Encoding 4 bs n) :
    ∃ i : U32, i.val = n ∧ FloatBits.Encoding 4 (readerBytes bs) i.val := by
  have e : FloatBits.Encoding 4 (readerBytes bs) n := floatBits.mpr (by simpa only [bytes_readerBytes] using h)
  have bound := FloatBits.payload_lt (readerBytes bs)
  rw [← e.2, e.1] at bound
  exact ⟨U32.ofNatCore n bound, rfl, e⟩

theorem readerFloat64 {bs n} (h : WebAssembly.Binary.FloatBits.Encoding 8 bs n) :
    ∃ i : U64, i.val = n ∧ FloatBits.Encoding 8 (readerBytes bs) i.val := by
  have e : FloatBits.Encoding 8 (readerBytes bs) n := floatBits.mpr (by simpa only [bytes_readerBytes] using h)
  have bound := FloatBits.payload_lt (readerBytes bs)
  rw [← e.2, e.1] at bound
  exact ⟨U64.ofNatCore n bound, rfl, e⟩

abbrev readerType := Body.MemoryMeaning.readerType

@[simp] theorem valueType_readerType (t) : valueType (readerType t) = t := by cases t <;> rfl

@[simp] theorem readerValueByte (t) : readerByte (WebAssembly.Binary.valueByte t) =
    Itasca.Binary.valueByte (readerType t) := by cases t <;> rfl

def readerRef : reftype → wasm_types.ElemType
  | .FUNCREF => .FuncRef
  | .EXTERNREF => .ExternRef

@[simp] theorem referenceType_readerRef (t) : Translation.referenceType (readerRef t) = t := by
  cases t <;> rfl

@[simp] theorem readerRefByte (t) : readerByte (WebAssembly.Binary.ReferencesBinary.referenceByte t) =
    Body.ReferencesBinary.referenceByte (readerRef t) := by cases t <;> rfl

theorem readConstant {e bs} (h : WebAssembly.Binary.ConstEncoding e bs) :
    ∃ c, constant c = e ∧ ConstEncoding c (readerBytes bs) := by
  suffices ∃ c, constant c = e by
    obtain ⟨c, rfl⟩ := this
    exact ⟨c, rfl, by simpa only [ConstEncoding, bytes_readerBytes] using h⟩
  cases h with
  | i32 _ h =>
    obtain ⟨v, rfl, _⟩ := readerS32 h
    exact ⟨.I32 v, rfl⟩
  | i64 _ h =>
    obtain ⟨v, rfl, _⟩ := readerS64 h
    exact ⟨.I64 v, rfl⟩
  | f32 _ h =>
    obtain ⟨v, rfl, _⟩ := readerFloat32 h
    exact ⟨.F32 v, rfl⟩
  | f64 _ h =>
    obtain ⟨v, rfl, _⟩ := readerFloat64 h
    exact ⟨.F64 v, rfl⟩
  | globalGet _ h =>
    obtain ⟨v, rfl, _⟩ := readerIndex h
    exact ⟨.GlobalGet v, rfl⟩
  | refFunc _ h =>
    obtain ⟨v, rfl, _⟩ := readerIndex h
    exact ⟨.RefFunc v, rfl⟩
  | refNull t => exact ⟨.RefNull (readerRef t), by cases t <;> rfl⟩
  | v128 _ _ _ lh hh =>
    obtain ⟨l, rfl, _⟩ := readerFloat64 lh
    obtain ⟨r, rfl, _⟩ := readerFloat64 hh
    exact ⟨.V128 l r, rfl⟩

end Itasca.Binary.Source

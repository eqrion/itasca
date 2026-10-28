import Exec.Interp.Memory.MemoryValueSlots
import Exec.Interp.Relations.Readback
namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

theorem numeric_input_word (words : List U64) (position : Nat) (ty : numtype) (value : num_)
    (wellFormed : wf_num_ ty value)
    (represented : WordsAt words position (Code.encodeValue (.CONST ty value))) :
    ∃ word, words[position]? = some word ∧ numericStoreValue ty word = value := by
  have lengthEq : (Code.encodeValue (.CONST ty value)).length = 1 := by
    rw [Code.encodeValue_length]
    cases ty <;> rfl
  obtain ⟨bits,encoded⟩ := List.length_eq_one_iff.mp lengthEq
  rw [encoded] at represented
  obtain ⟨bound,atWord⟩ := represented 0 (by simp)
  simp only [Nat.add_zero,List.getElem!_cons_zero] at bound atWord
  let word := words[position]
  have wordBits : word.val = bits := by simpa only [_root_.getElem!_pos words position bound] using atWord
  have pair : pairWords (numericMemoryType ty) (word,0#u64) = Code.encodeValue (.CONST ty value) := by
    rw [encoded,←wordBits]
    cases ty <;> rfl
  have floatBound : numericMemoryType ty = .F32 → word.val < 2^32 := by
    intro floating
    have sourceType : Code.valueType (.CONST ty value) = .F32 := by
      cases ty <;> simp_all [numericMemoryType,Code.valueType,valtype_numtype,numtype_Inn,numtype_Fnn]
    have bounded := encodeValue_f32_low (.CONST ty value) (.val_case_0 ty value wellFormed) sourceType
    simpa only [encoded,List.getElem!_cons_zero,wordBits] using bounded
  have roundtrip := Code.decode_encode (.CONST ty value) (.val_case_0 ty value wellFormed) []
  simp only [List.append_nil] at roundtrip
  have translated : sourceType (numericMemoryType ty) = Code.valueType (.CONST ty value) := by cases ty <;> rfl
  rw [←translated,←pair,decode_words_code _ _ _ floatBound] at roundtrip
  have decoded := congrArg Prod.fst (Option.some.inj roundtrip)
  rw [numericStoreValue_decodes] at decoded
  exact ⟨word,List.getElem?_eq_getElem bound,(val.CONST.inj decoded).2⟩
end Itasca.Runtime.Interp.MemoryDescriptor

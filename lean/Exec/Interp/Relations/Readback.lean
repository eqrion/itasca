import Exec.Interp.Relations.DecodeValue
import Exec.Interp.Relations.Regions

/-! Recover specification values from represented live result slots. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def readPair (words : List U64) (position : Nat) (ty : Itasca.types.ValueType) : U64 × U64 :=
  (words[position]!, if sourceType ty = .V128 then words[position + 1]! else 0#u64)

theorem WordsAt.readPair {words : List U64} {position : Nat} {bits : List Nat}
    (ty : Itasca.types.ValueType) (represented : WordsAt words position bits)
    (length : bits.length = Code.width (sourceType ty)) :
    pairWords ty (readPair words position ty) = bits := by
  by_cases hv : sourceType ty = .V128
  · have hl : bits.length = 2 := by simpa [hv, Code.width] using length
    apply List.ext_getElem
    · simp [pairWords, hv, hl]
    · intro i hi hb
      have hm : i = 0 ∨ i = 1 := by omega
      rcases hm with rfl | rfl
      · have h := (represented 0 hb).2
        simpa [pairWords, Itasca.Runtime.Interp.readPair, hv, _root_.getElem!_pos bits 0 hb] using h
      · have h := (represented 1 hb).2
        simpa [pairWords, Itasca.Runtime.Interp.readPair, hv, _root_.getElem!_pos bits 1 hb] using h
  · have hw : Code.width (sourceType ty) = 1 := by cases ty <;> simp_all [sourceType, Code.width]
    have hl : bits.length = 1 := length.trans hw
    apply List.ext_getElem
    · simp [pairWords, hv, hl]
    · intro i hi hb
      have hz : i = 0 := by omega
      subst i
      have h := (represented 0 hb).2
      simpa [pairWords, Itasca.Runtime.Interp.readPair, hv, _root_.getElem!_pos bits 0 hb] using h

theorem encodeValue_f32_low (value : val) (wellFormed : wf_val value)
    (typed : Code.valueType value = .F32) : (Code.encodeValue value)[0]! < 2^32 := by
  cases wellFormed with
  | val_case_0 ty value hv =>
    cases hv with
    | num__case_0 kind bits _ hb hty =>
      subst ty
      cases kind <;> simp [Code.valueType, valtype_numtype, numtype_Inn, numtype_Fnn] at typed
    | num__case_1 kind value hv hty =>
      subst ty
      cases kind with
      | F32 =>
        change SpecExt.Builtins.floatBits 32 value < 2^32
        exact SpecExt.Builtins.Float.floatBits_lt_32 value hv
      | F64 => simp [Code.valueType, valtype_numtype, numtype_Inn, numtype_Fnn] at typed
  | val_case_1 ty value _ _ => simp [Code.valueType] at typed
  | val_case_2 ty => cases ty <;> simp [Code.valueType] at typed
  | val_case_3 address => simp [Code.valueType] at typed
  | val_case_4 address => simp [Code.valueType] at typed

/-- Reference words fit usize before the decoder subtracts the null sentinel.
The store's issued-address bounds establish this condition for live results. -/
def ResultIndexFits : val → Prop
  | .REF_FUNC_ADDR address | .REF_HOST_ADDR address => address + 1 ≤ Usize.max
  | _ => True

theorem encodeValue_reference_low (value : val) (fits : ResultIndexFits value)
    (typed : Code.valueType value = .FUNCREF ∨ Code.valueType value = .EXTERNREF) :
    (Code.encodeValue value)[0]! ≤ Usize.max := by
  cases value with
  | CONST ty n => cases ty <;> simp [Code.valueType, valtype_numtype, numtype_Inn, numtype_Fnn] at typed
  | VCONST ty n => simp [Code.valueType] at typed
  | REF_NULL ty => simp [Code.encodeValue]
  | REF_FUNC_ADDR address | REF_HOST_ADDR address => simpa [Code.encodeValue, ResultIndexFits] using fits

@[step] theorem decode_slot_represents (slots : Slice U64) (position : Usize)
    (ty : Itasca.types.ValueType) (store : Usize) (value : val)
    (wellFormed : wf_val value) (typed : sourceType ty = Code.valueType value)
    (represented : WordsAt slots.val position.val (Code.encodeValue value))
    (bound : position.val + Code.width (sourceType ty) ≤ slots.length)
    (floatBound : ty = .F32 → slots.val[position.val]!.val < 2^32)
    (referenceBound : ty = .FuncRef ∨ ty = .ExternRef → slots.val[position.val]!.val ≤ Usize.max) :
    runtime.interp.decode_slot slots position ty store ⦃ result =>
      rawType result = ty ∧ sourceValue result = value ⦄ := by
  let pair := readPair slots.val position.val ty
  have hp : pairWords ty pair = Code.encodeValue value :=
    represented.readPair ty (by rw [Code.encodeValue_length, ← typed])
  obtain ⟨result, hd, hty, hv⟩ := WP.spec_imp_exists
    (decode_value_represents ty pair.1 pair.2 store value wellFormed typed hp floatBound referenceBound)
  step with decode_slot_spec slots position ty store pair.1 pair.2 result bound rfl (by simp only [pair, Itasca.Runtime.Interp.readPair]; split <;> simp_all) hd
    as ⟨actual, ha⟩
  simpa [ha] using And.intro hty hv

/-- The live-value representation supplies the decoder's numeric bounds;
only the independent issued-address bound remains explicit. -/
@[step] theorem decode_slot_value (slots : Slice U64) (position : Usize)
    (ty : Itasca.types.ValueType) (store : Usize) (value : val)
    (wellFormed : wf_val value) (typed : sourceType ty = Code.valueType value)
    (represented : WordsAt slots.val position.val (Code.encodeValue value))
    (fits : ResultIndexFits value) :
    runtime.interp.decode_slot slots position ty store ⦃ result =>
      rawType result = ty ∧ sourceValue result = value ⦄ := by
  have length : (Code.encodeValue value).length = Code.width (sourceType ty) := by
    rw [Code.encodeValue_length, ← typed]
  have positive := Code.width_positive (sourceType ty)
  have first : slots.val[position.val]!.val = (Code.encodeValue value)[0]! := by
    simpa using (represented 0 (by omega)).2
  have bound : position.val + Code.width (sourceType ty) ≤ slots.length := by
    have last := (represented ((Code.encodeValue value).length - 1) (by omega)).1
    change position.val + Code.width (sourceType ty) ≤ slots.val.length
    omega
  apply decode_slot_represents slots position ty store value wellFormed typed represented bound
  · intro ht
    rw [first]
    apply encodeValue_f32_low value wellFormed
    simpa [ht, sourceType] using typed.symm
  · intro ht
    rw [first]
    apply encodeValue_reference_low value fits
    rcases ht with rfl | rfl
    · exact Or.inl typed.symm
    · exact Or.inr typed.symm

end Itasca.Runtime.Interp


import Exec.Interp.Relations.DecodeValue
import Exec.Interp.Relations.Regions

/-! Recover specification values from represented live result slots. -/
namespace Exec.Interp
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
        simpa [pairWords, Exec.Interp.readPair, hv, _root_.getElem!_pos bits 0 hb] using h
      · have h := (represented 1 hb).2
        simpa [pairWords, Exec.Interp.readPair, hv, _root_.getElem!_pos bits 1 hb] using h
  · have hw : Code.width (sourceType ty) = 1 := by cases ty <;> simp_all [sourceType, Code.width]
    have hl : bits.length = 1 := length.trans hw
    apply List.ext_getElem
    · simp [pairWords, hv, hl]
    · intro i hi hb
      have hz : i = 0 := by omega
      subst i
      have h := (represented 0 hb).2
      simpa [pairWords, Exec.Interp.readPair, hv, _root_.getElem!_pos bits 0 hb] using h

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
  step with decode_slot_spec slots position ty store pair.1 pair.2 result bound rfl (by simp only [pair, Exec.Interp.readPair]; split <;> simp_all) hd
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


@[step] theorem read_results_loop {M : Type} (words : alloc.vec.Vec U64)
    (store : runtime.store.Store M) (results : alloc.vec.Vec runtime.Value)
    (index slot : Usize) (types : alloc.vec.Vec Itasca.types.ValueType) (values : List val)
    (typed : types.val.map sourceType = values.map Code.valueType)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt words.val 0 values)
    (bound : index.val ≤ values.length)
    (position : slot.val = Code.offset (values.map Code.valueType) index.val)
    (prior : results.val.map sourceValue = values.take index.val) :
    runtime.interp.invoke_with_loop2 words store results index slot types ⦃ (afterStore, after) =>
      afterStore = store ∧ after.val.map sourceValue = values ⦄ := by
  have lengths : types.length = values.length := by
    have h := congrArg List.length typed
    simpa using h
  unfold runtime.interp.invoke_with_loop2
  apply loop.spec_decr_nat (fun p => values.length - p.2.1.val)
    (fun p => p.2.1.val ≤ values.length ∧
      p.2.2.val = Code.offset (values.map Code.valueType) p.2.1.val ∧
      p.1.val.map sourceValue = values.take p.2.1.val)
  · rintro ⟨current, i, offset⟩ ⟨hi, hoffset, hprior⟩
    dsimp only at hi hoffset hprior
    unfold runtime.interp.invoke_with_loop2.body
    dsimp only
    split
    · have hib : i.val < values.length := by scalar_tac
      have hit : i.val < types.val.length := by change i.val < types.length; omega
      let value := values[i.val]
      have hlookup : values[i.val]? = some value := by simp [value, List.getElem?_eq_getElem hib]
      have member : value ∈ values := List.getElem_mem hib
      step as ⟨ty, hty⟩
      have htype : sourceType ty = Code.valueType value := by
        have h := congrArg (fun xs => xs[i.val]?) typed
        simpa [List.getElem?_eq_getElem hit, hlookup, ← hty] using h
      have hrep : WordsAt (alloc.vec.Vec.deref words).val offset.val (Code.encodeValue value) := by
        have h := represented.lookup hlookup
        simpa [alloc.vec.Vec.deref, hoffset] using h
      step with decode_slot_value (alloc.vec.Vec.deref words) offset ty store.id value
        (wellFormed value member) htype hrep (fits value member)
        as ⟨decoded, hraw, hdecoded⟩
      have hcurrent : current.length = i.val := by
        have h := congrArg List.length hprior
        simpa [List.length_take, Nat.min_eq_left hi] using h
      step as ⟨after, hafter⟩
      step with width_spec ty as ⟨width, hwidth⟩
      have hnextOffset : Code.offset (values.map Code.valueType) (i.val + 1) =
          offset.val + Code.width (sourceType ty) := by
        rw [hoffset]
        simp [Code.offset, List.take_add_one, hlookup, Code.slots_append, Code.slots, ← htype]
      have hcapacity : offset.val + Code.width (sourceType ty) ≤ words.length := by
        have hpositive := Code.width_positive (sourceType ty)
        have hlen : (Code.encodeValue value).length = Code.width (sourceType ty) := by
          rw [Code.encodeValue_length, ← htype]
        have last := hrep ((Code.encodeValue value).length - 1) (by omega)
        simp only [alloc.vec.Vec.deref, Slice.from_val] at last
        change offset.val + Code.width (sourceType ty) ≤ words.val.length
        omega
      step as ⟨widthSize, hwidthSize⟩
      step as ⟨nextSlot, hnextSlot⟩
      step as ⟨next, hnext⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [hnext, hnextOffset]
        scalar_tac
      · rw [hnext, List.take_add_one, hlookup]
        simp [hafter, hprior, hdecoded, value]
    · have he : i.val = values.length := by scalar_tac
      exact ⟨rfl, by simpa [he] using hprior⟩
  · exact ⟨bound, position, prior⟩


/-- The actual result-copy loop returns precisely the represented source
results and leaves the store unchanged. -/
@[step] theorem read_results {M : Type} (words : alloc.vec.Vec U64)
    (store : runtime.store.Store M) (results : alloc.vec.Vec runtime.Value)
    (types : alloc.vec.Vec Itasca.types.ValueType) (values : List val)
    (empty : results.val = [])
    (typed : types.val.map sourceType = values.map Code.valueType)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt words.val 0 values) :
    runtime.interp.invoke_with_loop2 words store results 0#usize 0#usize types
      ⦃ (afterStore, after) => afterStore = store ∧ after.val.map sourceValue = values ⦄ := by
  apply read_results_loop words store results 0#usize 0#usize types values typed wellFormed fits represented
  · simp
  · simp [Code.offset, Code.slots]
  · simp [empty]

end Exec.Interp




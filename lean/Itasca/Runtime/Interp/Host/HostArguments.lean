import Itasca.Runtime.Interp.Relations.Readback
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

@[step] theorem host_arguments_loop (words : alloc.vec.Vec U64)
    (store base : Usize) (results : alloc.vec.Vec runtime.Value)
    (index slot : Usize) (types : alloc.vec.Vec Itasca.types.ValueType) (values : List val)
    (typed : types.val.map sourceType = values.map Code.valueType)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt words.val base.val values)
    (bound : index.val ≤ values.length)
    (position : slot.val = base.val + Code.offset (values.map Code.valueType) index.val)
    (prior : results.val.map sourceValue = values.take index.val) :
    runtime.interp.call_loop0 words results store types index slot ⦃ after =>
      after.val.map sourceValue = values ⦄ := by
  have lengths : types.length = values.length := by
    have h := congrArg List.length typed
    simpa using h
  unfold runtime.interp.call_loop0
  apply loop.spec_decr_nat (fun p => values.length - p.2.1.val)
    (fun p => p.2.1.val ≤ values.length ∧
      p.2.2.val = base.val + Code.offset (values.map Code.valueType) p.2.1.val ∧
      p.1.val.map sourceValue = values.take p.2.1.val)
  · rintro ⟨current, i, offset⟩ ⟨hi, hoffset, hprior⟩
    dsimp only at hi hoffset hprior
    unfold runtime.interp.call_loop0.body
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
      step with decode_slot_value (alloc.vec.Vec.deref words) offset ty store value
        (wellFormed value member) htype hrep (fits value member)
        as ⟨decoded, hraw, hdecoded⟩
      have hcurrent : current.length = i.val := by
        have h := congrArg List.length hprior
        simpa [List.length_take, Nat.min_eq_left hi] using h
      step as ⟨after, hafter⟩
      step with width_spec ty as ⟨width, hwidth⟩
      have hnextOffset : base.val + Code.offset (values.map Code.valueType) (i.val + 1) =
          offset.val + Code.width (sourceType ty) := by
        rw [hoffset]
        simp [Code.offset, List.take_add_one, hlookup, Code.slots_append, Code.slots, ← htype, Nat.add_assoc]
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
      simpa [WP.spec_ok, he] using hprior
  · exact ⟨bound, position, prior⟩


/-- Host callbacks receive precisely the represented caller argument region. -/
@[step] theorem host_arguments (words : alloc.vec.Vec U64) (store base : Usize)
    (results : alloc.vec.Vec runtime.Value) (types : alloc.vec.Vec Itasca.types.ValueType)
    (values : List val) (empty : results.val = [])
    (typed : types.val.map sourceType = values.map Code.valueType)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt words.val base.val values) :
    runtime.interp.call_loop0 words results store types 0#usize base ⦃ after =>
      after.val.map sourceValue = values ⦄ := by
  apply host_arguments_loop words store base results 0#usize base types values typed wellFormed fits represented
  · simp
  · simp [Code.offset, Code.slots]
  · simp [empty]
end Itasca.Runtime.Interp

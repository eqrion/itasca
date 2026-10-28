import Exec.Interp.Relations.Readback
import Exec.Interp.Relations.DecodeOwnership
import Itasca.Support.Result
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

@[step] theorem read_results_loop_owned {M : Type} (words : alloc.vec.Vec U64)
    (store : runtime.store.Store M) (results : alloc.vec.Vec runtime.Value)
    (index slot : Usize) (types : alloc.vec.Vec Itasca.types.ValueType) (values : List val)
    (typed : types.val.map sourceType = values.map Code.valueType)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt words.val 0 values)
    (bound : index.val ≤ values.length)
    (position : slot.val = Code.offset (values.map Code.valueType) index.val)
    (prior : results.val.map sourceValue = values.take index.val)
    (priorOwned : ∀ value ∈ results.val, OwnedBy store.id value) :
    runtime.interp.invoke_with_loop2 words store results index slot types ⦃ (afterStore, after) =>
      afterStore = store ∧ after.val.map sourceValue = values ∧
        (∀ value ∈ after.val, OwnedBy store.id value) ⦄ := by
  have lengths : types.length = values.length := by
    have h := congrArg List.length typed
    simpa using h
  unfold runtime.interp.invoke_with_loop2
  apply loop.spec_decr_nat (fun p => values.length - p.2.1.val)
    (fun p => p.2.1.val ≤ values.length ∧
      p.2.2.val = Code.offset (values.map Code.valueType) p.2.1.val ∧
      p.1.val.map sourceValue = values.take p.2.1.val ∧
      (∀ value ∈ p.1.val, OwnedBy store.id value))
  · rintro ⟨current, i, offset⟩ ⟨hi, hoffset, hprior, howners⟩
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
      obtain ⟨decoded,decodeActual,hraw,hdecoded⟩ := WP.spec_imp_exists
        (decode_slot_value (alloc.vec.Vec.deref words) offset ty store.id value
          (wellFormed value member) htype hrep (fits value member))
      have howner := decode_slot_owned_of_ok (alloc.vec.Vec.deref words) offset ty store.id decoded decodeActual
      rw [decodeActual,bind_ok]
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
      refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
      · rw [hnext, hnextOffset]
        scalar_tac
      · rw [hnext, List.take_add_one, hlookup]
        simp [hafter, hprior, hdecoded, value]
      · intro value member
        rw [hafter] at member
        rcases List.mem_append.mp member with old | fresh
        · exact howners value old
        · simp only [List.mem_singleton] at fresh
          subst value
          exact howner
    · have he : i.val = values.length := by scalar_tac
      exact ⟨rfl, by simpa [he] using hprior,howners⟩
  · exact ⟨bound, position, prior,priorOwned⟩


/-- The actual result-copy loop returns precisely the represented source
results and leaves the store unchanged. -/
@[step] theorem read_results_owned {M : Type} (words : alloc.vec.Vec U64)
    (store : runtime.store.Store M) (results : alloc.vec.Vec runtime.Value)
    (types : alloc.vec.Vec Itasca.types.ValueType) (values : List val)
    (empty : results.val = [])
    (typed : types.val.map sourceType = values.map Code.valueType)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt words.val 0 values) :
    runtime.interp.invoke_with_loop2 words store results 0#usize 0#usize types
      ⦃ (afterStore, after) => afterStore = store ∧ after.val.map sourceValue = values ∧
        (∀ value ∈ after.val, OwnedBy store.id value) ⦄ := by
  apply read_results_loop_owned words store results 0#usize 0#usize types values typed wellFormed fits represented
  · simp
  · simp [Code.offset, Code.slots]
  · simp [empty]
  · simp [empty]

end Itasca.Runtime.Interp

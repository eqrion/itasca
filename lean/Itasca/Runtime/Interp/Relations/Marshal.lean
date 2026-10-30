import Itasca.Runtime.Interp.Relations.CopyRel
import Itasca.Runtime.Interp.Relations.Arguments
import Itasca.Runtime.Interp.Relations.TypeSlots

/-! API argument marshalling into the interpreter's live slot region. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem written_outside (words : List U64) (position index : Nat)
    (ty : Itasca.wasm_types.ValueType) (lo hi : U64)
    (outside : index < position ∨ position + Compiler.width (sourceType ty) ≤ index) :
    (written words position ty lo hi)[index]? = words[index]? := by
  have hp : index ≠ position := by have := Compiler.width_positive (sourceType ty); omega
  unfold written
  split
  · rename_i hv
    have hh : index ≠ position + 1 := by simp only [hv, Compiler.width] at outside; omega
    simp [hp, hh]
  · simp [hp]

theorem written_represents (words : List U64) (position : Nat)
    (ty : Itasca.wasm_types.ValueType) (lo hi : U64)
    (bound : position + Compiler.width (sourceType ty) ≤ words.length) :
    WordsAt (written words position ty lo hi) position (pairWords ty (lo, hi)) := by
  intro index hindex
  by_cases hv : sourceType ty = .V128
  · simp only [pairWords, hv, ↓reduceIte, List.length_cons, List.length_nil] at hindex
    have hhigh : position + 1 < words.length := by simp only [hv, Compiler.width] at bound; omega
    have hz : position < words.length := by omega
    have hj : index = 0 ∨ index = 1 := by omega
    rcases hj with rfl | rfl
    · exact ⟨by rw [written_length]; omega, by simp [pairWords, hv, written_low words position ty lo hi hz]⟩
    · exact ⟨by rw [written_length]; omega, by simp [pairWords, hv, written_high words position ty lo hi hv hhigh]⟩
  · have hw : Compiler.width (sourceType ty) = 1 := by cases ty <;> simp_all [sourceType, Compiler.width]
    have hz : position < words.length := by omega
    simp only [pairWords, hv, ↓reduceIte, List.length_cons, List.length_nil] at hindex
    have hj : index = 0 := by omega
    subst index
    exact ⟨by rw [written_length]; omega, by simp [pairWords, hv, written_low words position ty lo hi hz]⟩

/-- Writing one owned, representable argument establishes its source value
region and preserves every word outside that region. -/
@[step] theorem encode_slot_represents (slots : Slice U64) (position : Usize)
    (value : runtime.Value) (store : Usize) (owned : ValueOwnedFits store value)
    (bound : position.val + Compiler.width (sourceType (rawType value)) ≤ slots.length) :
    runtime.interp.encode_slot slots position (rawType value) value ⦃ after =>
      after.length = slots.length ∧
      WordsAt after.val position.val (Compiler.encodeValue (sourceValue value)) ∧
      ∀ index, index < position.val ∨ position.val + Compiler.width (sourceType (rawType value)) ≤ index →
        after.val[index]? = slots.val[index]? ⦄ := by
  obtain ⟨⟨lo, hi⟩, he, hwords⟩ := WP.spec_imp_exists (encode_value_spec value store owned)
  step with encode_slot_spec slots position (rawType value) value lo hi he bound as ⟨after, ha⟩
  refine ⟨?_, ?_, ?_⟩
  · change after.val.length = slots.val.length
    rw [ha, written_length]
  · rw [ha, ← hwords]
    exact written_represents slots.val position.val (rawType value) lo hi bound
  · intro index outside
    rw [ha]
    exact written_outside slots.val position.val index (rawType value) lo hi outside


def argumentWords (args : List runtime.Value) (count : Nat) : List Nat :=
  Compiler.encodeValues ((args.take count).map sourceValue)

theorem argument_words_step {args : List runtime.Value} {index : Nat} {value : runtime.Value}
    (lookup : args[index]? = some value) :
    argumentWords args (index + 1) = argumentWords args index ++ Compiler.encodeValue (sourceValue value) := by
  simp [argumentWords, List.take_add_one, lookup, Compiler.encode_values_append, Compiler.encodeValues]

theorem argument_words_bound (args : List runtime.Value) (count : Nat) :
    (argumentWords args count).length ≤ (Compiler.encodeValues (args.map sourceValue)).length := by
  rw [argumentWords, Compiler.encode_values_length, Compiler.encode_values_length]
  simp only [List.map_map, List.map_take]
  exact Compiler.offset_le _ _

@[step] theorem marshal_arguments_loop (words : alloc.vec.Vec U64)
    (args : Slice runtime.Value) (types : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (index slot : Usize) (store : Usize)
    (typed : types.val = args.val.map rawType)
    (owned : ∀ value ∈ args.val, ValueOwnedFits store value)
    (bound : (Compiler.encodeValues (args.val.map sourceValue)).length ≤ words.length)
    (indexBound : index.val ≤ args.length)
    (position : slot.val = (argumentWords args.val index.val).length)
    (initialWords : WordsAt words.val 0 (argumentWords args.val index.val)) :
    runtime.interp.invoke_with_loop0 words args types index slot ⦃ after =>
      after.length = words.length ∧ ValuesAt after.val 0 (args.val.map sourceValue) ⦄ := by
  unfold runtime.interp.invoke_with_loop0
  apply loop.spec_decr_nat (fun p => args.length - p.2.1.val)
    (fun p => p.1.length = words.length ∧ p.2.1.val ≤ args.length ∧
      p.2.2.val = (argumentWords args.val p.2.1.val).length ∧
      WordsAt p.1.val 0 (argumentWords args.val p.2.1.val))
  · rintro ⟨current, i, offset⟩ ⟨hlen, hi, hoffset, hpref⟩
    dsimp only at hlen hi hoffset hpref
    unfold runtime.interp.invoke_with_loop0.body
    dsimp only
    split
    · have hib : i.val < args.val.length := by change i.val < args.length; scalar_tac
      have hit : i.val < types.length := by change i.val < types.val.length; rw [typed, List.length_map]; exact hib
      simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
      step as ⟨ty, hty⟩
      step as ⟨value, hvalue⟩
      have hlookup : args.val[i.val]? = some value := by simp [List.getElem?_eq_getElem hib, hvalue]
      have htype : ty = rawType value := by simpa [typed, ← hvalue] using hty
      have hnextWords := argument_words_step hlookup
      have hcapacity : offset.val + Compiler.width (sourceType (rawType value)) ≤ current.length := by
        have hb := argument_words_bound args.val (i.val + 1)
        rw [hnextWords, List.length_append, Compiler.encode_value_length, source_value_type] at hb
        omega
      have hv : ValueOwnedFits store value := owned value (by rw [hvalue]; exact List.getElem_mem hib)
      rw [htype]
      step with encode_slot_represents current.slice offset value store hv (by simpa only [alloc.vec.Vec.length, alloc.vec.Vec.val] using hcapacity)
        as ⟨after, hafterLen, hencoded, houtside⟩
      step with width_spec (rawType value) as ⟨width, hwidth⟩
      step as ⟨nextSlot, hnextSlot⟩
      step as ⟨next, hnext⟩
      refine ⟨?_, by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simpa [alloc.vec.Vec.val] using hafterLen.trans hlen
      · rw [hnext, hnextWords, List.length_append, Compiler.encode_value_length, source_value_type]
        scalar_tac
      · rw [hnext, hnextWords]
        apply WordsAt.append
        · apply hpref.congr_region hafterLen
          intro j hj
          apply houtside
          exact Or.inl (by omega)
        · simpa [hoffset, alloc.vec.Vec.val] using hencoded
    · have he : i.val = args.length := by scalar_tac
      have ht : args.val.take i.val = args.val := List.take_of_length_le (by change args.length ≤ i.val; omega)
      exact ⟨hlen, by simpa [ValuesAt, argumentWords, ht] using hpref⟩
  · exact ⟨rfl, indexBound, position, initialWords⟩


/-- The actual invocation argument loop produces the specification encoding
of every accepted argument, starting at slot zero. -/
@[step] theorem marshal_arguments (words : alloc.vec.Vec U64)
    (args : Slice runtime.Value) (types : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (store : Usize) (typed : types.val = args.val.map rawType)
    (owned : ∀ value ∈ args.val, ValueOwnedFits store value)
    (bound : (Compiler.encodeValues (args.val.map sourceValue)).length ≤ words.length) :
    runtime.interp.invoke_with_loop0 words args types 0#usize 0#usize ⦃ after =>
      after.length = words.length ∧ ValuesAt after.val 0 (args.val.map sourceValue) ⦄ := by
  apply marshal_arguments_loop words args types 0#usize 0#usize store typed owned bound
  · simp
  · simp [argumentWords, Compiler.encodeValues]
  · intro j hj
    simp [argumentWords, Compiler.encodeValues] at hj

end Itasca.Runtime.Interp



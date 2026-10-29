import Itasca.Runtime.Interp.Relations.Marshal
import Itasca.Runtime.Interp.Relations.Fetch

/-!
Host result copying and resumption. The result-buffer loop establishes the slot effect consumed when resuming the suspended execution after a callback.
-/

/-! ## Host Results -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
@[step] theorem host_results_encode_loop (words : alloc.vec.Vec U64)
    (args : alloc.vec.Vec runtime.Value) (types : alloc.vec.Vec Itasca.types.ValueType)
    (index slot : Usize) (store base : Usize)
    (typed : types.val = args.val.map rawType)
    (owned : ∀ value ∈ args.val, ValueOwnedFits store value)
    (bound : base.val + (Compiler.encodeValues (args.val.map sourceValue)).length ≤ words.length)
    (indexBound : index.val ≤ args.length)
    (position : slot.val = base.val + (argumentWords args.val index.val).length)
    (initialWords : WordsAt words.val base.val (argumentWords args.val index.val)) :
    runtime.interp.call_loop2 words args index slot types ⦃ after =>
      after.length = words.length ∧ ValuesAt after.val base.val (args.val.map sourceValue) ∧
      ∀ j, j < base.val ∨ base.val + (Compiler.encodeValues (args.val.map sourceValue)).length ≤ j →
        after.val[j]? = words.val[j]? ⦄ := by
  unfold runtime.interp.call_loop2
  apply loop.spec_decr_nat (fun p => args.length - p.2.1.val)
    (fun p => p.1.length = words.length ∧ p.2.1.val ≤ args.length ∧
      p.2.2.val = base.val + (argumentWords args.val p.2.1.val).length ∧
      WordsAt p.1.val base.val (argumentWords args.val p.2.1.val) ∧
      ∀ j, j < base.val ∨ base.val + (Compiler.encodeValues (args.val.map sourceValue)).length ≤ j →
        p.1.val[j]? = words.val[j]?)
  · rintro ⟨current, i, offset⟩ ⟨hlen, hi, hoffset, hpref, preserved⟩
    dsimp only at hlen hi hoffset hpref
    unfold runtime.interp.call_loop2.body
    dsimp only
    split
    · have hib : i.val < args.val.length := by change i.val < args.length; scalar_tac
      have hit : i.val < types.length := by change i.val < types.val.length; rw [typed, List.length_map]; exact hib
      step as ⟨value, hvalue⟩
      simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
      step as ⟨ty, hty⟩
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
      refine ⟨?_, by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
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
      · intro j outside
        have nextBound := argument_words_bound args.val (i.val + 1)
        rw [hnextWords, List.length_append, Compiler.encode_value_length, source_value_type] at nextBound
        exact (houtside j (by rcases outside with left | right; exact Or.inl (by omega); exact Or.inr (by omega))).trans
          (preserved j outside)
    · have he : i.val = args.length := by scalar_tac
      have ht : args.val.take i.val = args.val := List.take_of_length_le (by change args.length ≤ i.val; omega)
      exact ⟨hlen, by simpa [ValuesAt, argumentWords, ht] using hpref, preserved⟩
  · exact ⟨rfl, indexBound, position, initialWords, fun _ _ => rfl⟩


/-- Type-checked host results replace exactly the caller's result region. -/
@[step] theorem host_results_encode (words : alloc.vec.Vec U64)
    (args : alloc.vec.Vec runtime.Value) (types : alloc.vec.Vec Itasca.types.ValueType)
    (store base : Usize) (typed : types.val = args.val.map rawType)
    (owned : ∀ value ∈ args.val, ValueOwnedFits store value)
    (bound : base.val + (Compiler.encodeValues (args.val.map sourceValue)).length ≤ words.length) :
    runtime.interp.call_loop2 words args 0#usize base types ⦃ after =>
      after.length = words.length ∧ ValuesAt after.val base.val (args.val.map sourceValue) ∧
      ∀ j, j < base.val ∨ base.val + (Compiler.encodeValues (args.val.map sourceValue)).length ≤ j →
        after.val[j]? = words.val[j]? ⦄ := by
  apply host_results_encode_loop words args types 0#usize base store base typed owned bound
  · simp
  · simp [argumentWords, Compiler.encodeValues]
  · intro j impossible
    simp [argumentWords, Compiler.encodeValues] at impossible
end Itasca.Runtime.Interp

end

/-! ## Host Resume -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- The extracted host-call continuation, after the callback's borrowed result
slice has been restored to its scratch vector. -/
def hostResume {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (address : runtime.FuncAddr) (base : Usize) (results : alloc.vec.Vec runtime.Value)
    (status : core.result.Result Unit runtime.platform.HostError) :
    Result (core.result.Result Unit runtime.ExecError × runtime.interp.Execution) := do
  match status with
  | .Ok _ =>
    let function ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.store.FuncInst) store.funcs address.index
    let signature ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Itasca.types.FuncType) store.types function.signature
    let checked ← runtime.interp.check_values memory store results.slice signature.results.slice
    let failed ← runtime.interp.check_failed checked
    if failed then Result.ok (.Err (.Trap .Host),{exec with host_results := results})
    else
      let words ← runtime.interp.call_loop2 exec.slots results 0#usize base signature.results
      Result.ok (.Ok (),{exec with slots := words,host_results := results})
  | .Err .Trap => Result.ok (.Err (.Trap .Host),{exec with host_results := results})
  | .Err .StackOverflow => Result.ok (.Err (.Exhausted .CallStack),{exec with host_results := results})

end Itasca.Runtime.Interp

end

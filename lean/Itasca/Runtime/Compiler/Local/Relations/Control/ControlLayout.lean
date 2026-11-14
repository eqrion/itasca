import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame

/-! Exact word heights for validator control-stack prefixes, including bottom
stack entries, using the extracted integer-width and accumulation loops. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std



theorem stack_words_take_mono (values : List Itasca.code.StackType) {a b : Nat} (order : a ≤ b) :
    stackWords (values.take a) ≤ stackWords (values.take b) := by
  have nested : (values.take b).take a = values.take a := by simp [List.take_take, Nat.min_eq_left order]
  rw [← nested]
  simp only [stackWords, List.map_take]
  have sum := congrArg List.sum (List.take_append_drop a ((values.take b).map compilerStackWidth))
  simp only [List.sum_append, List.map_take] at sum
  omega

theorem stack_words_take_succ (values : List Itasca.code.StackType) (i : Nat) (bound : i < values.length) :
    stackWords (values.take (i + 1)) = stackWords (values.take i) + compilerStackWidth values[i] := by
  rw [← List.take_concat_get' values i bound]
  simp only [stackWords, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]

@[step] theorem control_stack_width (ty : Itasca.code.StackType) :
    runtime.compiler.stack_width ty ⦃ out => out.val = compilerStackWidth ty ⦄ := by
  cases ty with
  | Bot => simp [runtime.compiler.stack_width, compilerStackWidth, WP.spec_ok]
  | Val ty => exact compiler_width ty

@[step] theorem control_stack_height (values : Slice Itasca.code.StackType) (count : Usize) (initial : U32)
    (countFits : count.val ≤ values.val.length)
    (heightFits : initial.val + stackWords (values.val.take count.val) ≤ U32.max) :
    runtime.compiler.control.stack_height values count initial ⦃ out =>
      out.val = initial.val + stackWords (values.val.take count.val) ⦄ := by
  unfold runtime.compiler.control.stack_height runtime.compiler.control.stack_height_loop
  apply loop.spec_decr_nat (fun p => count.val - p.2.val)
    (fun p => p.2.val ≤ count.val ∧ p.1.val = initial.val + stackWords (values.val.take p.2.val))
  · rintro ⟨height, i⟩ ⟨hi, hheight⟩
    dsimp only at hi hheight
    unfold runtime.compiler.control.stack_height_loop.body
    dsimp only
    split
    · rename_i more
      have lower : i.val < count.val := by scalar_tac
      have inBounds : i.val < values.length := by change i.val < values.val.length; omega
      step as ⟨ty, hty⟩
      step with control_stack_width ty as ⟨word, hword⟩
      have increment := stack_words_take_succ values.val i.val (by omega)
      have bounded := stack_words_take_mono values.val (a := i.val + 1) (b := count.val) (by omega)
      have additionFits : height.val + word.val ≤ U32.max := by
        rw [hheight, hword, hty]
        omega
      step as ⟨nextHeight, hnext⟩
      step as ⟨nextIndex, hindex⟩
      refine ⟨?_, ?_, ?_⟩
      · omega
      · rw [hnext, hheight, hword, hty, hindex, increment]
        omega
      · omega
    · rename_i finished
      have same : i.val = count.val := by scalar_tac
      simpa [WP.spec_ok, same] using hheight
  · simp [stackWords]
/-- A successful height computation certifies its exact sum. This partial
correctness statement also covers dormant source stacks; it makes no totality
claim for operands whose mathematical slot count exceeds u32. -/
theorem control_stack_height_success (values : Slice Itasca.code.StackType)
    (count : Usize) (initial out : U32) (countFits : count.val ≤ values.val.length)
    (success : runtime.compiler.control.stack_height values count initial = .ok out) :
    out.val = initial.val + stackWords (values.val.take count.val) := by
  let inv : U32 × Usize → Prop := fun state =>
    state.2.val ≤ count.val ∧ state.1.val = initial.val + stackWords (values.val.take state.2.val)
  have body : ∀ state, inv state → ∀ flow,
      runtime.compiler.control.stack_height_loop.body values count state.1 state.2 = .ok flow →
      match flow with
      | .cont next => inv next ∧ count.val - next.2.val < count.val - state.2.val
      | .done result => result.val = initial.val + stackWords (values.val.take count.val) := by
    rintro ⟨height, index⟩ ⟨bound, exactHeight⟩ flow call
    dsimp only at bound exactHeight
    unfold runtime.compiler.control.stack_height_loop.body at call
    split at call
    · rename_i more
      have ltCount : index.val < count.val := more
      have inBounds : index.val < values.val.length := by omega
      obtain ⟨value, read, rest⟩ := initializer_bind_success call
      have readSpec : Slice.index_usize values index ⦃ found => found = values.val[index.val] ⦄ := by
        step as ⟨found, atFound⟩
        exact atFound
      rw [read, WP.spec_ok] at readSpec
      subst value
      obtain ⟨word, widthCall, rest⟩ := initializer_bind_success rest
      have widthSpec := control_stack_width values.val[index.val]
      rw [widthCall, WP.spec_ok] at widthSpec
      obtain ⟨nextHeight, added, rest⟩ := initializer_bind_success rest
      obtain ⟨nextIndex, advanced, rest⟩ := initializer_bind_success rest
      have returned := Result.ok_injective rest
      subst flow
      have heightEq := control_add_success added
      have indexEq := control_add_success advanced
      have increment := stack_words_take_succ values.val index.val inBounds
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · dsimp only; scalar_tac
      · dsimp only
        rw [heightEq, exactHeight, widthSpec]
        have next : nextIndex.val = index.val + 1 := by simpa using indexEq
        rw [next, increment]
        omega
      · dsimp only; scalar_tac
    · rename_i done
      have same : index.val = count.val := by scalar_tac
      have returned := Result.ok_injective call
      subst flow
      simpa only [same] using exactHeight
  exact initializer_loop_success
    (fun state => runtime.compiler.control.stack_height_loop.body values count state.1 state.2)
    (fun state => count.val - state.2.val) inv
    (fun result : U32 => result.val = initial.val + stackWords (values.val.take count.val))
    (by
      intro state hi flow call
      have h := body state hi flow call
      cases flow <;> exact h) (initial, 0#usize) (by simp [inv, stackWords]) out success

end Itasca.Runtime.Compiler

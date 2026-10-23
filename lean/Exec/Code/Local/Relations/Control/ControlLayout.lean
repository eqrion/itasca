import Exec.Code.Local.Callbacks.Common.Observe
/-! Exact word heights for validator control-stack prefixes, including bottom
stack entries, using the extracted integer-width and accumulation loops. -/
namespace Exec.Code
open Aeneas Aeneas.Std



theorem stackWords_take_mono (values : List Itasca.code.StackType) {a b : Nat} (order : a ≤ b) :
    stackWords (values.take a) ≤ stackWords (values.take b) := by
  have nested : (values.take b).take a = values.take a := by simp [List.take_take, Nat.min_eq_left order]
  rw [← nested]
  simp only [stackWords, List.map_take]
  have sum := congrArg List.sum (List.take_append_drop a ((values.take b).map compilerStackWidth))
  simp only [List.sum_append, List.map_take] at sum
  omega

theorem stackWords_take_succ (values : List Itasca.code.StackType) (i : Nat) (bound : i < values.length) :
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
      have increment := stackWords_take_succ values.val i.val (by omega)
      have bounded := stackWords_take_mono values.val (a := i.val + 1) (b := count.val) (by omega)
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
end Exec.Code

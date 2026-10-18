import Exec.Interp.Relations.Marshal

/-! Clearing per-invocation scratch state uses the actual extracted pop loops. -/
namespace Exec.Interp
open Aeneas Aeneas.Std

@[step] theorem clear_results (results : alloc.vec.Vec runtime.Value) :
    runtime.interp.invoke_with_loop3 results ⦃ after => after.val = [] ⦄ := by
  unfold runtime.interp.invoke_with_loop3
  apply loop.spec_decr_nat (fun current => current.length) (fun _ => True)
  · intro current _
    unfold runtime.interp.invoke_with_loop3.body
    dsimp only
    split
    · have positive : 0 < current.length := by scalar_tac
      simp [alloc.vec.Vec.pop]
      omega
    · have empty : current.length = 0 := by scalar_tac
      simpa only [WP.spec_ok] using List.length_eq_zero_iff.mp empty
  · trivial

@[step] theorem clear_frames (exec : runtime.interp.Execution) :
    runtime.interp.invoke_with_loop0 exec ⦃ (slots, frames, hostArgs, hostResults) =>
      slots = exec.slots ∧ frames.val = [] ∧ hostArgs = exec.host_args ∧ hostResults = exec.host_results ⦄ := by
  unfold runtime.interp.invoke_with_loop0
  apply loop.spec_decr_nat (fun current => current.frames.length)
    (fun current => current.slots = exec.slots ∧ current.host_args = exec.host_args ∧
      current.host_results = exec.host_results)
  · intro current hinv
    unfold runtime.interp.invoke_with_loop0.body
    dsimp only
    split
    · have positive : 0 < current.frames.length := by scalar_tac
      simp [alloc.vec.Vec.pop]
      exact ⟨hinv.1, hinv.2.1, hinv.2.2, by omega⟩
    · have empty : current.frames.length = 0 := by scalar_tac
      exact ⟨hinv.1, List.length_eq_zero_iff.mp empty, hinv.2⟩
  · exact ⟨rfl, rfl, rfl⟩

end Exec.Interp

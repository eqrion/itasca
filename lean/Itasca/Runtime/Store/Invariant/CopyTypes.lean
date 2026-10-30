import Itasca.Runtime.Store.Api.Define

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

@[step] theorem copy_type_loop (source target : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (position : Usize) (hpos : position.val ≤ source.length)
    (htarget : target.val = source.val.take position.val) :
    runtime.copy_type_loop0 source target position ⦃ after => after = source ⦄ := by
  unfold runtime.copy_type_loop0
  apply loop.spec_decr_nat (fun pair => source.length - pair.2.val)
    (fun pair => pair.2.val ≤ source.length ∧ pair.1.val = source.val.take pair.2.val)
  · intro pair hinv
    rcases pair with ⟨items, pos⟩
    rcases hinv with ⟨hpos, hitems⟩
    unfold runtime.copy_type_loop0.body
    dsimp only at hpos hitems ⊢
    split
    · rename_i hmore
      have hi : pos.val < source.length := by scalar_tac
      have hlen : items.length = pos.val := by simp [hitems, Nat.min_eq_left hpos]
      have hmax : items.length < Usize.max := by scalar_tac
      step as ⟨value, hvalue⟩
      step as ⟨after, hafter⟩
      step as ⟨next, hnext⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hafter, hitems, hnext, List.take_succ_eq_append_getElem hi, hvalue]
    · rename_i hstop
      have heq : pos.val = source.length := by scalar_tac
      simp only [WP.spec_ok]
      apply alloc.vec.Vec.ext
      simpa [heq] using hitems
  · exact ⟨hpos, htarget⟩

@[step] theorem copy_type_loop_results (source target : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (position : Usize) (hpos : position.val ≤ source.length)
    (htarget : target.val = source.val.take position.val) :
    runtime.copy_type_loop1 source target position ⦃ after => after = source ⦄ := by
  have heq : runtime.copy_type_loop1 source target position = runtime.copy_type_loop0 source target position := by rfl
  rw [heq]
  exact copy_type_loop source target position hpos htarget

/-- Type copying preserves the entire signature, or reports only an allocation
failure; allocator capacity changes cannot change any value. -/
theorem copy_type_spec {A : Type} (allocator : runtime.platform.Alloc A)
    (ha : Platform.AllocCorrect allocator) (ty : Itasca.wasm_types.FuncType) :
    runtime.copy_type allocator ty ⦃ answer =>
      answer = .Ok ty ∨ answer = .Err (.Exhausted .Allocation) ⦄ := by
  unfold runtime.copy_type
  dsimp only
  obtain ⟨answer, hr⟩ := reserve_wrapper_eq allocator ha (alloc.vec.Vec.new Itasca.wasm_types.ValueType) (alloc.vec.Vec.len ty.params)
  rw [hr]
  cases answer
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨answer, hr⟩ := reserve_wrapper_eq allocator ha (alloc.vec.Vec.new Itasca.wasm_types.ValueType) (alloc.vec.Vec.len ty.results)
    rw [hr]
    cases answer
    · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · simp
      step with copy_type_loop ty.params (alloc.vec.Vec.new Itasca.wasm_types.ValueType) 0#usize (by scalar_tac) (by simp) as ⟨params, hp⟩
      step with copy_type_loop_results ty.results (alloc.vec.Vec.new Itasca.wasm_types.ValueType) 0#usize (by scalar_tac) (by simp) as ⟨results, hr⟩
      simp [hp, hr]

end Itasca.Runtime.Store

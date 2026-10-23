import Exec.Store.Invariant.InstanceItems
import Exec.Store.Invariant.PrecommitError
namespace Exec.Store
open Aeneas Aeneas.Std
theorem item_counts_loop_errors (counts : Array Usize 7#usize) (items start : Usize)
    (startBound : start.val ≤ counts.val.length) :
    runtime.store.instantiate.Store.prepare_instance_loop0 items (.Ok ()) counts start
      ⦃ out => ErrorAllowed ResourceError out.2 ∧ (out.2 = .Ok () → out.1.val = items.val + ((counts.val.drop start.val).map UScalar.val).sum) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop0
  apply loop.spec_decr_nat (fun state => counts.val.length - state.2.2.val)
    (fun state => ErrorAllowed ResourceError state.2.1 ∧ state.2.2.val ≤ counts.val.length ∧
      (state.2.1 = .Ok () → state.1.val + ((counts.val.drop state.2.2.val).map UScalar.val).sum =
        items.val + ((counts.val.drop start.val).map UScalar.val).sum))
  · rintro ⟨current, status, index⟩ ⟨errors, bound, total⟩
    dsimp only at errors bound total ⊢
    unfold runtime.store.instantiate.Store.prepare_instance_loop0.body
    simp only [lift, bind_ok]
    split
    · rename_i more
      have hmore : index.val < counts.val.length := by simpa using more
      cases status with
      | Err error => simp [core.result.Result.is_ok, errors]
      | Ok value =>
        cases value
        have exactTotal := total rfl
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step as ⟨additional, read⟩
        step with add_items_effect current additional as ⟨status, updated, effect⟩
        have nextErrors : ErrorAllowed ResourceError status := by
          rcases effect with ⟨ok, addition⟩ | ⟨failed, overflow⟩
          · rw [ok]; trivial
          · rw [failed]; trivial
        have max := counts.property
        step as ⟨next, increment⟩
        refine ⟨nextErrors, ?_, ?_, ?_⟩
        · omega
        · intro success
          rcases effect with ⟨ok, addition⟩ | ⟨failed, overflow⟩
          · rw [List.drop_eq_getElem_cons hmore] at exactTotal
            simp only [List.map_cons, List.sum_cons] at exactTotal
            simp only [increment]
            rw [read] at addition
            omega
          · simp [failed] at success
        · omega
    · have equal : index.val = counts.val.length := by simp at *; omega
      simp only [WP.spec_ok]
      refine ⟨errors, ?_⟩
      intro success
      have exactTotal := total success
      simpa [equal] using exactTotal
  · exact ⟨True.intro, startBound, fun _ => rfl⟩

theorem element_items_loop_errors (module : runtime.compiler.ExecutableModule) (items start : Usize)
    (startBound : start.val ≤ module.module.env.elements.val.length) :
    runtime.store.instantiate.Store.prepare_instance_loop1 module items (.Ok ()) start
      ⦃ out => ErrorAllowed ResourceError out.2 ∧ (out.2 = .Ok () → out.1.val = items.val +
        ((module.module.env.elements.val.drop start.val).map fun element => element.init.length).sum) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop1
  apply loop.spec_decr_nat (fun state => module.module.env.elements.val.length - state.2.2.val)
    (fun state => ErrorAllowed ResourceError state.2.1 ∧ state.2.2.val ≤ module.module.env.elements.val.length ∧
      (state.2.1 = .Ok () → state.1.val +
        ((module.module.env.elements.val.drop state.2.2.val).map fun element => element.init.length).sum =
        items.val + ((module.module.env.elements.val.drop start.val).map fun element => element.init.length).sum))
  · rintro ⟨current, status, index⟩ ⟨errors, bound, total⟩
    dsimp only at errors bound total ⊢
    unfold runtime.store.instantiate.Store.prepare_instance_loop1.body
    simp only [runtime.compiler.ExecutableModule.env, Exec.module.Module.env,
      Itasca.module.Module.impl.env, Exec.module.Env.elements, Itasca.module.Env.impl.elements, bind_ok]
    split
    · rename_i more
      have hmore : index.val < module.module.env.elements.val.length := by simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error => simp [core.result.Result.is_ok, errors]
      | Ok value =>
        cases value
        have exactTotal := total rfl
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step as ⟨element, read⟩
        step with add_items_effect current element.init.len as ⟨status, updated, effect⟩
        have nextErrors : ErrorAllowed ResourceError status := by
          rcases effect with ⟨ok, addition⟩ | ⟨failed, overflow⟩
          · rw [ok]; trivial
          · rw [failed]; trivial
        have max := module.module.env.elements.property
        step as ⟨next, increment⟩
        refine ⟨nextErrors, ?_, ?_, ?_⟩
        · omega
        · intro success
          rcases effect with ⟨ok, addition⟩ | ⟨failed, overflow⟩
          · rw [List.drop_eq_getElem_cons hmore] at exactTotal
            simp only [List.map_cons, List.sum_cons] at exactTotal
            simp only [increment]
            rw [read] at addition
            simp [alloc.vec.Vec.deref] at addition
            change updated.val = current.val + module.module.env.elements.val[index.val].init.length at addition
            omega
          · simp [failed] at success
        · omega
    · rename_i stop
      have equal : index.val = module.module.env.elements.val.length := by simp [alloc.vec.Vec.deref] at stop; omega
      simp only [WP.spec_ok]
      refine ⟨errors, ?_⟩
      intro success
      have exactTotal := total success
      simpa [equal] using exactTotal
  · exact ⟨True.intro, startBound, fun _ => rfl⟩


end Exec.Store

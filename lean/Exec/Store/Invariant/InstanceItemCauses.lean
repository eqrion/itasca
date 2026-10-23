import Exec.Store.Invariant.InstanceItems
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Exact checked-sum outcome. An error witnesses that the complete mathematical
sum exceeds the machine counter; it is not merely an exhaustion label. -/
def ItemSumOutcome (total : Nat) (out : Usize × core.result.Result Unit runtime.ExecError) : Prop :=
  match out.2 with
  | .Ok () => out.1.val = total
  | .Err error => error = .Exhausted .Objects ∧ Usize.max < total

theorem item_counts_resource_causes (counts : Array Usize 7#usize) (items start : Usize)
    (startBound : start.val ≤ counts.val.length) :
    runtime.store.instantiate.Store.prepare_instance_loop0 items (.Ok ()) counts start
      ⦃ out => ItemSumOutcome (items.val + ((counts.val.drop start.val).map UScalar.val).sum) out ⦄ := by
  let total := items.val + ((counts.val.drop start.val).map UScalar.val).sum
  unfold runtime.store.instantiate.Store.prepare_instance_loop0
  apply loop.spec_decr_nat (fun state => counts.val.length - state.2.2.val)
    (fun state => state.2.2.val ≤ counts.val.length ∧
      match state.2.1 with
      | .Ok () => state.1.val + ((counts.val.drop state.2.2.val).map UScalar.val).sum = total
      | .Err error => error = .Exhausted .Objects ∧ Usize.max < total)
  · rintro ⟨current,status,index⟩ ⟨bound,invariant⟩
    dsimp only at bound invariant ⊢
    unfold runtime.store.instantiate.Store.prepare_instance_loop0.body
    simp only [lift,bind_ok]
    split
    · rename_i more
      have hmore : index.val < counts.val.length := by simpa using more
      cases status with
      | Err error => simpa [core.result.Result.is_ok,ItemSumOutcome,total] using invariant
      | Ok value =>
        cases value
        simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
        step as ⟨additional,read⟩
        step with add_items_effect current additional as ⟨status,updated,effect⟩
        have max := counts.property
        step as ⟨next,increment⟩
        rw [List.drop_eq_getElem_cons hmore] at invariant
        simp only [List.map_cons,List.sum_cons] at invariant
        refine ⟨?_,?_,?_⟩
        · omega
        · rcases effect with ⟨ok,addition⟩ | ⟨failed,overflow⟩
          · subst status
            rw [read] at addition
            simpa only [increment] using (by omega : updated.val + ((counts.val.drop (index.val+1)).map UScalar.val).sum = total)
          · cases failed
            rw [read] at overflow
            exact ⟨rfl,by omega⟩
        · omega
    · have equal : index.val = counts.val.length := by simp at *; omega
      cases status with
      | Err error => simpa [ItemSumOutcome,total] using invariant
      | Ok unit => simpa [ItemSumOutcome,equal,total] using invariant
  · exact ⟨startBound,rfl⟩

theorem element_items_resource_causes (module : runtime.compiler.ExecutableModule) (items start : Usize)
    (startBound : start.val ≤ module.module.env.elements.val.length) :
    runtime.store.instantiate.Store.prepare_instance_loop1 module items (.Ok ()) start
      ⦃ out => ItemSumOutcome (items.val +
        ((module.module.env.elements.val.drop start.val).map fun element => element.init.length).sum) out ⦄ := by
  let total := items.val + ((module.module.env.elements.val.drop start.val).map fun element => element.init.length).sum
  unfold runtime.store.instantiate.Store.prepare_instance_loop1
  apply loop.spec_decr_nat (fun state => module.module.env.elements.val.length - state.2.2.val)
    (fun state => state.2.2.val ≤ module.module.env.elements.val.length ∧
      match state.2.1 with
      | .Ok () => state.1.val + ((module.module.env.elements.val.drop state.2.2.val).map fun element => element.init.length).sum = total
      | .Err error => error = .Exhausted .Objects ∧ Usize.max < total)
  · rintro ⟨current,status,index⟩ ⟨bound,invariant⟩
    dsimp only at bound invariant ⊢
    unfold runtime.store.instantiate.Store.prepare_instance_loop1.body
    simp only [runtime.compiler.ExecutableModule.env,Exec.module.Module.env,
      Itasca.module.Module.impl.env,Exec.module.Env.elements,Itasca.module.Env.impl.elements,bind_ok]
    split
    · rename_i more
      have hmore : index.val < module.module.env.elements.val.length := by simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error => simpa [core.result.Result.is_ok,ItemSumOutcome,total] using invariant
      | Ok value =>
        cases value
        simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
        step as ⟨element,read⟩
        step with add_items_effect current element.init.len as ⟨status,updated,effect⟩
        have max := module.module.env.elements.property
        step as ⟨next,increment⟩
        rw [List.drop_eq_getElem_cons hmore] at invariant
        simp only [List.map_cons,List.sum_cons] at invariant
        refine ⟨?_,?_,?_⟩
        · omega
        · rcases effect with ⟨ok,addition⟩ | ⟨failed,overflow⟩
          · subst status
            rw [read] at addition
            simp [alloc.vec.Vec.deref] at addition
            change updated.val = current.val + module.module.env.elements.val[index.val].init.length at addition
            simpa only [increment] using (by omega : updated.val + ((module.module.env.elements.val.drop (index.val+1)).map fun element => element.init.length).sum = total)
          · cases failed
            rw [read] at overflow
            simp [alloc.vec.Vec.deref] at overflow
            have overflowValue : Usize.max < current.val + module.module.env.elements.val[index.val].init.length := overflow.2
            exact ⟨rfl,by omega⟩
        · omega
    · have equal : index.val = module.module.env.elements.val.length := by simp [alloc.vec.Vec.deref] at *; omega
      cases status with
      | Err error => simpa [ItemSumOutcome,total] using invariant
      | Ok unit => simpa [ItemSumOutcome,equal,total] using invariant
  · exact ⟨startBound,rfl⟩

end Exec.Store

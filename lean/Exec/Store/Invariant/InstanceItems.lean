import Exec.Store.Api.GlobalLoop
import Exec.Store.Initialization.SegmentAccounting

namespace Exec.Store
open Aeneas Aeneas.Std

@[step] theorem add_items_effect (items additional : Usize) :
    runtime.store.add_items items additional ⦃ out =>
      (out.1 = .Ok () ∧ out.2.val = items.val + additional.val) ∨
      (out = (.Err (.Exhausted .Objects), items) ∧ Usize.max < items.val + additional.val) ⦄ := by
  unfold runtime.store.add_items
  step as ⟨total, htotal⟩
  cases total with
  | none => simp only [WP.spec_ok]; exact Or.inr ⟨True.intro, htotal⟩
  | some total => simp only [WP.spec_ok]; exact Or.inl ⟨True.intro, htotal.2.1⟩

theorem item_counts_loop (counts : Array Usize 7#usize) (items start : Usize)
    (startBound : start.val ≤ counts.val.length) :
    runtime.store.instantiate.Store.instantiate_inner_loop0 items (.Ok ()) counts start
      ⦃ out => out.2 = .Ok () → out.1.val = items.val + ((counts.val.drop start.val).map UScalar.val).sum ⦄ := by
  unfold runtime.store.instantiate.Store.instantiate_inner_loop0
  apply loop.spec_decr_nat (fun state => counts.val.length - state.2.2.val)
    (fun state => state.2.2.val ≤ counts.val.length ∧
      (state.2.1 = .Ok () → state.1.val + ((counts.val.drop state.2.2.val).map UScalar.val).sum =
        items.val + ((counts.val.drop start.val).map UScalar.val).sum))
  · rintro ⟨current, status, index⟩ ⟨bound, total⟩
    dsimp only at bound total ⊢
    unfold runtime.store.instantiate.Store.instantiate_inner_loop0.body
    simp only [lift, bind_ok]
    split
    · rename_i more
      have hmore : index.val < counts.val.length := by simpa using more
      cases status with
      | Err error => simp [core.result.Result.is_ok]
      | Ok value =>
        cases value
        have exactTotal := total rfl
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step as ⟨additional, read⟩
        step with add_items_effect current additional as ⟨status, updated, effect⟩
        have max := counts.property
        step as ⟨next, increment⟩
        refine ⟨?_, ?_, ?_⟩
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
      intro success
      have exactTotal := total success
      simpa [equal] using exactTotal
  · exact ⟨startBound, fun _ => rfl⟩

theorem element_items_loop (module : runtime.compiler.ExecutableModule) (items start : Usize)
    (startBound : start.val ≤ module.module.env.elements.val.length) :
    runtime.store.instantiate.Store.instantiate_inner_loop1 module items (.Ok ()) start
      ⦃ out => out.2 = .Ok () → out.1.val = items.val +
        ((module.module.env.elements.val.drop start.val).map fun element => element.init.length).sum ⦄ := by
  unfold runtime.store.instantiate.Store.instantiate_inner_loop1
  apply loop.spec_decr_nat (fun state => module.module.env.elements.val.length - state.2.2.val)
    (fun state => state.2.2.val ≤ module.module.env.elements.val.length ∧
      (state.2.1 = .Ok () → state.1.val +
        ((module.module.env.elements.val.drop state.2.2.val).map fun element => element.init.length).sum =
        items.val + ((module.module.env.elements.val.drop start.val).map fun element => element.init.length).sum))
  · rintro ⟨current, status, index⟩ ⟨bound, total⟩
    dsimp only at bound total ⊢
    unfold runtime.store.instantiate.Store.instantiate_inner_loop1.body
    simp only [runtime.compiler.ExecutableModule.env, Exec.module.Module.env,
      Itasca.module.Module.impl.env, Exec.module.Env.elements, Itasca.module.Env.impl.elements, bind_ok]
    split
    · rename_i more
      have hmore : index.val < module.module.env.elements.val.length := by simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error => simp [core.result.Result.is_ok]
      | Ok value =>
        cases value
        have exactTotal := total rfl
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step as ⟨element, read⟩
        step with add_items_effect current element.init.len as ⟨status, updated, effect⟩
        have max := module.module.env.elements.property
        step as ⟨next, increment⟩
        refine ⟨?_, ?_, ?_⟩
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
      intro success
      have exactTotal := total success
      simpa [equal] using exactTotal
  · exact ⟨startBound, fun _ => rfl⟩

/-- The retained-map charge used by the actual instantiation preflight. -/
def moduleItems (module : runtime.compiler.ExecutableModule) : Nat :=
  module.module.env.types.length + module.module.env.func_types.length +
  module.module.env.table_types.length + module.module.env.mem_types.length +
  module.module.env.global_types.length + module.module.env.elements.length +
  module.module.tail.data.length +
  (module.module.env.elements.val.map fun element => element.init.length).sum

def moduleItemCounts (module : runtime.compiler.ExecutableModule) : Array Usize 7#usize :=
  Array.make 7#usize [module.module.env.types.len, module.module.env.func_types.len,
    module.module.env.table_types.len, module.module.env.mem_types.len,
    module.module.env.global_types.len, module.module.env.elements.len, module.module.tail.data.len]

theorem element_items_error (module : runtime.compiler.ExecutableModule) (items start : Usize)
    (error : runtime.ExecError) :
    runtime.store.instantiate.Store.instantiate_inner_loop1 module items (.Err error) start =
      .ok (items, .Err error) := by
  unfold runtime.store.instantiate.Store.instantiate_inner_loop1
  rw [loop.eq_def]
  simp only [runtime.store.instantiate.Store.instantiate_inner_loop1.body,
    runtime.compiler.ExecutableModule.env, Exec.module.Module.env, Itasca.module.Module.impl.env,
    Exec.module.Env.elements, Itasca.module.Env.impl.elements, bind_ok]
  split <;> simp [core.result.Result.is_ok]

/-- Both actual checked-addition loops either report exhaustion or compute the
exact source-derived charge. This is a totality statement, not a premise that
the preflight has already terminated. -/
theorem instance_item_preflight (module : runtime.compiler.ExecutableModule) :
    (do
      let (items, status) ← runtime.store.instantiate.Store.instantiate_inner_loop0 0#usize (.Ok ())
        (moduleItemCounts module) 0#usize
      runtime.store.instantiate.Store.instantiate_inner_loop1 module items status 0#usize)
      ⦃ out => out.2 = .Ok () → out.1.val = moduleItems module ⦄ := by
  step with item_counts_loop (moduleItemCounts module) 0#usize 0#usize (by simp)
    as ⟨items, status, counted⟩
  cases status with
  | Err error => simp [element_items_error]
  | Ok value =>
    cases value
    have counts := counted rfl
    step with element_items_loop module items 0#usize (by simp) as ⟨out, summed, success⟩
    have result := summed success
    simpa [moduleItemCounts, moduleItems, counts, Array.make, Nat.add_assoc] using result

/-- Passing the actual item limit supplies the store and fresh-instance vector
capacity required by the staged segment loops. Existing segment counts use the
reachable-store accounting invariant, rather than an unproved storage bound. -/
theorem instance_segment_capacity {M : Type} {view : M → Slice U8}
    (store : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (shape : Shape view store) (accounted : SegmentAccounting store)
    (items : Usize) (exactItems : items.val = moduleItems module)
    (fits : store.instance_items.val + items.val ≤ store.limits.max_instance_items.val) :
    store.elems.length + module.module.env.elements.length ≤ Usize.max ∧
    store.datas.length + module.module.tail.data.length ≤ Usize.max ∧
    module.module.env.global_types.length ≤ Usize.max ∧
    module.module.env.elements.length ≤ Usize.max ∧ module.module.tail.data.length ≤ Usize.max := by
  have elementBound := accounted.element_bound shape
  have dataBound := accounted.data_bound shape
  have limit := store.limits.max_instance_items.hmax
  have bounded : store.limits.max_instance_items.val ≤ Usize.max := by scalar_tac
  unfold moduleItems at exactItems
  omega

end Exec.Store

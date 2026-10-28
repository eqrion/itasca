import Itasca.Runtime.Store.Api.GlobalLoop
import Itasca.Runtime.Store.Initialization.SegmentAccounting

namespace Itasca.Runtime.Store
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
    runtime.store.instantiate.Store.prepare_instance_loop1 module items (.Err error) start =
      .ok (items, .Err error) := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop1
  rw [loop.eq_def]
  simp only [runtime.store.instantiate.Store.prepare_instance_loop1.body,
    runtime.compiler.ExecutableModule.env, Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok]
  split <;> simp [core.result.Result.is_ok]

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

end Itasca.Runtime.Store

import Exec.Representation.Collection
import Exec.Store.Initialization.Initializer
import Exec.Interp.Relations.Range

/-! Wasm1 active-segment prechecks evaluate certified constant offsets and check
bounds without modifying a retained object. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem element_bounds_inactive (store : runtime.store.Store M) (platform : P)
    (instIndex index : Usize) (inst : runtime.store.ModuleInst) (segment : Itasca.module.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (inactive : segment.mode = .Passive ∨ segment.mode = .Declarative) :
    runtime.store.instantiate.Store.check_element_bounds memory hooks floats allocator store platform instIndex index
      ⦃ out => out = (.Ok (), store, platform) ⦄ := by
  unfold runtime.store.instantiate.Store.check_element_bounds
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok]
  step with Itasca.Runtime.Representation.slice_index_given inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
  subst found
  rcases inactive with inactive | inactive <;> simp [inactive]

theorem data_bounds_inactive (store : runtime.store.Store M) (platform : P)
    (instIndex index : Usize) (inst : runtime.store.ModuleInst) (segment : Itasca.module.Data)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hdata : inst.module.module.tail.data.val[index.val]? = some segment)
    (inactive : segment.mode = .Passive) :
    runtime.store.instantiate.Store.check_data_bounds memory hooks floats allocator store platform instIndex index
      ⦃ out => out = (.Ok (), store, platform) ⦄ := by
  unfold runtime.store.instantiate.Store.check_data_bounds
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.tail,
    Itasca.module.Module.impl.tail, bind_ok]
  step with Interp.vec_index_given inst.module.module.tail.data index segment hdata as ⟨found, hfound⟩
  subst found
  simp [inactive]

end Itasca.Runtime.Store

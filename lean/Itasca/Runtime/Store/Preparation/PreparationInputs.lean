import Itasca.Runtime.Store.Linking.LinkMaps
import Itasca.Runtime.Store.Invariant.TypeStaging

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- The validator cache bounds every defined function's declared type index;
the type loop's complete map transfers that bound to canonical indices. -/
theorem cache_defined_type_bounds {module : runtime.compiler.ExecutableModule}
    {tables memories} (cache : Cache module.module.env tables memories)
    (indices : alloc.vec.Vec Usize)
    (complete : indices.length = module.module.env.types.length) :
    ∀ idx ∈ module.module.env.func_type_indices.val, idx.val < indices.length := by
  intro idx member
  have allMember : idx ∈ importedFuncs module.module.env.imports.val ++ module.module.env.func_type_indices.val :=
    List.mem_append_right _ member
  obtain ⟨position, bound, found⟩ := List.mem_iff_getElem.mp allMember
  have typeBound : position < module.module.env.func_types.val.length := by rw [← cache.funcs.length_eq]; exact bound
  obtain ⟨resolved, same⟩ := cache.funcs.get bound typeBound
  simp only [List.get_eq_getElem, found] at resolved
  simpa only [complete] using resolved

/-- The issued source environment already bounds the combined imported and
defined function-map length. No extra vector-capacity premise is needed. -/
theorem LinkedMaps.function_capacity {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {module : runtime.compiler.ExecutableModule}
    {inst : runtime.store.ModuleInst}
    (maps : LinkedMaps view store module module.module.env.imports.val inst)
    {tables memories} (cache : Cache module.module.env tables memories) :
    inst.funcs.length + module.module.env.func_type_indices.val.length ≤ Usize.max := by
  have length := cache.funcs.length_eq
  have imported := maps.funcs.length_eq
  have maximum := module.module.env.func_types.property
  simp only [List.length_append] at length
  change inst.funcs.val.length + module.module.env.func_type_indices.val.length ≤ Usize.max
  omega

/-- Once all defined functions are added, the map count is exactly the source
function count used by constant-expression ref.func validation. -/
theorem complete_function_count {module : runtime.compiler.ExecutableModule}
    {tables memories} (cache : Cache module.module.env tables memories)
    (imported defined : Nat) (imports : imported = (importedFuncs module.module.env.imports.val).length)
    (complete : defined = imported + module.module.env.func_type_indices.val.length) :
    defined = module.module.env.func_types.val.length := by
  have length := cache.funcs.length_eq
  simp only [List.length_append] at length
  omega

end Itasca.Runtime.Store

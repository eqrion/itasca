import Exec.Store.Invariant.FunctionSignatureLoop
import Exec.Store.Preparation.PreparationInputs

namespace Exec.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- The actual complete function-allocation loop constructs the full canonical
signature table and exact source-index metadata for every newly staged entry.
Its premises are the maps already established by linking/type interning. -/
theorem prepare_function_signatures {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (instanceIndex : Usize)
    {tables memories} (cache : Cache inst.module.module.env tables memories)
    (objectBound : objectCount store ≤ Usize.max)
    (entries : TypeEntries store inst.module.module.env.types.val inst.types.val)
    (table : Interp.FunctionTable store inst
      ((inst.module.module.env.func_types.val.take (importedFuncs inst.module.module.env.imports.val).length).map decodeFuncType)) :
    runtime.store.instantiate.Store.instantiate_inner_loop4 memory allocator store (.Ok ()) 0#usize inst instanceIndex
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {store with funcs := after.funcs} ∧ next = {inst with funcs := next.funcs} ∧
        StagedPrefix store after ∧ objectCount after ≤ Usize.max ∧
        (status = .Ok () → Interp.FunctionTable after next (inst.module.module.env.func_types.val.map decodeFuncType)) ∧
        StagedFunctionSignatures store after instanceIndex
          (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length) ⦄ := by
  let imported := (importedFuncs inst.module.module.env.imports.val).length
  let defined := inst.module.module.env.func_types.val.drop imported
  have rawLength : imported + inst.module.module.env.func_type_indices.val.length = inst.module.module.env.func_types.val.length := by
    simpa only [List.length_append] using cache.funcs.length_eq
  have initialCount : inst.funcs.length = imported := by
    have same := table.length_eq
    simp only [List.length_map, List.length_take] at same
    change inst.funcs.val.length = imported
    change inst.funcs.val.length = Nat.min imported inst.module.module.env.func_types.val.length at same
    have importedBound : imported ≤ inst.module.module.env.func_types.val.length := by omega
    simpa only [Nat.min_eq_left importedBound] using same
  have capacity : inst.funcs.length + inst.module.module.env.func_type_indices.val.length ≤ Usize.max := by
    rw [initialCount, rawLength]
    exact inst.module.module.env.func_types.property
  have typeBounds := cache_defined_type_bounds cache inst.types entries.length_eq.symm
  have definedResolves : List.Forall₂ (Resolves inst.module.module.env.types.val)
      inst.module.module.env.func_type_indices.val defined := by
    simpa only [defined, imported, List.drop_left] using List.forall₂_drop imported cache.funcs
  have checked := function_signature_loop memory allocator law store store inst inst instanceIndex 0#usize
    (by simp) rfl rfl (.refl _) objectBound typeBounds (function_table_issued table) (by simp) capacity
    ((inst.module.module.env.func_types.val.take imported).map decodeFuncType) defined definedResolves entries
    (by simpa using table) (.refl _ _ _)
  apply WP.spec_mono checked
  rintro out ⟨after, next, status, parts, changed, instChanged, retained, bound, issued, count, complete, staged⟩
  refine ⟨after, next, status, parts, changed, instChanged, retained, bound, ?_, staged⟩
  intro success
  have full := complete success
  simpa only [defined, ← List.map_append, List.take_append_drop] using full

end Exec.Store

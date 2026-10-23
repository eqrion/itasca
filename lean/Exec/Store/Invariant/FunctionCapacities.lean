import Exec.Code.Body.Capacity.FunctionCapacity
import Exec.Representation.Collection
import Exec.Store.Invariant.InstantiationCode
import Exec.Representation.StoreCapacity
namespace Exec.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv

theorem FunctionCapacity.staged {M : Type} {before after : runtime.store.Store M}
    {oldCode newCode : CodeInterpretation} (retained : StagedPrefix before after)
    (agrees : CodeAgreesOn before oldCode newCode) {function : runtime.store.FuncInst}
    (capacity : FunctionCapacity oldCode before function) : FunctionCapacity newCode after function := by
  intro instanceIndex functionIndex defined
  obtain ⟨inst, compiled, typeIndex, found, functionFound, bound, entries, table, signature, typeFound, signatureFound⟩ := capacity instanceIndex functionIndex defined
  refine ⟨inst, compiled, typeIndex, Exec.Representation.lookup_prefix _ _ retained.instances found, functionFound, ?_,
    entries.extend retained, function_table_prefix retained table, signature, typeFound,
    retained.type_lookup signatureFound⟩
  rw [agrees instanceIndex.val inst found functionIndex.val]
  exact bound

/-- Publication retains old bounds and installs the actual compiler's source
frame certificates for every fresh defined function. -/
theorem function_capacities_publish {M : Type}
    (before after : runtime.store.Store M) (oldCode : CodeInterpretation)
    (retained : StagedPrefix before after)
    (oldCapacities : FunctionCapacities oldCode before)
    (inst : runtime.store.ModuleInst) (sources : List funccode)
    (found : after.instances.val[before.instances.len.val]? = some inst)
    (certificate : Code.ModuleCapacities inst.module sources)
    {tables memories} (cache : Cache inst.module.module.env tables memories)
    (entries : TypeEntries after inst.module.module.env.types.val inst.types.val)
    (table : Interp.FunctionTable after inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (staged : StagedFunctionSignatures before after before.instances.len
      (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length)) :
    FunctionCapacities (installCode oldCode before.instances.len.val sources) after := by
  intro function present
  rcases staged function present with old | ⟨index, bound, encoded, signatureFound⟩
  · exact (oldCapacities function old).staged retained (installCode_agrees before oldCode sources)
  · intro instanceIndex functionIndex defined
    obtain ⟨sameInstance, sameFunction⟩ := runtime.store.FuncCode.Wasm.inj (defined.symm.trans encoded)
    subst instanceIndex
    subst functionIndex
    let imported := (importedFuncs inst.module.module.env.imports.val).length
    let definedTypes := inst.module.module.env.func_types.val.drop imported
    have resolves : List.Forall₂ (Resolves inst.module.module.env.types.val)
        inst.module.module.env.func_type_indices.val definedTypes := by
      simpa only [definedTypes, imported, List.drop_left] using List.forall₂_drop imported cache.funcs
    have sourceBound : index.val < inst.module.module.env.func_type_indices.val.length := by
      rw [resolves.length_eq]
      exact bound
    let typeIndex := inst.module.module.env.func_type_indices.val[index.val]
    have sourceIndex : inst.module.module.env.func_type_indices.val[index.val]? = some typeIndex :=
      List.getElem?_eq_getElem sourceBound
    obtain ⟨compiled, source, compiledFound, sourceFound, capacity⟩ := certificate.entry index.val typeIndex sourceIndex
    have resolved := resolves.get sourceBound bound
    simp only [List.get_eq_getElem] at resolved
    obtain ⟨typeBound, resolvedType⟩ := resolved
    have actualType : inst.module.module.env.types.val[typeIndex.val]? = some definedTypes[index.val] := by
      rw [List.getElem?_eq_getElem typeBound, resolvedType]
    refine ⟨inst, compiled, typeIndex, found, compiledFound, ?_, entries, table,
      definedTypes[index.val], actualType, signatureFound⟩
    rw [installCode_lookup oldCode before.instances.len.val sources inst.module index.val source sourceFound]
    exact capacity

theorem InstantiationCode.capacities {M : Type}
    {before ready : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (metadata : InstantiationCode before ready inst) (oldCode : CodeInterpretation)
    (oldCapacities : FunctionCapacities oldCode before)
    (found : ready.instances.val[before.instances.len.val]? = some inst)
    (sources : List funccode) (certificate : Code.ModuleCapacities inst.module sources)
    {tables memories} (cache : Cache inst.module.module.env tables memories) :
    FunctionCapacities (installCode oldCode before.instances.len.val sources) ready := by
  obtain ⟨staged, count, rfl, retained, entries, table, signatures⟩ := metadata
  exact function_capacities_publish before staged oldCode retained oldCapacities inst sources found certificate cache entries table signatures

/-- Updates to runtime contents preserve source frame bounds whenever function
and instance metadata remain equal. -/
theorem FunctionCapacities.metadata {M : Type} {before after : runtime.store.Store M}
    {code : CodeInterpretation} (capacities : FunctionCapacities code before)
    (functions : after.funcs = before.funcs) (instances : after.instances = before.instances)
    (types : after.types = before.types) (identity : after.id = before.id) :
    FunctionCapacities code after := by
  simpa only [FunctionCapacities, FunctionCapacity, TypeEntries, Interp.FunctionTable, functions, instances, types, identity] using capacities

/-- Reassigning code at a fresh instance key preserves all old source bounds. -/
theorem FunctionCapacities.code_agrees {M : Type} {store : runtime.store.Store M}
    {oldCode newCode : CodeInterpretation} (capacities : FunctionCapacities oldCode store)
    (agrees : CodeAgreesOn store oldCode newCode) : FunctionCapacities newCode store := by
  intro function present instanceIndex functionIndex defined
  obtain ⟨inst, compiled, typeIndex, found, functionFound, bound, entries, table, signature, typeFound, signatureFound⟩ :=
    capacities function present instanceIndex functionIndex defined
  refine ⟨inst, compiled, typeIndex, found, functionFound, ?_, entries, table, signature, typeFound, signatureFound⟩
  rw [agrees instanceIndex.val inst found functionIndex.val]
  exact bound
end Exec.Store

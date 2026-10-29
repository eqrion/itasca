import Itasca.Runtime.Store.Invariant.FunctionPayload
import Itasca.Runtime.Spec.Allocation

/-!
Decoded function allocation and source payload lists. The per-function allocation witness establishes the ordered source function-instance list.
-/

/-! ## Function Allocation Decode -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem FunctionAllocatedAt.decode {M : Type}
    {seed : runtime.store.ModuleInst} {instanceIndex : Usize} {ordinal : Nat}
    {function : runtime.store.FuncInst}
    (allocated : FunctionAllocatedAt seed instanceIndex ordinal function)
    (code : CodeInterpretation) (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (types : inst.types = seed.types)
    (source : func) (typeIndex : U32)
    (indexFound : seed.module.module.env.func_type_indices.val[ordinal]? = some typeIndex)
    (sourceIndex : Spec.allocationFunctionIndex source = typeIndex.val)
    (sourceCode : code instanceIndex.val inst.module ordinal = funccode_func source) :
    decodeFunction code store function = Spec.allocationFunction (decodeInstance store inst) source := by
  obtain ⟨index, ordinalEq, encoded, rawIndex, rawFound, signatureFound⟩ := allocated
  have same : rawIndex = typeIndex := Option.some.inj (rawFound.symm.trans indexFound)
  subst rawIndex
  simp only [decodeFunction, encoded, found, ordinalEq, sourceCode, Spec.allocationFunction,
    decodeInstance, sourceIndex, types, List.getElem!_eq_getElem?_getD,
    List.getElem?_map, signatureFound, Option.map_some, Option.getD_some]

end Itasca.Runtime.Store

end

/-! ## Function Source Allocation -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Exact source-ordinal allocation and the installed body interpretation give
all newly allocated source function instances, in declaration order. -/
theorem FunctionPayload.source_list {M : Type} {before after : runtime.store.Store M}
    {seed : runtime.store.ModuleInst} {instanceIndex : Usize}
    (sources : List func)
    (payload : FunctionPayload before after seed instanceIndex sources.length)
    (code : CodeInterpretation) (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (types : inst.types = seed.types)
    (typeIndices : List.Forall₂ (fun index source => index.val = Spec.allocationFunctionIndex source)
      seed.module.module.env.func_type_indices.val sources)
    (sourceCode : ∀ index source, sources[index]? = some source →
      code instanceIndex.val inst.module index = funccode_func source) :
    after.funcs.val.map (decodeFunction code store) = before.funcs.val.map (decodeFunction code store) ++
      sources.map (Spec.allocationFunction (decodeInstance store inst)) := by
  obtain ⟨fresh, stored, paired⟩ := payload
  rw [stored, List.map_append]
  congr 1
  have length : fresh.length = sources.length := by simpa only [List.length_range] using paired.length_eq.symm
  apply List.ext_getElem
  · simpa only [List.length_map] using length
  · intro index leftBound rightBound
    have sourceBound : index < sources.length := by simpa only [List.length_map] using rightBound
    have freshBound : index < fresh.length := by simpa only [List.length_map] using leftBound
    have rawBound : index < seed.module.module.env.func_type_indices.val.length := by
      rw [typeIndices.length_eq]
      exact sourceBound
    have allocated : FunctionAllocatedAt seed instanceIndex index fresh[index] := by
      simpa only [List.get_eq_getElem, List.getElem_range] using paired.get (by simpa using sourceBound) freshBound
    have sourceIndex : Spec.allocationFunctionIndex sources[index] = seed.module.module.env.func_type_indices.val[index].val := by
      have matching := typeIndices.get rawBound sourceBound
      simpa only [List.get_eq_getElem] using matching.symm
    simp only [List.getElem_map]
    exact allocated.decode code store inst found types sources[index]
      seed.module.module.env.func_type_indices.val[index] (List.getElem?_eq_getElem rawBound)
      sourceIndex (sourceCode index sources[index] (List.getElem?_eq_getElem sourceBound))
end Itasca.Runtime.Store

end

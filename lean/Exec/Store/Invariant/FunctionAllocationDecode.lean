import Exec.Store.Invariant.FunctionPayload
import Exec.Spec.Allocation
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

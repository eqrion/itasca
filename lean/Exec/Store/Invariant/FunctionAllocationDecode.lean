import Exec.Store.Invariant.FunctionPayload
import Exec.Spec.Allocation
namespace Exec.Store
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

/-- The actual append ledger determines the decoded suffix once each indexed
entry's type and source body have been attached. This is only a list decoding
lemma; the attachment premise is discharged by `FunctionAllocatedAt.decode`. -/
theorem FunctionPayload.decode {M : Type} {before after : runtime.store.Store M}
    {seed : runtime.store.ModuleInst} {instanceIndex : Usize} {count : Nat}
    (payload : FunctionPayload before after seed instanceIndex count)
    (decode : runtime.store.FuncInst → funcinst) (source : Nat → funcinst)
    (entry : ∀ index function, FunctionAllocatedAt seed instanceIndex index function →
      decode function = source index) :
    after.funcs.val.map decode = before.funcs.val.map decode ++ (List.range count).map source := by
  obtain ⟨fresh, stored, paired⟩ := payload
  rw [stored, List.map_append]
  congr 1
  have mapped : ∀ indices functions,
      List.Forall₂ (FunctionAllocatedAt seed instanceIndex) indices functions →
      functions.map decode = indices.map source := by
    intro indices functions paired
    induction paired with
    | nil => rfl
    | cons current rest ih => simp only [List.map_cons, entry _ _ current, ih]
  exact mapped _ _ paired
end Exec.Store

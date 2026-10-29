import Itasca.Runtime.Store.Invariant.FunctionSourceAllocation
import Itasca.Runtime.Store.Invariant.FunctionTables
import Itasca.Runtime.Compiler.Local.Source.SourceSlice
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca

/-- Independent source declaration order agrees with the actual raw type-index
vector; equal section counts exclude zip truncation. -/
theorem source_function_type_indices (indices : List U32) (entries : List ModuleBinary.Code)
    (lengths : indices.length = entries.length) :
    List.Forall₂ (fun index source => index.val = Spec.allocationFunctionIndex source)
      indices (List.zipWith CodeEntry.function indices entries) := by
  induction indices generalizing entries with
  | nil => cases entries <;> simp_all
  | cons index indices ih =>
    cases entries with
    | nil => simp at lengths
    | cons entry entries =>
      have tail : indices.length = entries.length := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using lengths
      exact .cons rfl (ih entries tail)

@[simp] theorem source_function_code (source : func) : Compiler.functionCode source = funccode_func source := by
  cases source <;> rfl

theorem installed_source_function (code : CodeInterpretation) (instanceIndex : Nat)
    (module : runtime.compiler.ExecutableModule) (raw : ModuleBinary.Module)
    (index : Nat) (source : func)
    (found : (List.zipWith CodeEntry.function raw.functions raw.codes)[index]? = some source) :
    installCode code instanceIndex (Compiler.sourceFunctions raw) instanceIndex module index = funccode_func source := by
  apply install_code_lookup
  simp only [Compiler.source_functions_eq, List.getElem?_map, found, Option.map_some, source_function_code]

theorem canonical_function_payload_decode {M : Type} {before after : runtime.store.Store M}
    {seed : runtime.store.ModuleInst} {instanceIndex : Usize}
    (raw : ModuleBinary.Module)
    (lengths : raw.functions.length = raw.codes.length)
    (indices : seed.module.module.env.func_type_indices.val = raw.functions)
    (payload : FunctionPayload before after seed instanceIndex raw.functions.length)
    (code : CodeInterpretation) (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (types : inst.types = seed.types) :
    after.funcs.val.map (decodeFunction (installCode code instanceIndex.val (Compiler.sourceFunctions raw)) store) =
      before.funcs.val.map (decodeFunction (installCode code instanceIndex.val (Compiler.sourceFunctions raw)) store) ++
      (List.zipWith CodeEntry.function raw.functions raw.codes).map
        (Spec.allocationFunction (decodeInstance store inst)) := by
  apply FunctionPayload.source_list _ ?_ _ store inst found types ?_ ?_
  · simpa only [List.length_zipWith, lengths, Nat.min_self] using payload
  · rw [indices]
    exact source_function_type_indices raw.functions raw.codes lengths
  · exact installed_source_function code instanceIndex.val inst.module raw
end Itasca.Runtime.Store

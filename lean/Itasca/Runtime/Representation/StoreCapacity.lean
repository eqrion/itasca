import Itasca.Runtime.Representation.TypeEntries
import Itasca.Runtime.Representation.FunctionTable
import Itasca.Runtime.Representation.FunctionCapacity

/-!
Source frame capacities for issued functions and decoded store signatures. Interpreter resource causes and store invariants share these certificates.
-/

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
/-- Every defined function has a source-derived static frame requirement.
Host functions impose no Wasm frame requirement. -/
def FunctionCapacity {M : Type} (code : CodeInterpretation) (store : runtime.store.Store M)
    (function : runtime.store.FuncInst) : Prop :=
  ∀ instanceIndex functionIndex, function.code = .Wasm instanceIndex functionIndex →
    ∃ inst compiled typeIndex,
      store.instances.val[instanceIndex.val]? = some inst ∧
      inst.module.functions.val[functionIndex.val]? = some compiled ∧
      Code.FunctionCapacity inst.module.profile inst.module.module.env typeIndex
        (code instanceIndex.val inst.module functionIndex.val) compiled ∧
      TypeEntries store inst.module.module.env.types.val inst.types.val ∧
      Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType) ∧
      ∃ signature, inst.module.module.env.types.val[typeIndex.val]? = some signature ∧
        store.types.val[function.signature.val]? = some signature

/-- Static source frame bounds for all issued defined functions. -/
def FunctionCapacities {M : Type} (code : CodeInterpretation) (store : runtime.store.Store M) : Prop :=
  ∀ function ∈ store.funcs.val, FunctionCapacity code store function

/-- Canonical type indices decode to exactly the source validation table. -/
theorem TypeEntries.capacity_decode {M : Type} {store : runtime.store.Store M}
    {source : List Itasca.types.FuncType} {indices : List Usize}
    (entries : TypeEntries store source indices) :
    indices.map (fun index => (store.types.val.map decodeFuncType).getD index.val default) =
      source.map decodeFuncType := by
  induction entries with
  | nil => rfl
  | @cons ty index types indices found rest ih =>
    simp only [List.map_cons]
    rw [ih]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, found, Option.map_some, Option.getD_some]

end Itasca.Runtime.Store

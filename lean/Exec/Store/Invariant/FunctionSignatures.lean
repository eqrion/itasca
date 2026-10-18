import Exec.Store.Invariant.FunctionTables
import Exec.Store.Invariant.FunctionStaging

namespace Exec.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Successful defined-function insertion extends the concrete signature table
by the exact canonical signature stored in the new function entry. -/
theorem FunctionStageEffect.function_table {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.Instance} {instanceIndex index signature out}
    (effect : FunctionStageEffect store inst instanceIndex index signature out)
    {types : List functype} (table : Interp.FunctionTable store inst types)
    {rawType : Itasca.types.FuncType} (typed : store.types.val[signature.val]? = some rawType)
    (success : out.1 = .Ok ()) :
    Interp.FunctionTable out.2.1 out.2.2 (types ++ [decodeFuncType rawType]) := by
  rcases effect with ⟨error, rfl⟩ | ⟨functions, addresses, appended, mapped, capacity, rfl⟩
  · simp at success
  · have retained : StagedPrefix store {store with funcs := functions} := by
      constructor <;> simp [appended]
    have oldTable := function_table_prefix retained table
    change List.Forall₂ _ addresses.val _
    rw [mapped]
    apply List.rel_append oldTable
    refine .cons ⟨rfl, {signature, code := .Wasm instanceIndex index}, rawType, ?_, typed, rfl⟩ .nil
    simp [appended]

/-- Canonical type-map lookup follows the source type relation through the
actual instance map; no equality of unchecked type indices is assumed. -/
theorem type_entries_resolve {M : Type} {store : runtime.store.Store M}
    {source : List Itasca.types.FuncType} {indices : List Usize}
    (entries : TypeEntries store source indices) (index : U32) (ty : Itasca.types.FuncType)
    (resolved : Resolves source index ty) :
    ∃ bound : index.val < indices.length,
      store.types.val[indices[index.val].val]? = some ty := by
  obtain ⟨sourceBound, same⟩ := resolved
  have bound : index.val < indices.length := by rw [← entries.length_eq]; exact sourceBound
  refine ⟨bound, ?_⟩
  have found := entries.get sourceBound bound
  simpa only [List.get_eq_getElem, same] using found

/-- Every staged function is either an existing entry or a new defined entry
with its exact source-function index and canonical raw signature. -/
def StagedFunctionSignatures {M : Type} (before after : runtime.store.Store M)
    (instanceIndex : Usize) (definedTypes : List Itasca.types.FuncType) : Prop :=
  ∀ function ∈ after.funcs.val, function ∈ before.funcs.val ∨
    ∃ index : Usize, ∃ bound : index.val < definedTypes.length,
      function.code = .Wasm instanceIndex index ∧
      after.types.val[function.signature.val]? = some definedTypes[index.val]

theorem StagedFunctionSignatures.refl {M : Type} (store : runtime.store.Store M)
    (instanceIndex : Usize) (definedTypes : List Itasca.types.FuncType) :
    StagedFunctionSignatures store store instanceIndex definedTypes := fun _ present => .inl present

theorem StagedFunctionSignatures.extend {M : Type} {before store after : runtime.store.Store M}
    {instanceIndex : Usize} {definedTypes : List Itasca.types.FuncType}
    (staged : StagedFunctionSignatures before store instanceIndex definedTypes)
    (retained : StagedPrefix store after) (functions : after.funcs = store.funcs) :
    StagedFunctionSignatures before after instanceIndex definedTypes := by
  intro function present
  rw [functions] at present
  rcases staged function present with old | ⟨index, bound, code, signature⟩
  · exact .inl old
  · exact .inr ⟨index, bound, code, retained.type_lookup signature⟩

theorem StagedFunctionSignatures.rebase {M : Type} {before stagedFrom after : runtime.store.Store M}
    {instanceIndex : Usize} {definedTypes : List Itasca.types.FuncType}
    (functions : stagedFrom.funcs = before.funcs)
    (staged : StagedFunctionSignatures stagedFrom after instanceIndex definedTypes) :
    StagedFunctionSignatures before after instanceIndex definedTypes := by
  simpa only [StagedFunctionSignatures, functions] using staged

/-- Defined-function allocation records the compiler index and signature even
when a later function allocation rejects and the public wrapper rolls back. -/
theorem FunctionStageEffect.signatures {M : Type} {before store : runtime.store.Store M}
    {inst : runtime.store.Instance} {instanceIndex index signature out}
    (effect : FunctionStageEffect store inst instanceIndex index signature out)
    {definedTypes : List Itasca.types.FuncType}
    (staged : StagedFunctionSignatures before store instanceIndex definedTypes)
    (bound : index.val < definedTypes.length)
    (typed : store.types.val[signature.val]? = some definedTypes[index.val]) :
    StagedFunctionSignatures before out.2.1 instanceIndex definedTypes := by
  rcases effect with ⟨error, rfl⟩ | ⟨functions, addresses, appended, mapped, capacity, rfl⟩
  · exact staged
  · intro function present
    change function ∈ functions.val at present
    rw [appended] at present
    rcases List.mem_append.mp present with old | fresh
    · exact staged function old
    · have same : function = {signature, code := .Wasm instanceIndex index} := List.mem_singleton.mp fresh
      subst function
      exact .inr ⟨index, bound, rfl, typed⟩

/-- The actual canonical type map decodes to its source signature list. -/
theorem type_entries_decoded {M : Type} {store : runtime.store.Store M}
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

end Exec.Store

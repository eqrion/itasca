import Itasca.Runtime.Store.Invariant.CodeAgreement
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Equations
import Itasca.Generated.Types

/-!
Sections, each formerly its own module: FunctionSignatures, InstantiationCode, NormalResult, PrecommitError.
-/

/-! ## FunctionSignatures -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Successful defined-function insertion extends the concrete signature table
by the exact canonical signature stored in the new function entry. -/
theorem FunctionStageEffect.function_table {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {instanceIndex index signature out}
    (effect : FunctionStageEffect store inst instanceIndex index signature out)
    {types : List functype} (table : Interp.FunctionTable store inst types)
    {rawType : Itasca.wasm_types.FuncType} (typed : store.types.val[signature.val]? = some rawType)
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
    {source : List Itasca.wasm_types.FuncType} {indices : List Usize}
    (entries : TypeEntries store source indices) (index : U32) (ty : Itasca.wasm_types.FuncType)
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
    (instanceIndex : Usize) (definedTypes : List Itasca.wasm_types.FuncType) : Prop :=
  ∀ function ∈ after.funcs.val, function ∈ before.funcs.val ∨
    ∃ index : Usize, ∃ bound : index.val < definedTypes.length,
      function.code = .Wasm instanceIndex index ∧
      after.types.val[function.signature.val]? = some definedTypes[index.val]

theorem StagedFunctionSignatures.refl {M : Type} (store : runtime.store.Store M)
    (instanceIndex : Usize) (definedTypes : List Itasca.wasm_types.FuncType) :
    StagedFunctionSignatures store store instanceIndex definedTypes := fun _ present => .inl present

theorem StagedFunctionSignatures.extend {M : Type} {before store after : runtime.store.Store M}
    {instanceIndex : Usize} {definedTypes : List Itasca.wasm_types.FuncType}
    (staged : StagedFunctionSignatures before store instanceIndex definedTypes)
    (retained : StagedPrefix store after) (functions : after.funcs = store.funcs) :
    StagedFunctionSignatures before after instanceIndex definedTypes := by
  intro function present
  rw [functions] at present
  rcases staged function present with old | ⟨index, bound, code, signature⟩
  · exact .inl old
  · exact .inr ⟨index, bound, code, retained.type_lookup signature⟩

theorem StagedFunctionSignatures.rebase {M : Type} {before stagedFrom after : runtime.store.Store M}
    {instanceIndex : Usize} {definedTypes : List Itasca.wasm_types.FuncType}
    (functions : stagedFrom.funcs = before.funcs)
    (staged : StagedFunctionSignatures stagedFrom after instanceIndex definedTypes) :
    StagedFunctionSignatures before after instanceIndex definedTypes := by
  simpa only [StagedFunctionSignatures, functions] using staged

/-- Defined-function allocation records the compiler index and signature even
when a later function allocation rejects and the public wrapper rolls back. -/
theorem FunctionStageEffect.signatures {M : Type} {before store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {instanceIndex index signature out}
    (effect : FunctionStageEffect store inst instanceIndex index signature out)
    {definedTypes : List Itasca.wasm_types.FuncType}
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
    {source : List Itasca.wasm_types.FuncType} {indices : List Usize}
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

end

/-! ## InstantiationCode -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Concrete code-address metadata produced by preparation and staging. The
provisional witness differs only in the committed resource counter, allowing
old code retention to use exact precharge vector prefixes. This contains no
assumption about execution of the installed functions. -/
def InstantiationCode {M : Type} (before ready : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) : Prop :=
  ∃ staged count, ready = {staged with instance_items := count} ∧
    StagedPrefix before staged ∧
    TypeEntries staged inst.module.module.env.types.val inst.types.val ∧
    Interp.FunctionTable staged inst (inst.module.module.env.func_types.val.map decodeFuncType) ∧
    StagedFunctionSignatures before staged before.instances.len
      (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length)

theorem InstantiationCode.type_entries {M : Type} {before ready : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} (code : InstantiationCode before ready inst) :
    TypeEntries ready inst.module.module.env.types.val inst.types.val := by
  obtain ⟨staged, count, rfl, _, entries, _, _⟩ := code
  exact entries

theorem InstantiationCode.function_table {M : Type} {before ready : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} (code : InstantiationCode before ready inst) :
    Interp.FunctionTable ready inst (inst.module.module.env.func_types.val.map decodeFuncType) := by
  obtain ⟨staged, count, rfl, _, _, table, _⟩ := code
  exact table

end Itasca.Runtime.Store

end

/-! ## NormalResult -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- An immediate normal return of a bind requires an immediate normal return
of its input and the same normal result from the continuation. Effects and
divergence cannot be discarded by binding. -/
theorem normal_bind_exists {α β : Type} (input : Result α) (next : α → Result β)
    (output : β) (run : Aeneas.Std.bind input next = .ok output) :
    ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input with
  | ret value => exact ⟨value, rfl, by simpa only [bind_ok] using run⟩
  | vis effect continuation => simp only [bind_vis, vis_not_ok] at run
  | div => simp only [bind_div, div_not_ok] at run

end Itasca.Runtime.Store

end

/-! ## PrecommitError -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The only ordinary failure class available while allocating a certified
initializer or staging a store object. -/
def ResourceError : runtime.ExecError → Prop
  | .Exhausted _ => True
  | _ => False

def ErrorAllowed {α : Type} (allowed : runtime.ExecError → Prop) : core.result.Result α runtime.ExecError → Prop
  | .Ok _ => True
  | .Err error => allowed error

/-- Precommit rejections are linking, foreign-store handles, or embedding-resource
failures. Segment traps arise only after publication. -/
def PrecommitError : runtime.ExecError → Prop
  | .Link _ => True
  | .WrongStore => True
  | .Exhausted _ => True
  | _ => False

theorem ResourceError.precommit {error} (resource : ResourceError error) : PrecommitError error := by
  cases error <;> simp_all [ResourceError, PrecommitError]

end Itasca.Runtime.Store

end

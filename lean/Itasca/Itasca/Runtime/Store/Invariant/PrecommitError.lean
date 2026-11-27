import Itasca.Runtime.Store.Definitions
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Store.Linking.LinkedOwners
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Interp.Relations.ReadbackAndBindings
import Itasca.Runtime.Compiler.Local.Relations.Function.RootLabel
import Itasca.Runtime.Equations.Interp
import ItascaRust.Types

/-!
Proofs for Runtime / Store / Invariant.

This module collects CodeAgreement, PrecommitError.
Each section documents its contracts and consumers.
-/

/-! ## CodeAgreement -/

section

open Itasca.Representation

/-! ## FunctionTables -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Module.Environment

theorem StagedPrefix.type_lookup {M : Type} {before after : runtime.store.Store M}
    (retained : StagedPrefix before after) {index : Nat} {ty : Itasca.wasm_types.FuncType}
    (found : before.types.val[index]? = some ty) : after.types.val[index]? = some ty :=
  Itasca.Representation.lookup_prefix _ _ retained.types found

/-- Updating unrelated instance maps does not change its function signatures. -/
theorem function_table_instance {M : Type} {store : runtime.store.Store M}
    {before after : runtime.store.ModuleInst} {types : List functype}
    (functions : after.funcs = before.funcs) (table : Representation.FunctionTable store before types) :
    Representation.FunctionTable store after types := by
  simpa only [Representation.FunctionTable, functions] using table

/-- Signature lookup tables survive extension of all raw store vectors. -/
theorem function_table_prefix {M : Type} {before after : runtime.store.Store M}
    (retained : StagedPrefix before after) {inst : runtime.store.ModuleInst} {types : List functype}
    (table : Representation.FunctionTable before inst types) : Representation.FunctionTable after inst types := by
  apply table.imp
  intro address ty matching
  obtain ⟨owner, function, signature, found, signatureFound, decoded⟩ := matching
  exact ⟨owner.trans retained.identity.symm, function, signature,
    Itasca.Representation.lookup_prefix _ _ retained.funcs found, Itasca.Representation.lookup_prefix _ _ retained.types signatureFound, decoded⟩

/-- Every address in a concrete signature table denotes an existing function. -/
theorem function_table_issued {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {types : List functype}
    (table : Representation.FunctionTable store inst types) :
    ∀ address ∈ inst.funcs.val, address.index.val < store.funcs.length := by
  intro address present
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp present
  have typeBound : index < types.length := by rw [← table.length_eq]; exact bound
  obtain ⟨owner, function, signature, found, signatureFound, decoded⟩ := table.get bound typeBound
  simp only [List.get_eq_getElem, same] at found
  exact (List.getElem?_eq_some_iff.mp found).1

/-- A linked function import has exactly the signature resolved by the source
module's canonical type cache. -/
theorem ImportedFunction.signature {M : Type} {store : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {typeIndex : U32} {address : runtime.FuncAddr}
    (linked : ImportedFunction store module typeIndex address) {ty : Itasca.wasm_types.FuncType}
    (resolved : Resolves module.module.env.types.val typeIndex ty) :
    address.store = store.id ∧ ∃ function,
      store.funcs.val[address.index.val]? = some function ∧
      store.types.val[function.signature.val]? = some ty := by
  obtain ⟨owner, function, actual, found, signatureFound, source⟩ := linked
  obtain ⟨bound, same⟩ := resolved
  have sourceExpected : module.module.env.types.val[typeIndex.val]? = some ty := by
    rw [List.getElem?_eq_getElem bound, same]
  have actualEq : actual = ty := Option.some.inj (source.symm.trans sourceExpected)
  subst actual
  exact ⟨owner, function, found, signatureFound⟩

private theorem imports_table {M : Type} {store : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {indices : List U32} {addresses : List runtime.FuncAddr}
    (linked : List.Forall₂ (ImportedFunction store module) indices addresses)
    {types : List Itasca.wasm_types.FuncType}
    (resolved : List.Forall₂ (Resolves module.module.env.types.val) indices types) :
    List.Forall₂ (fun address ty => address.store = store.id ∧
      ∃ function signature, store.funcs.val[address.index.val]? = some function ∧
        store.types.val[function.signature.val]? = some signature ∧ Itasca.Translation.Environment.funcType signature = ty)
      addresses (types.map Itasca.Translation.Environment.funcType) := by
  induction linked generalizing types with
  | nil => cases resolved; exact .nil
  | cons current rest ih =>
    cases resolved with
    | cons head tail =>
      obtain ⟨owner, function, found, signature⟩ := current.signature head
      exact .cons ⟨owner, function, _, found, signature, rfl⟩ (ih tail)

/-- Completed linking constructs the interpreter's actual signature table for
the imported function prefix, directly from the validator's canonical cache. -/
theorem LinkedMaps.function_table {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {inst : runtime.store.ModuleInst}
    (maps : LinkedMaps view store module module.module.env.imports.val inst)
    {tables memories} (cache : Cache module.module.env tables memories) :
    Representation.FunctionTable store inst
      ((module.module.env.func_types.val.take (importedFuncs module.module.env.imports.val).length).map Itasca.Translation.Environment.funcType) := by
  apply imports_table maps.funcs
  have resolvedPrefix := List.forall₂_take (importedFuncs module.module.env.imports.val).length cache.funcs
  simpa only [List.take_left] using resolvedPrefix

theorem install_code_agrees {M : Type} (store : runtime.store.Store M)
    (before : CodeInterpretation) (source : List funccode) :
    CodeAgreesOn store before (installCode before store.instances.length source) := by
  intro index inst found function
  have bound := (List.getElem?_eq_some_iff.mp found).1
  simp only [installCode, if_neg (Nat.ne_of_lt bound)]

theorem install_code_lookup (before : CodeInterpretation) (fresh : Nat)
    (source : List funccode) (module : runtime.compiler.ExecutableModule)
    (index : Nat) (function : funccode) (found : source[index]? = some function) :
    installCode before fresh source fresh module index = function := by
  simp only [installCode, ↓reduceIte, List.getD_eq_getElem?_getD, found, Option.getD_some]

end Itasca.Store

end

/-! ## CodeAgreement -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Assigning source code at fresh instance keys leaves every existing
function's decoded source unchanged, including absent-instance fallbacks. -/
theorem decode_function_code_agrees {M : Type} {store : runtime.store.Store M}
    {before after : CodeInterpretation} (agrees : CodeAgreesOn store before after)
    (function : runtime.store.FuncInst) :
    decodeFunction after store function = decodeFunction before store function := by
  cases kind : function.code with
  | Host id => simp only [decodeFunction, kind]
  | Wasm index fn =>
    cases found : store.instances.val[index.val]? with
    | none => simp only [decodeFunction, kind, found]
    | some inst => simp only [decodeFunction, kind, found, agrees index.val inst found fn.val]

theorem decode_store_code_agrees {M : Type} (view : M → Slice U8)
    {store : runtime.store.Store M} {before after : CodeInterpretation}
    (agrees : CodeAgreesOn store before after) :
    decodeStore view after store = decodeStore view before store := by
  have functions : store.funcs.val.map (decodeFunction after store) =
      store.funcs.val.map (decodeFunction before store) := by
    apply List.map_congr_left
    intro function _
    exact decode_function_code_agrees agrees function
  unfold decodeStore
  rw [functions]

end Itasca.Store

end

end

/-! ## PrecommitError -/

section

open Itasca.Representation

/-! ## FunctionSignatures -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Module.Environment

/-- Successful defined-function insertion extends the concrete signature table
by the exact canonical signature stored in the new function entry. -/
theorem FunctionStageEffect.function_table {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {instanceIndex index signature out}
    (effect : FunctionStageEffect store inst instanceIndex index signature out)
    {types : List functype} (table : Representation.FunctionTable store inst types)
    {rawType : Itasca.wasm_types.FuncType} (typed : store.types.val[signature.val]? = some rawType)
    (success : out.1 = .Ok ()) :
    Representation.FunctionTable out.2.1 out.2.2 (types ++ [Itasca.Translation.Environment.funcType rawType]) := by
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
    indices.map (fun index => (store.types.val.map Itasca.Translation.Environment.funcType).getD index.val default) =
      source.map Itasca.Translation.Environment.funcType := by
  induction entries with
  | nil => rfl
  | @cons ty index types indices found rest ih =>
    simp only [List.map_cons]
    rw [ih]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, found, Option.map_some, Option.getD_some]

end Itasca.Store

end

/-! ## InstantiationCode -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std
open Itasca.Module.Environment

/-- Concrete code-address metadata produced by preparation and staging. The
provisional witness differs only in the committed resource counter, allowing
old code retention to use exact precharge vector prefixes. This contains no
assumption about execution of the installed functions. -/
def InstantiationCode {M : Type} (before ready : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) : Prop :=
  ∃ staged count, ready = {staged with instance_items := count} ∧
    StagedPrefix before staged ∧
    TypeEntries staged inst.module.module.env.types.val inst.types.val ∧
    Representation.FunctionTable staged inst (inst.module.module.env.func_types.val.map Itasca.Translation.Environment.funcType) ∧
    StagedFunctionSignatures before staged before.instances.len
      (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length)

theorem InstantiationCode.type_entries {M : Type} {before ready : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} (code : InstantiationCode before ready inst) :
    TypeEntries ready inst.module.module.env.types.val inst.types.val := by
  obtain ⟨staged, count, rfl, _, entries, _, _⟩ := code
  exact entries

theorem InstantiationCode.function_table {M : Type} {before ready : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} (code : InstantiationCode before ready inst) :
    Representation.FunctionTable ready inst (inst.module.module.env.func_types.val.map Itasca.Translation.Environment.funcType) := by
  obtain ⟨staged, count, rfl, _, _, table, _⟩ := code
  exact table

end Itasca.Store

end

/-! ## NormalResult -/

section

namespace Itasca.Store
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

end Itasca.Store

end

/-! ## PrecommitError -/

section

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- The only ordinary failure class available while allocating a certified
initializer or staging a store object. -/
def ResourceError : runtime.ExecError → Prop
  | .Exhausted _ => True
  | _ => False

def ErrorAllowed {α : Type} (allowed : runtime.ExecError → Prop) : core.result.Result α runtime.ExecError → Prop
  | .Ok _ => True
  | .Err error => allowed error

theorem ResourceError.precommit {error} (resource : ResourceError error) : PrecommitError error := by
  cases error <;> simp_all [ResourceError, PrecommitError]

end Itasca.Store

end

end

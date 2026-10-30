import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Store.Linking.LinkMaps
import Itasca.Runtime.Store.Invariant.Extension
import Itasca.Runtime.Interp.Relations.CompiledFunctions

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

theorem StagedPrefix.type_lookup {M : Type} {before after : runtime.store.Store M}
    (retained : StagedPrefix before after) {index : Nat} {ty : Itasca.wasm_types.FuncType}
    (found : before.types.val[index]? = some ty) : after.types.val[index]? = some ty :=
  Itasca.Runtime.Representation.lookup_prefix _ _ retained.types found

/-- Updating unrelated instance maps does not change its function signatures. -/
theorem function_table_instance {M : Type} {store : runtime.store.Store M}
    {before after : runtime.store.ModuleInst} {types : List functype}
    (functions : after.funcs = before.funcs) (table : Interp.FunctionTable store before types) :
    Interp.FunctionTable store after types := by
  simpa only [Interp.FunctionTable, functions] using table

/-- Signature lookup tables survive extension of all raw store vectors. -/
theorem function_table_prefix {M : Type} {before after : runtime.store.Store M}
    (retained : StagedPrefix before after) {inst : runtime.store.ModuleInst} {types : List functype}
    (table : Interp.FunctionTable before inst types) : Interp.FunctionTable after inst types := by
  apply table.imp
  intro address ty matching
  obtain ⟨owner, function, signature, found, signatureFound, decoded⟩ := matching
  exact ⟨owner.trans retained.identity.symm, function, signature,
    Itasca.Runtime.Representation.lookup_prefix _ _ retained.funcs found, Itasca.Runtime.Representation.lookup_prefix _ _ retained.types signatureFound, decoded⟩

/-- Every address in a concrete signature table denotes an existing function. -/
theorem function_table_issued {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {types : List functype}
    (table : Interp.FunctionTable store inst types) :
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
        store.types.val[function.signature.val]? = some signature ∧ decodeFuncType signature = ty)
      addresses (types.map decodeFuncType) := by
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
    Interp.FunctionTable store inst
      ((module.module.env.func_types.val.take (importedFuncs module.module.env.imports.val).length).map decodeFuncType) := by
  apply imports_table maps.funcs
  have resolvedPrefix := List.forall₂_take (importedFuncs module.module.env.imports.val).length cache.funcs
  simpa only [List.take_left] using resolvedPrefix

/-- New ghost code assignments agree on every already issued instance. This is
source syntax correspondence, not an execution theorem. -/
def CodeAgreesOn {M : Type} (store : runtime.store.Store M)
    (before after : CodeInterpretation) : Prop :=
  ∀ index inst, store.instances.val[index]? = some inst →
    ∀ function, after index inst.module function = before index inst.module function

/-- Install the source code for a fresh instance. Existing instance keys retain
their previous interpretation even when their compiled modules coincide. -/
def installCode (before : CodeInterpretation) (fresh : Nat) (source : List funccode) : CodeInterpretation :=
  fun index module function => if index = fresh then source.getD function default else before index module function

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

end Itasca.Runtime.Store

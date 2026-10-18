import Exec.Representation.Collection
import Exec.Store.Linking.LinkMaps
import Exec.Store.Invariant.Extension
import Exec.Interp.Relations.CompiledFunctions

namespace Exec.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

theorem StagedPrefix.type_lookup {M : Type} {before after : runtime.store.Store M}
    (retained : StagedPrefix before after) {index : Nat} {ty : Itasca.types.FuncType}
    (found : before.types.val[index]? = some ty) : after.types.val[index]? = some ty :=
  Exec.Representation.lookup_prefix _ _ retained.types found

/-- Updating unrelated instance maps does not change its function signatures. -/
theorem function_table_instance {M : Type} {store : runtime.store.Store M}
    {before after : runtime.store.Instance} {types : List functype}
    (functions : after.funcs = before.funcs) (table : Interp.FunctionTable store before types) :
    Interp.FunctionTable store after types := by
  simpa only [Interp.FunctionTable, functions] using table

/-- Signature lookup tables survive extension of all raw store vectors. -/
theorem function_table_prefix {M : Type} {before after : runtime.store.Store M}
    (retained : StagedPrefix before after) {inst : runtime.store.Instance} {types : List functype}
    (table : Interp.FunctionTable before inst types) : Interp.FunctionTable after inst types := by
  apply table.imp
  intro address ty matching
  obtain ⟨owner, function, signature, found, signatureFound, decoded⟩ := matching
  exact ⟨owner.trans retained.identity.symm, function, signature,
    Exec.Representation.lookup_prefix _ _ retained.funcs found, Exec.Representation.lookup_prefix _ _ retained.types signatureFound, decoded⟩

/-- Every address in a concrete signature table denotes an existing function. -/
theorem function_table_issued {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.Instance} {types : List functype}
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
    (linked : ImportedFunction store module typeIndex address) {ty : Itasca.types.FuncType}
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
    {types : List Itasca.types.FuncType}
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
    {module : runtime.compiler.ExecutableModule} {inst : runtime.store.Instance}
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

/-- Existing compiled functions retain their lookup, source, and compiler
certificates when store vectors and the ghost code interpretation extend. -/
theorem function_compiled_prefix {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} {oldCode newCode : CodeInterpretation}
    (shape : Shape view before) (retained : StagedPrefix before after)
    (agrees : CodeAgreesOn before oldCode newCode) {function : runtime.store.Function}
    (compiled : Interp.FunctionCompiled oldCode before function) :
    Interp.FunctionCompiled newCode after function := by
  intro instanceIndex functionIndex defined
  obtain ⟨inst, code, signature, functions, declared, body, epilogue,
    found, functionFound, signatureFound, source, table, certificate⟩ := compiled instanceIndex functionIndex defined
  refine ⟨inst, code, signature, functions, declared, body, epilogue,
    Exec.Representation.lookup_prefix _ _ retained.instances found, functionFound,
    Exec.Representation.lookup_prefix _ _ retained.types signatureFound, ?_, function_table_prefix retained table, ?_⟩
  · rw [agrees instanceIndex.val inst found functionIndex.val]
    exact source
  · rw [decodeInstance_prefix before after retained inst (shape.instances inst (List.mem_of_getElem? found))]
    exact certificate

/-- Install the source code for a fresh instance. Existing instance keys retain
their previous interpretation even when their compiled modules coincide. -/
def installCode (before : CodeInterpretation) (fresh : Nat) (source : List funccode) : CodeInterpretation :=
  fun index module function => if index = fresh then source.getD function default else before index module function

theorem installCode_agrees {M : Type} (store : runtime.store.Store M)
    (before : CodeInterpretation) (source : List funccode) :
    CodeAgreesOn store before (installCode before store.instances.length source) := by
  intro index inst found function
  have bound := (List.getElem?_eq_some_iff.mp found).1
  simp only [installCode, if_neg (Nat.ne_of_lt bound)]

theorem installCode_lookup (before : CodeInterpretation) (fresh : Nat)
    (source : List funccode) (module : runtime.compiler.ExecutableModule)
    (index : Nat) (function : funccode) (found : source[index]? = some function) :
    installCode before fresh source fresh module index = function := by
  simp only [installCode, ↓reduceIte, List.getD_eq_getElem?_getD, found, Option.getD_some]

/-- Aggregate preservation for all old function entries. Fresh defined entries
are discharged separately from their source-index and compiler certificates. -/
theorem compiled_functions_retained {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} {oldCode newCode : CodeInterpretation}
    (shape : Shape view before) (retained : StagedPrefix before after)
    (agrees : CodeAgreesOn before oldCode newCode)
    (compiled : Interp.CompiledFunctions oldCode before) :
    ∀ function ∈ before.funcs.val, Interp.FunctionCompiled newCode after function := by
  intro function present
  exact function_compiled_prefix shape retained agrees (compiled function present)

/-- Compiler coverage depends only on function/signature/instance metadata.
Memory, table, and global content changes therefore preserve it. -/
theorem compiled_functions_metadata {M : Type} {before after : runtime.store.Store M}
    (code : CodeInterpretation) (identity : after.id = before.id)
    (functions : after.funcs = before.funcs) (types : after.types = before.types)
    (instances : after.instances = before.instances)
    (compiled : Interp.CompiledFunctions code before) : Interp.CompiledFunctions code after := by
  simpa only [Interp.CompiledFunctions, Interp.FunctionCompiled, Interp.FunctionTable,
    decodeInstance, identity, functions, types, instances] using compiled

end Exec.Store

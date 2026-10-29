import Itasca.Runtime.Store.Invariant.FunctionSignatures
import Itasca.Runtime.Store.Invariant.SupportedFunctionTables
import Itasca.Runtime.Compiler.Body.Relations.Executable.ExecutableModuleFunctions
import Itasca.Runtime.Compiler.Body.Relations.Executable.ExecutableFunctionContext
import Itasca.Runtime.Interp.Machine.Stateful.Projection
import Itasca.Runtime.Interp.Machine.Coverage.SupportedHeadCoverage
import Itasca.Runtime.Interp.Machine.Simd.Point
import Itasca.Runtime.Interp.Machine.Calls.IndirectPoint
import Itasca.Runtime.Store.Invariant.InstantiationCode

/-!
Executable function certificates after publication. Compiled function definitions establish the executable-code component retained by instantiation.
-/

/-! ## Executable Compiled Definitions -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Publication of a fresh instance turns staged source-index metadata into
complete compiled-function coverage. Existing functions retain their old
certificates; fresh functions use the compiler's module certificate and the
actual canonical type/function maps. -/
theorem executable_compiled_functions_publish {M : Type} {view : M → Slice U8}
    (before after : runtime.store.Store M) (oldCode : CodeInterpretation)
    (shape : Shape view before) (retained : StagedPrefix before after)
    (oldCompiled : Interp.Machine.CompiledFunctions oldCode before)
    (inst : runtime.store.ModuleInst) (sources : List funccode)
    (found : after.instances.val[before.instances.len.val]? = some inst)
    (certificate : Compiler.ExecutableModuleFunctions inst.module sources)
    (dataCount : ∀ count, inst.module.module.env.data_count = some count →
      count.val = inst.module.module.tail.data.val.length)
    {tables memories} (cache : Cache inst.module.module.env tables memories)
    (entries : TypeEntries after inst.module.module.env.types.val inst.types.val)
    (table : Interp.FunctionTable after inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (staged : StagedFunctionSignatures before after before.instances.len
      (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length)) :
    Interp.Machine.CompiledFunctions (installCode oldCode before.instances.len.val sources) after := by
  intro function present
  rcases staged function present with old | ⟨index, bound, encoded, signatureFound⟩
  · exact supported_function_compiled_prefix shape retained (install_code_agrees before oldCode sources) (oldCompiled function old)
  · intro instanceIndex functionIndex defined
    obtain ⟨sameInstance, sameFunction⟩ := runtime.store.FuncCode.Wasm.inj (defined.symm.trans encoded)
    subst instanceIndex
    subst functionIndex
    let imported := (importedFuncs inst.module.module.env.imports.val).length
    let definedTypes := inst.module.module.env.func_types.val.drop imported
    have resolves : List.Forall₂ (Resolves inst.module.module.env.types.val)
        inst.module.module.env.func_type_indices.val definedTypes := by
      simpa only [definedTypes, imported, List.drop_left] using List.forall₂_drop imported cache.funcs
    have sourceBound : index.val < inst.module.module.env.func_type_indices.val.length := by
      rw [resolves.length_eq]
      exact bound
    let typeIndex := inst.module.module.env.func_type_indices.val[index.val]
    have sourceIndex : inst.module.module.env.func_type_indices.val[index.val]? = some typeIndex :=
      List.getElem?_eq_getElem sourceBound
    obtain ⟨compiled, source, compiledFound, sourceFound, typeIndexEq, signature,
      declared, body, epilogue, typeFound, sourceEq, functionCode⟩ := certificate.entry index.val typeIndex sourceIndex
    have resolved := resolves.get sourceBound bound
    simp only [List.get_eq_getElem] at resolved
    obtain ⟨typeBound, resolvedType⟩ := resolved
    have actualType : inst.module.module.env.types.val[typeIndex.val]? = some definedTypes[index.val] := by
      rw [List.getElem?_eq_getElem typeBound, resolvedType]
    have signatureEq : signature = definedTypes[index.val] := Option.some.inj (typeFound.symm.trans actualType)
    subst signature
    refine ⟨inst, compiled, definedTypes[index.val], declared, body, epilogue,
      found, compiledFound, signatureFound, ?_, table, type_entries_decoded entries, Compiler.ExecutableFunctionCode.complete_module functionCode dataCount⟩
    · rw [install_code_lookup oldCode before.instances.len.val sources inst.module index.val source sourceFound]
      simpa only [typeIndexEq] using sourceEq

end Itasca.Runtime.Store

end

/-! ## Executable Instantiation Code -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv
/-- The compiler's syntactic module certificate supplies fresh function bodies;
existing bodies keep their old certificate. Charging instance items changes no
field involved in code interpretation or function lookup. -/
theorem InstantiationCode.executable_compiled {M : Type} {view : M → Slice U8}
    {before ready : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (code : InstantiationCode before ready inst) (oldCode : CodeInterpretation)
    (shape : Shape view before) (oldCompiled : Interp.Machine.CompiledFunctions oldCode before)
    (found : ready.instances.val[before.instances.len.val]? = some inst)
    (sources : List funccode) (certificate : Compiler.ExecutableModuleFunctions inst.module sources)
    (dataCount : ∀ count, inst.module.module.env.data_count = some count →
      count.val = inst.module.module.tail.data.val.length)
    {tables memories} (cache : Cache inst.module.module.env tables memories) :
    Interp.Machine.CompiledFunctions (installCode oldCode before.instances.len.val sources) ready := by
  obtain ⟨staged, count, rfl, retained, entries, table, signatures⟩ := code
  have compiled := executable_compiled_functions_publish before staged oldCode shape retained oldCompiled inst sources
    found certificate dataCount cache entries table signatures
  exact compiled

end Itasca.Runtime.Store

end

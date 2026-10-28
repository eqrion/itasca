import Exec.Store.Invariant.FunctionSignatures
import Exec.Store.Invariant.SupportedFunctionTables
import Exec.Code.Body.Relations.Common.ExecutableModuleFunctions
import Exec.Code.Body.Relations.Common.ExecutableFunctionContext
import Exec.Interp.StructuredMachine.StatefulProjection
import Exec.Interp.StructuredMachine.SupportedHeadCoverage
import Exec.Interp.StructuredMachine.SimdPoint
import Exec.Interp.StructuredMachine.IndirectPoint

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
    (oldCompiled : Interp.StructuredMachine.CompiledFunctions oldCode before)
    (inst : runtime.store.ModuleInst) (sources : List funccode)
    (found : after.instances.val[before.instances.len.val]? = some inst)
    (certificate : Code.ExecutableModuleFunctions inst.module sources)
    (dataCount : ∀ count, inst.module.module.env.data_count = some count →
      count.val = inst.module.module.tail.data.val.length)
    {tables memories} (cache : Cache inst.module.module.env tables memories)
    (entries : TypeEntries after inst.module.module.env.types.val inst.types.val)
    (table : Interp.FunctionTable after inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (staged : StagedFunctionSignatures before after before.instances.len
      (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length)) :
    Interp.StructuredMachine.CompiledFunctions (installCode oldCode before.instances.len.val sources) after := by
  intro function present
  rcases staged function present with old | ⟨index, bound, encoded, signatureFound⟩
  · exact supported_function_compiled_prefix shape retained (installCode_agrees before oldCode sources) (oldCompiled function old)
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
      found, compiledFound, signatureFound, ?_, table, type_entries_decoded entries, Code.ExecutableFunctionCode.complete_module functionCode dataCount⟩
    · rw [installCode_lookup oldCode before.instances.len.val sources inst.module index.val source sourceFound]
      simpa only [typeIndexEq] using sourceEq

end Itasca.Runtime.Store

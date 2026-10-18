import Exec.Store.Invariant.SourceBindings
import Exec.Store.Invariant.SourceSyntax
import Exec.Store.Invariant.CodeAgreement
import Exec.Store.Invariant.CoreTypingExtension
import Exec.Interp.Machines.Core.CoreFunctionTyping
import Exec.Code.Local.Source.SourceBatchLookup
namespace Exec.Store
open Aeneas Aeneas.Std Itasca Itasca.ModuleEnv

/-- New defined functions get their source typing from the independently
validated module; old function bodies use checked semantic store extension. -/
theorem core_source_functions_publish_wf {M : Type} (view : M → Slice U8)
    (before after : runtime.store.Store M) (oldCode : CodeInterpretation)
    (raw : ModuleBinary.Module)
    (beforeShape : Shape view before)
    (beforeSyntax : StoreSyntax oldCode before)
    (afterWf : wf_store (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) after))
    (retained : StagedPrefix before after)
    (oldTyped : Interp.CoreFunctionsTyped view oldCode before)
    (inst : runtime.store.Instance)
    (found : after.instances.val[before.instances.len.val]? = some inst)
    (elaborated : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (bindings : Abs.ModuleBindings
      (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) after)
      (decodeInstance after inst) (ModuleElaboration.contextOf raw))
    (staged : StagedFunctionSignatures before after before.instances.len
      (inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length)) :
    Interp.CoreFunctionsTyped view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) after := by
  intro function member
  rcases staged function member with old | ⟨index, bound, encoded, signature⟩
  · have agrees := installCode_agrees before oldCode (Code.sourceFunctions raw)
    have prior : Interp.CoreFunctionsTyped view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) before :=
      core_functions_typed_code_agrees agrees oldTyped
    exact staged_core_function_typed_old_wf view _ before after beforeShape (beforeSyntax.code_agrees agrees)
      afterWf retained prior function old
  · let defined := inst.module.module.env.func_types.val.drop (importedFuncs inst.module.module.env.imports.val).length
    have resolves : List.Forall₂ (Resolves inst.module.module.env.types.val)
        inst.module.module.env.func_type_indices.val defined := by
      simpa only [defined, List.drop_left] using
        List.forall₂_drop (importedFuncs inst.module.module.env.imports.val).length matched.2.funcs
    have sourceBound : index.val < inst.module.module.env.func_type_indices.val.length := by
      rw [resolves.length_eq]; exact bound
    let typeIndex := inst.module.module.env.func_type_indices.val[index.val]
    have sourceIndex : inst.module.module.env.func_type_indices.val[index.val]? = some typeIndex := List.getElem?_eq_getElem sourceBound
    have functionsEq := congrArg ModuleBinary.Module.functions matched.1
    have typesEq := congrArg ModuleBinary.Module.types matched.1
    simp only [ModuleElaboration.fromEnv] at functionsEq typesEq
    have rawIndex : raw.functions[index.val]? = some typeIndex := by rw [functionsEq]; exact sourceIndex
    have codeBound : index.val < raw.codes.length := by rw [← elaborated.code_count, functionsEq]; exact sourceBound
    let entry := raw.codes[index.val]
    have entryFound : raw.codes[index.val]? = some entry := List.getElem?_eq_getElem codeBound
    have sourceFound := Code.sourceFunctions_lookup rawIndex entryFound
    have resolved := resolves.get sourceBound bound
    simp only [List.get_eq_getElem] at resolved
    obtain ⟨typeBound, equal⟩ := resolved
    have typeFound : raw.types[typeIndex.val]? = some defined[index.val] := by
      rw [typesEq, List.getElem?_eq_getElem typeBound, equal]
    have sourceTyped := Code.source_function_typed elaborated typed index.val typeIndex entry rawIndex entryFound
    have actualType : ModuleElaboration.functionType raw.types typeIndex = decodeFuncType defined[index.val] := by
      simp only [ModuleElaboration.functionType, typeFound, Option.map_some, Option.getD_some,
        decodeFuncType_source]
    rw [actualType] at sourceTyped
    have contextEq : ModuleElaboration.contextOf raw = Code.moduleSourceContext inst.module := by
      conv_lhs => rw [matched.1]
      exact ModuleElaboration.contextOf_fromEnv matched.2
    simp only [Interp.CoreFunctionTyped, encoded]
    refine ⟨inst, .mk_uN typeIndex.val, entry.declared.map (fun ty => local.LOCAL (Translate.valueType ty)), entry.body, found, ?_, ?_, ?_⟩
    · exact installCode_lookup oldCode before.instances.len.val (Code.sourceFunctions raw) inst.module index.val _ sourceFound
    · rwa [← contextEq]
    · rw [← contextEq]
      simpa only [decodeFunction, encoded, found, List.getD_eq_getElem?_getD, List.getElem?_map, signature,
        Option.map_some, Option.getD_some, ← alloc.vec.Vec.len_val, Code.sourceFunctionCode, CodeEntry.function, defined] using sourceTyped

end Exec.Store

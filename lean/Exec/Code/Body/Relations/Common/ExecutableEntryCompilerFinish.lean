import Exec.Code.Body.Relations.Common.EntryCompilerInitial
import Exec.Code.Body.Reader.Common.IndexedReaderCompilerFinish
import Exec.Code.Body.Relations.Common.ExecutableFunction
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem executable_witness_compiler_finish {A : Type} (ops : runtime.platform.Alloc A)
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish profile}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final profile)
    (facts : CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body)
    {source : List instr}
    (body : StructuredCompiledBodyWithTables final.function.jump_tables.val (ExecutableEmission (CompilerTables.ofFunction final.function) (EnvTranslation.context env w.ctx)) w.startedState final
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ft.results.val.map Translate.valueType) (w.ctx.locals.val.map Translate.valueType) source)
    (compiled : runtime.bytecode.CompiledFunction) (budget : runtime.compiler.Budget A)
    (accepted : runtime.compiler.FunctionCompiler.finish ops final (.Ok ()) = .ok (.Ok compiled, budget)) :
    DefinedExecutableFunctionCode env w.typeIdx
      (.FUNC (.mk_uN w.typeIdx.val)
        ((ModuleLocals.declared w.groups).map Translate.valueType |>.map local.LOCAL) source) compiled := by
  have signature : (env.types.val.map EnvTranslation.funcType)[w.startedState.function.type_index.val]? =
      some ⟨.mk_list (w.ft.params.val.map Translate.valueType), .mk_list (w.ft.results.val.map Translate.valueType)⟩ := by
    simp [facts.typeIndex, List.getElem?_map, List.getElem?_eq_getElem w.type_lt,
      w.function_type, EnvTranslation.funcType]
  have localTypes : w.startedState.function.locals.val.map Translate.valueType =
      w.ft.params.val.map Translate.valueType ++ (ModuleLocals.declared w.groups).map Translate.valueType := by
    rw [facts.locals, w.context_locals, List.map_append]
  have localsWidth : w.startedState.function.local_slots.val = slots
      (w.ft.params.val.map Translate.valueType ++ (ModuleLocals.declared w.groups).map Translate.valueType) := by
    simpa only [compilerLocals, localTypes] using facts.localLayout.slots
  have body' : StructuredCompiledBodyWithTables final.function.jump_tables.val (ExecutableEmission (CompilerTables.ofFunction final.function) (EnvTranslation.context env w.ctx)) w.startedState final
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ft.results.val.map Translate.valueType)
      (w.ft.params.val.map Translate.valueType ++ (ModuleLocals.declared w.groups).map Translate.valueType) source := by
    simpa only [w.context_locals, List.map_append] using body
  obtain ⟨epilogue, certificate⟩ := body'.finish ops signature localTypes facts.parameterSlots localsWidth
    (by rw [facts.capacity]) (.Ok ()) compiled budget accepted
  have same := (compiler_finish_accepted ops final (.Ok ()) compiled budget accepted).2.1
  obtain ⟨_, stable, _⟩ := body
  refine ⟨?_, w.ft, (ModuleLocals.declared w.groups).map Translate.valueType, source, epilogue, ?_, rfl, rfl, ?_⟩
  · rw [same, stable.fields.2.2.2.1, facts.typeIndex]
  · simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
  · have contextEq : sourceFunctionContext env
        (w.ft.params.val.map Translate.valueType ++ (ModuleLocals.declared w.groups).map Translate.valueType)
        (w.ft.results.val.map Translate.valueType) = EnvTranslation.context env w.ctx := by
      rw [← sourceFunctionContext_reader env w.ctx, w.context_locals, List.map_append, w.context_results]
    simpa only [contextEq, EnvTranslation.context, same] using certificate
end Exec.Code

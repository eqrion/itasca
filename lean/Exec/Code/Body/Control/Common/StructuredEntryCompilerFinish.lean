import Exec.Code.Body.Relations.Common.EntryCompilerInitial
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerFinish
import Exec.Code.Local.Relations.Common.CoreFunction
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The accepted entry supplies every fixed premise of function assembly.
Only the completed body relation remains for the opcode fold to establish. -/
theorem structured_witness_compiler_finish {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type} (ops : runtime.platform.Alloc A)
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish profile}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final profile)
    (facts : CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body)
    {source : List instr}
    (body : StructuredCompiledBody emit w.startedState final
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ft.results.val.map Translate.valueType) (w.ctx.locals.val.map Translate.valueType) source)
    (compiled : runtime.bytecode.CompiledFunction) (budget : runtime.compiler.Budget A)
    (accepted : runtime.compiler.FunctionCompiler.finish ops final (.Ok ()) = .ok (.Ok compiled, budget)) :
    DefinedStructuredFunctionCode emit env w.typeIdx
      (.FUNC (.mk_uN w.typeIdx.val)
        ((ModuleLocals.declared w.groups).map Translate.valueType |>.map local.LOCAL) source) compiled := by
  have localTypes : w.startedState.function.locals.val.map Translate.valueType =
      w.ft.params.val.map Translate.valueType ++ (ModuleLocals.declared w.groups).map Translate.valueType := by
    rw [facts.locals, w.context_locals, List.map_append]
  have signature : (env.types.val.map EnvTranslation.funcType)[w.startedState.function.type_index.val]? =
      some ⟨.mk_list (w.ft.params.val.map Translate.valueType), .mk_list (w.ft.results.val.map Translate.valueType)⟩ := by
    simp [facts.typeIndex, List.getElem?_map, List.getElem?_eq_getElem w.type_lt,
      w.function_type, EnvTranslation.funcType]
  have localsWidth : w.startedState.function.local_slots.val = slots
      (w.ft.params.val.map Translate.valueType ++ (ModuleLocals.declared w.groups).map Translate.valueType) := by
    simpa only [compilerLocals, localTypes] using facts.localLayout.slots
  have body' : StructuredCompiledBody emit w.startedState final
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ft.results.val.map Translate.valueType)
      (w.ft.params.val.map Translate.valueType ++ (ModuleLocals.declared w.groups).map Translate.valueType) source := by
    simpa only [w.context_locals, List.map_append] using body
  obtain ⟨epilogue, certificate⟩ := body'.finish ops signature localTypes facts.parameterSlots localsWidth
    (by rw [facts.capacity]) (.Ok ()) compiled budget accepted
  have same := (compiler_finish_accepted ops final (.Ok ()) compiled budget accepted).2.1
  obtain ⟨_, stable, _⟩ := body
  refine ⟨?_, w.ft, (ModuleLocals.declared w.groups).map Translate.valueType, source, epilogue, ?_, rfl, certificate⟩
  · rw [same, stable.fields.2.2.2.1, facts.typeIndex]
  · simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
end Exec.Code

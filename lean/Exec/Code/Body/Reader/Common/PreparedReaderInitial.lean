import Exec.Code.Body.Relations.Common.PreparedCompilerStart
import Exec.Code.Body.Reader.Common.IndexedReaderCompilerInitial
import Exec.Code.Body.Reader.Table.StructuredReaderCompilerPoint
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem indexed_prepared_compiler_start (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start profile}
    (w : CodeEntry.Prepared data env index start profile)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val + w.finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (startedCall : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started)) :
    CompilerEntryFacts started env w.ctx w.typeIdx w.ft w.body ∧
    StructuredCompilerPrefix jumpTables emit started started
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ft.results.val.map Translate.valueType) (w.ctx.locals.val.map Translate.valueType)
      [] (SourceScope.initial (w.ft.results.val.map Translate.valueType)) [] 0 := by
  have sourceLookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
  obtain ⟨signature, lookup, matched⟩ := signatureTable.lookup_source sourceLookup
  have beginFits : batchStart.val + w.bodyStart.val ≤ Usize.max := by
    have length := w.body_bytes.length
    omega
  have facts := compiler_function_start_facts ops law signatures functionSlots budget batchStart initial started
    w.ctx w.typeIdx signature w.bodyStart w.finish lookup beginFits endFits created startedCall
  obtain ⟨layout, locals, capacity, params, typeIndex, bodyStart, _, sigs, funcs, _⟩ := facts
  constructor
  · refine ⟨layout, locals, capacity, ?_, typeIndex, ?_, ?_, ?_⟩
    · rw [params]
      exact matched.paramWords
    · simpa only [sigs] using signatureTable
    · simpa only [FunctionParameterSlots, funcs] using functionTable
    · exact function_body_coordinate_bound w.body_bytes bodyStart endFits
  · exact structured_compiler_function_start_prefix emit ops law signatures functionSlots budget batchStart initial started
      w.ctx w.typeIdx signature w.bodyStart w.finish _ _ _ lookup matched.resultWords beginFits endFits created startedCall

theorem indexed_prepared_compiler_initial_wasm2 (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start profile}
    (w : CodeEntry.Prepared data env index start profile)
    (bodyBound : w.body.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val + w.finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (startedCall : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started)) :
    CompilerEntryFacts started env w.ctx w.typeIdx w.ft w.body ∧
    StructuredReaderCompilerPointWasm2 jumpTables emit started started
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ft.results.val.map Translate.valueType) (w.ctx.locals.val.map Translate.valueType)
      w.body env w.ctx.locals w.typeIdx w.ft (Wasm2.initial w.typeIdx) := by
  obtain ⟨facts, compiled⟩ := indexed_prepared_compiler_start jumpTables emit ops law w signatureTable functionTable endFits created startedCall
  have lookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
  exact ⟨facts, (StructuredReaderCompilerStateWasm2.initial _ _ _ _ _ _ _ _ _ lookup bodyBound compiled).point⟩

end Exec.Code

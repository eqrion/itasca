import Exec.Code.Body.Relations.Common.EntryCompilerInitial
import Itasca.Module.Code.ReachedEntry
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Entry framing and captured signature lookup justify every unchecked
operation in the fresh function-start callback, including rejected allocation. -/
theorem prepared_compiler_start_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial : runtime.compiler.FunctionCompiler A} {data env index start profile}
    (w : CodeEntry.Prepared data env index start profile)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (endFits : batchStart.val + w.finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish ⦃ _ => True ⦄ := by
  have sourceLookup : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  obtain ⟨signature,lookup,_⟩ := signatureTable.lookup_source sourceLookup
  have fresh := compiler_new ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at fresh
  obtain ⟨layout,locals,operands,controls,frames,code,reachable,sigs,slots,batch⟩ := fresh
  apply WP.spec_mono (compiler_function_start ops law initial w.ctx w.typeIdx signature
    w.bodyStart w.finish (by simpa only [sigs] using lookup)
    (by rw [batch]; have length := w.body_bytes.length; omega)
    (by simpa only [batch] using endFits) locals layout operands
    (by simp only [controls,List.length_nil]; scalar_tac)
    (by simp only [frames,List.length_nil]; scalar_tac))
  intros
  trivial

theorem prepared_compiler_start {A : Type} (ops : runtime.platform.Alloc A)
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
    CompilerPrefix started started
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
  · exact compiler_function_start_prefix ops law signatures functionSlots budget batchStart initial started
      w.ctx w.typeIdx signature w.bodyStart w.finish _ _ _ lookup matched.resultWords beginFits endFits created startedCall

end Exec.Code

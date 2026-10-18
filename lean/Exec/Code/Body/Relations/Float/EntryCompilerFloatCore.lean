import Exec.Code.Body.Lowering.Float.FloatCoreEntryCompilerFinish
import Exec.Code.Body.Control.Common.StructuredEntryCompilerInitial
import Exec.Code.Body.Reader.Float.FloatCoreReaderCompilerBodyWasm1
import Exec.Code.Body.Reader.Float.FloatCoreReaderCompilerBodyWasm2
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Successful construction, entry validation and compiler finishing establish
the retained source certificate for the scalar core, without assuming a
compiler relation or instruction-callback correctness. -/
theorem witness_compile_float_core_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final .Wasm2)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val + finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    {source : List instr} (encoded : Wasm2.BodyEncoding w.body source)
    (supported : Forall Abs.FloatCoreInstr source)
    (compiled : runtime.bytecode.CompiledFunction) (finalBudget : runtime.compiler.Budget A)
    (finished : runtime.compiler.FunctionCompiler.finish ops final (.Ok ()) = .ok (.Ok compiled, finalBudget)) :
    DefinedFloatCoreFunctionCode env w.typeIdx
      (.FUNC (.mk_uN w.typeIdx.val)
        ((ModuleLocals.declared w.groups).map Translate.valueType |>.map local.LOCAL) source) compiled := by
  obtain ⟨facts, point, run⟩ := structured_witness_compiler_initial_wasm2 (FloatCoreEmission (EnvTranslation.context env w.ctx)) ops law w signatureTable functionTable endFits created
  have body := run.compile_float_core ops law (EnvTranslation.context env w.ctx) point encoded supported facts.localLayout facts.locals
    facts.functionSlots rfl rfl rfl facts.signatures facts.bodyBound
  exact float_core_witness_compiler_finish ops w facts body compiled finalBudget finished

theorem witness_compile_float_core_wasm1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final .Wasm1)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val + finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    {source : List instr} (encoded : Wasm1.BodyEncoding w.body source)
    (supported : Forall Abs.FloatCoreInstr source)
    (singleResult : w.ft.results.val.length ≤ 1)
    (compiled : runtime.bytecode.CompiledFunction) (finalBudget : runtime.compiler.Budget A)
    (finished : runtime.compiler.FunctionCompiler.finish ops final (.Ok ()) = .ok (.Ok compiled, finalBudget)) :
    DefinedFloatCoreFunctionCode env w.typeIdx
      (.FUNC (.mk_uN w.typeIdx.val)
        ((ModuleLocals.declared w.groups).map Translate.valueType |>.map local.LOCAL) source) compiled := by
  obtain ⟨facts, results, point, run⟩ := structured_witness_compiler_initial_wasm1 (FloatCoreEmission (EnvTranslation.context env w.ctx)) ops law w signatureTable functionTable endFits created singleResult
  have body := run.compile_float_core ops law (EnvTranslation.context env w.ctx) point encoded supported facts.localLayout facts.locals
    facts.functionSlots rfl rfl rfl results facts.bodyBound
  rw [w.context_results] at body
  exact float_core_witness_compiler_finish ops w facts body compiled finalBudget finished

/-- Both profiles produce the same function certificate from their independent
body grammar and the actual compiler calls. -/
theorem witness_compile_float_core {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish profile}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final profile)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val + finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    {source : List instr} (encoded : Profile.BodyEncoding profile w.body source)
    (supported : Forall Abs.FloatCoreInstr source)
    (singleResult : profile = .Wasm1 → w.ft.results.val.length ≤ 1)
    (compiled : runtime.bytecode.CompiledFunction) (finalBudget : runtime.compiler.Budget A)
    (finished : runtime.compiler.FunctionCompiler.finish ops final (.Ok ()) = .ok (.Ok compiled, finalBudget)) :
    DefinedFloatCoreFunctionCode env w.typeIdx
      (.FUNC (.mk_uN w.typeIdx.val)
        ((ModuleLocals.declared w.groups).map Translate.valueType |>.map local.LOCAL) source) compiled := by
  cases profile with
  | Wasm1 =>
    exact witness_compile_float_core_wasm1 ops law w signatureTable functionTable endFits created
      encoded supported (singleResult rfl) compiled finalBudget finished
  | Wasm2 =>
    exact witness_compile_float_core_wasm2 ops law w signatureTable functionTable endFits created
      encoded supported compiled finalBudget finished
end Exec.Code

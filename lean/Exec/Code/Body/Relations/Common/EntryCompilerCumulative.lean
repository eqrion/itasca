import Exec.Code.Body.Control.Common.CumulativeEntryCompilerFinish
import Exec.Code.Body.Control.Common.StructuredEntryCompilerInitial
import Exec.Code.Body.Reader.Common.CumulativeReaderCompilerBodyWasm2
import Exec.Code.Body.Reader.Common.CumulativeReaderCompilerBodyWasm1
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem witness_compile_cumulative_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
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
    (supported : Forall Abs.CumulativeInstr source)
    (compiled : runtime.bytecode.CompiledFunction) (finalBudget : runtime.compiler.Budget A)
    (finished : runtime.compiler.FunctionCompiler.finish ops final (.Ok ()) = .ok (.Ok compiled, finalBudget)) :
    DefinedCumulativeFunctionCode env w.typeIdx
      (.FUNC (.mk_uN w.typeIdx.val)
        ((ModuleLocals.declared w.groups).map Translate.valueType |>.map local.LOCAL) source) compiled := by
  let C := EnvTranslation.context env w.ctx
  have initialPoint := fun future : List (U32 × U32) =>
    structured_witness_compiler_initial_wasm2 (CumulativeEmission (w.startedState.function.indirect.val ++ future) C)
      ops law w signatureTable functionTable endFits created
  obtain ⟨facts,_,run⟩ := initialPoint []
  have point : CumulativeReaderCompilerPointWasm2 C w.startedState w.startedState
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ft.results.val.map Translate.valueType) (w.ctx.locals.val.map Translate.valueType)
      w.body env w.ctx.locals w.typeIdx w.ft (Wasm2.initial w.typeIdx) :=
    fun future => (initialPoint future).2.1
  have matched : EnvTranslation.Matches env ⟨w.ctx.locals,w.ft.results⟩ C := by
    refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
    simp only [C,EnvTranslation.context,w.context_results]
  have body := run.compile_cumulative ops law C point encoded supported facts.localLayout facts.locals
    facts.functionSlots matched rfl facts.signatures facts.bodyBound
  exact cumulative_witness_compiler_finish ops w facts body compiled finalBudget finished

theorem witness_compile_cumulative_wasm1 {A : Type} (ops : runtime.platform.Alloc A)
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
    (supported : Forall Abs.CumulativeInstr source)
    (singleResult : w.ft.results.val.length ≤ 1)
    (compiled : runtime.bytecode.CompiledFunction) (finalBudget : runtime.compiler.Budget A)
    (finished : runtime.compiler.FunctionCompiler.finish ops final (.Ok ()) = .ok (.Ok compiled, finalBudget)) :
    DefinedCumulativeFunctionCode env w.typeIdx
      (.FUNC (.mk_uN w.typeIdx.val)
        ((ModuleLocals.declared w.groups).map Translate.valueType |>.map local.LOCAL) source) compiled := by
  let C := EnvTranslation.context env w.ctx
  have initialPoint := fun future : List (U32 × U32) =>
    structured_witness_compiler_initial_wasm1 (CumulativeEmission (w.startedState.function.indirect.val ++ future) C)
      ops law w signatureTable functionTable endFits created singleResult
  obtain ⟨facts,results,_,run⟩ := initialPoint []
  have point : CumulativeReaderCompilerPointWasm1 C w.startedState w.startedState
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (w.ctx.results.val.map Translate.valueType) (w.ctx.locals.val.map Translate.valueType)
      w.body env w.ctx (Wasm1.Loop.initialBlockType w.ctx.results.val) (Wasm1.Loop.initial (Wasm1.Loop.initialBlockType w.ctx.results.val)) :=
    fun future => (initialPoint future).2.2.1
  have body := run.compile_cumulative ops law C point encoded supported facts.localLayout facts.locals
    facts.functionSlots rfl ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ facts.signatures results facts.bodyBound
  rw [w.context_results] at body
  exact cumulative_witness_compiler_finish ops w facts body compiled finalBudget finished

/-- Both profiles produce the same function certificate from their independent
body grammar and the actual compiler calls. -/
theorem witness_compile_cumulative {A : Type} (ops : runtime.platform.Alloc A)
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
    (supported : Forall Abs.CumulativeInstr source)
    (singleResult : profile = .Wasm1 → w.ft.results.val.length ≤ 1)
    (compiled : runtime.bytecode.CompiledFunction) (finalBudget : runtime.compiler.Budget A)
    (finished : runtime.compiler.FunctionCompiler.finish ops final (.Ok ()) = .ok (.Ok compiled, finalBudget)) :
    DefinedCumulativeFunctionCode env w.typeIdx
      (.FUNC (.mk_uN w.typeIdx.val)
        ((ModuleLocals.declared w.groups).map Translate.valueType |>.map local.LOCAL) source) compiled := by
  cases profile with
  | Wasm1 =>
    exact witness_compile_cumulative_wasm1 ops law w signatureTable functionTable endFits created
      encoded supported (singleResult rfl) compiled finalBudget finished
  | Wasm2 =>
    exact witness_compile_cumulative_wasm2 ops law w signatureTable functionTable endFits created
      encoded supported compiled finalBudget finished
end Exec.Code

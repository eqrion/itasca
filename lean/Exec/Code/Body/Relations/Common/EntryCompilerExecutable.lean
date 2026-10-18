import Exec.Code.Body.Relations.Common.ExecutableEntryCompilerFinish
import Exec.Code.Body.Control.Table.IndexedTableEntryInitial
import Exec.Code.Body.Reader.Common.IndexedReaderCompilerBodyWasm1
import Exec.Code.Body.Reader.Common.IndexedReaderCompilerBodyWasm2
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem witness_compile_executable_wasm2 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final .Wasm2)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val)=
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val+finish.val≤Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart=.ok initial)
    {source : List instr} (encoded : Wasm2.BodyEncoding w.body source)
    (compiled : runtime.bytecode.CompiledFunction) (finalBudget : runtime.compiler.Budget A)
    (finished : runtime.compiler.FunctionCompiler.finish ops final (.Ok ())=.ok (.Ok compiled,finalBudget)) :
    DefinedExecutableFunctionCode env w.typeIdx (.FUNC (.mk_uN w.typeIdx.val)
      ((ModuleLocals.declared w.groups).map Translate.valueType |>.map local.LOCAL) source) compiled := by
  let C := EnvTranslation.context env w.ctx
  obtain ⟨facts,point,run⟩ := indexed_table_witness_compiler_initial_wasm2
    (fun tables => ExecutableEmission tables C) ops law w signatureTable functionTable endFits created
  have matched : EnvTranslation.Matches env ⟨w.ctx.locals,w.ft.results⟩ C := by
    refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
    simp only [C,EnvTranslation.context,w.context_results]
  have body := run.compile_executable ops law C point encoded facts.localLayout facts.locals
    facts.functionSlots matched rfl facts.signatures facts.bodyBound
  exact executable_witness_compiler_finish ops w facts body compiled finalBudget finished

theorem witness_compile_executable_wasm1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final .Wasm1)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val)=
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val+finish.val≤Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart=.ok initial)
    {source : List instr} (encoded : Wasm1.BodyEncoding w.body source)
    (singleResult : w.ft.results.val.length≤1)
    (compiled : runtime.bytecode.CompiledFunction) (finalBudget : runtime.compiler.Budget A)
    (finished : runtime.compiler.FunctionCompiler.finish ops final (.Ok ())=.ok (.Ok compiled,finalBudget)) :
    DefinedExecutableFunctionCode env w.typeIdx (.FUNC (.mk_uN w.typeIdx.val)
      ((ModuleLocals.declared w.groups).map Translate.valueType |>.map local.LOCAL) source) compiled := by
  let C := EnvTranslation.context env w.ctx
  obtain ⟨facts,results,point,run⟩ := indexed_table_witness_compiler_initial_wasm1
    (fun tables => ExecutableEmission tables C) ops law w signatureTable functionTable endFits created singleResult
  have body := run.compile_executable ops law C point encoded facts.localLayout facts.locals
    facts.functionSlots ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ rfl facts.signatures results facts.bodyBound
  rw [w.context_results] at body
  exact executable_witness_compiler_finish ops w facts body compiled finalBudget finished

/-- Both complete source profiles produce the same indexed function evidence;
source coverage follows from independent binary encoding. -/
theorem witness_compile_executable {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish profile}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final profile)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val)=
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val+finish.val≤Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart=.ok initial)
    {source : List instr} (encoded : Profile.BodyEncoding profile w.body source)
    (singleResult : profile=.Wasm1 → w.ft.results.val.length≤1)
    (compiled : runtime.bytecode.CompiledFunction) (finalBudget : runtime.compiler.Budget A)
    (finished : runtime.compiler.FunctionCompiler.finish ops final (.Ok ())=.ok (.Ok compiled,finalBudget)) :
    DefinedExecutableFunctionCode env w.typeIdx (.FUNC (.mk_uN w.typeIdx.val)
      ((ModuleLocals.declared w.groups).map Translate.valueType |>.map local.LOCAL) source) compiled := by
  cases profile with
  | Wasm1 =>
    exact witness_compile_executable_wasm1 ops law w signatureTable functionTable endFits created
      encoded (singleResult rfl) compiled finalBudget finished
  | Wasm2 =>
    exact witness_compile_executable_wasm2 ops law w signatureTable functionTable endFits created
      encoded compiled finalBudget finished
end Exec.Code

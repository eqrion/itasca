import Itasca.Runtime.Compiler.Body.Relations.Entry.ExecutableEntryCompilerFinish
import Itasca.Runtime.Compiler.Body.Control.Table.IndexedTableEntryInitial
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedCompilerBodyWasm2

/-!
Both complete source profiles produce the same indexed function evidence; source coverage follows from independent binary encoding.

Main declarations: `witness_compile_executable`. A direct consumer is `Compiler.Body.Relations.Entry.EntryBodyExecutable`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

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
  have body := run.compile_executable ops law C point encoded.to_wasm2 facts.localLayout facts.locals
    facts.functionSlots matched rfl facts.signatures facts.bodyBound
  exact executable_witness_compiler_finish ops w facts body compiled finalBudget finished

end Itasca.Runtime.Code

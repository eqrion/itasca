import Exec.Code.Body.Relations.Common.EntryCompilerExecutable

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem witness_body_executable {A : Type} (ops : runtime.platform.Alloc A)
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
    : CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body ∧
      StructuredCompiledBody final.function.jump_tables.val
        (ExecutableEmission (CompilerTables.ofFunction final.function) (EnvTranslation.context env w.ctx))
        w.startedState final (env.types.val.map EnvTranslation.funcType)
        (env.func_types.val.map EnvTranslation.funcType) (w.ft.results.val.map Translate.valueType)
        (w.ctx.locals.val.map Translate.valueType) source := by
  let C := EnvTranslation.context env w.ctx
  obtain ⟨facts,point,run⟩ := indexed_table_witness_compiler_initial_wasm2
    (fun tables => ExecutableEmission tables C) ops law w signatureTable functionTable endFits created
  have matched : EnvTranslation.Matches env ⟨w.ctx.locals,w.ft.results⟩ C := by
    refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
    simp only [C,EnvTranslation.context,w.context_results]
  have body := run.compile_executable ops law C point encoded.to_wasm2 facts.localLayout facts.locals
    facts.functionSlots matched rfl facts.signatures facts.bodyBound
  exact ⟨facts,body⟩

end Exec.Code

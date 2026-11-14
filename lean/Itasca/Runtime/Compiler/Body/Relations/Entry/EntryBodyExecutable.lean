import Itasca.Runtime.Compiler.Body.Relations.Entry.PreparedRawInitial
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedCompilerFinish
import Itasca.Runtime.Compiler.Body.Relations.Executable.RecordingEmission
import Itasca.Runtime.Compiler.Body.Control.Table.IndexedTableEntryInitial
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedCompilerBodyWasm2

/-!
Sections, each formerly its own module: ExecutableEntryCompilerFinish, EntryCompilerExecutable, EntryBodyExecutable.
-/

/-! ## ExecutableEntryCompilerFinish -/

section

/-!
Finishing a compiled entry while retaining its executable certificate.

Main declarations: `executable_witness_compiler_finish`. A direct consumer is `Compiler.Body.Relations.Entry.EntryCompilerExecutable`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem executable_witness_compiler_finish {A : Type} (ops : runtime.platform.Alloc A)
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish }
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final )
    (facts : CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body)
    {source : List instr}
    (body : StructuredCompiledBody final.function.jump_tables.val (ExecutableEmission (CompilerTables.ofFunction final.function) (EnvTranslation.context env w.ctx)) w.startedState final
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
  have body' : StructuredCompiledBody final.function.jump_tables.val (ExecutableEmission (CompilerTables.ofFunction final.function) (EnvTranslation.context env w.ctx)) w.startedState final
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
      rw [← source_function_context_reader env w.ctx, w.context_locals, List.map_append, w.context_results]
    simpa only [contextEq, EnvTranslation.context, same] using certificate
end Itasca.Runtime.Compiler

end

/-! ## EntryCompilerExecutable -/

section

/-!
Both complete source profiles produce the same indexed function evidence; source coverage follows from independent binary encoding.

Main declarations: `witness_compile_executable`. A direct consumer is `Compiler.Body.Relations.Entry.EntryBodyExecutable`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Both complete source profiles produce the same indexed function evidence;
source coverage follows from independent binary encoding. -/
theorem witness_compile_executable {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish }
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final )
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val)=
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val+finish.val≤Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart=.ok initial)
    {source : List instr} (encoded : Profile.BodyEncoding w.body source)
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

end Itasca.Runtime.Compiler

end

/-! ## EntryBodyExecutable -/

section

/-!
An executable source-body certificate from the validated entry witness.

Main declarations: `witness_body_executable`. A direct consumer is `Compiler.Module.EntryFinishAvailable`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem witness_body_executable {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish }
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final )
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val)=
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val+finish.val≤Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart=.ok initial)
    {source : List instr} (encoded : Profile.BodyEncoding w.body source) : CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body ∧
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

end Itasca.Runtime.Compiler

end

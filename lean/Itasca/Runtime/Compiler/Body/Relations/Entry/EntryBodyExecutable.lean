import Itasca.Runtime.Compiler.Body.Relations.Entry.PreparedRawInitial
import Itasca.Runtime.Compiler.Body.Reader.Replay.SafetyAndFinish
import Itasca.Runtime.Compiler.Body.Relations.ExecutableEmission
import Itasca.Runtime.Compiler.Body.Control.IndexedEntryCompilerInitial
import Itasca.Runtime.Compiler.Body.Reader.Replay.FoldAndStatefulReplay

open Itasca.Representation

/-! ## ExecutableEntryCompilerFinish -/

section

/-!
Finishing a compiled entry while retaining its executable certificate.

Main declarations: `executable_witness_compiler_finish`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem executable_witness_compiler_finish {A : Type} (ops : runtime.platform.Alloc A)
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish }
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final )
    (facts : CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body)
    {source : List instr}
    (body : StructuredCompiledBody final.function.jump_tables.val (ExecutableEmission (CompilerTables.ofFunction final.function) (Translation.Environment.context env w.ctx)) w.startedState final
      (env.types.val.map Translation.Environment.funcType) (env.func_types.val.map Translation.Environment.funcType)
      (w.ft.results.val.map Translation.valueType) (w.ctx.locals.val.map Translation.valueType) source)
    (compiled : runtime.bytecode.CompiledFunction) (budget : runtime.compiler.Budget A)
    (accepted : runtime.compiler.FunctionCompiler.finish ops final (.Ok ()) = .ok (.Ok compiled, budget)) :
    DefinedExecutableFunctionCode env w.typeIdx
      (.FUNC (.mk_uN w.typeIdx.val)
        ((CodeEntry.Locals.declared w.groups).map Translation.valueType |>.map local.LOCAL) source) compiled := by
  have signature : (env.types.val.map Translation.Environment.funcType)[w.startedState.function.type_index.val]? =
      some ⟨.mk_list (w.ft.params.val.map Translation.valueType), .mk_list (w.ft.results.val.map Translation.valueType)⟩ := by
    simp [facts.typeIndex, List.getElem?_map, List.getElem?_eq_getElem w.type_lt,
      w.function_type, Translation.Environment.funcType]
  have localTypes : w.startedState.function.locals.val.map Translation.valueType =
      w.ft.params.val.map Translation.valueType ++ (CodeEntry.Locals.declared w.groups).map Translation.valueType := by
    rw [facts.locals, w.context_locals, List.map_append]
  have localsWidth : w.startedState.function.local_slots.val = slots
      (w.ft.params.val.map Translation.valueType ++ (CodeEntry.Locals.declared w.groups).map Translation.valueType) := by
    simpa only [compilerLocals, localTypes] using facts.localLayout.slots
  have body' : StructuredCompiledBody final.function.jump_tables.val (ExecutableEmission (CompilerTables.ofFunction final.function) (Translation.Environment.context env w.ctx)) w.startedState final
      (env.types.val.map Translation.Environment.funcType) (env.func_types.val.map Translation.Environment.funcType)
      (w.ft.results.val.map Translation.valueType)
      (w.ft.params.val.map Translation.valueType ++ (CodeEntry.Locals.declared w.groups).map Translation.valueType) source := by
    simpa only [w.context_locals, List.map_append] using body
  obtain ⟨epilogue, certificate⟩ := body'.finish ops signature localTypes facts.parameterSlots localsWidth
    (by rw [facts.capacity]) (.Ok ()) compiled budget accepted
  have same := (compiler_finish_accepted ops final (.Ok ()) compiled budget accepted).2.1
  obtain ⟨_, stable, _⟩ := body
  refine ⟨?_, w.ft, (CodeEntry.Locals.declared w.groups).map Translation.valueType, source, epilogue, ?_, rfl, rfl, ?_⟩
  · rw [same, stable.fields.2.2.2.1, facts.typeIndex]
  · simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
  · have contextEq : sourceFunctionContext env
        (w.ft.params.val.map Translation.valueType ++ (CodeEntry.Locals.declared w.groups).map Translation.valueType)
        (w.ft.results.val.map Translation.valueType) = Translation.Environment.context env w.ctx := by
      rw [← source_function_context_reader env w.ctx, w.context_locals, List.map_append, w.context_results]
    simpa only [contextEq, Translation.Environment.context, same] using certificate
end Itasca.Compiler

end

/-! ## EntryCompilerExecutable -/

section

/-!
Independent binary body encoding constructs indexed function evidence for the complete instruction grammar.

Main declarations: `witness_compile_executable`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Independent binary body encoding constructs indexed function evidence for the
complete instruction grammar. -/
theorem witness_compile_executable {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish }
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final )
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val)=
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType)))
    (endFits : batchStart.val+finish.val≤Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart=.ok initial)
    {source : List instr} (encoded : Body.BodyEncoding w.body source)
    (compiled : runtime.bytecode.CompiledFunction) (finalBudget : runtime.compiler.Budget A)
    (finished : runtime.compiler.FunctionCompiler.finish ops final (.Ok ())=.ok (.Ok compiled,finalBudget)) :
    DefinedExecutableFunctionCode env w.typeIdx (.FUNC (.mk_uN w.typeIdx.val)
      ((CodeEntry.Locals.declared w.groups).map Translation.valueType |>.map local.LOCAL) source) compiled := by
  let C := Translation.Environment.context env w.ctx
  obtain ⟨facts,point,run⟩ := indexed_table_witness_compiler_initial
    (fun tables => ExecutableEmission tables C) ops law w signatureTable functionTable endFits created
  have matched : Translation.Environment.Matches env ⟨w.ctx.locals,w.ft.results⟩ C := by
    refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
    simp only [C,Translation.Environment.context,w.context_results]
  have body := run.compile_executable ops law C point encoded facts.localLayout facts.locals
    facts.functionSlots matched rfl facts.signatures facts.bodyBound
  exact executable_witness_compiler_finish ops w facts body compiled finalBudget finished

end Itasca.Compiler

end

/-! ## EntryBodyExecutable -/

section

/-!
An executable source-body certificate from the validated entry witness.

Main declarations: `witness_body_executable`.
-/

namespace Itasca.Compiler
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
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translation.valueType)))
    (endFits : batchStart.val+finish.val≤Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart=.ok initial)
    {source : List instr} (encoded : Body.BodyEncoding w.body source) : CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body ∧
      StructuredCompiledBody final.function.jump_tables.val
        (ExecutableEmission (CompilerTables.ofFunction final.function) (Translation.Environment.context env w.ctx))
        w.startedState final (env.types.val.map Translation.Environment.funcType)
        (env.func_types.val.map Translation.Environment.funcType) (w.ft.results.val.map Translation.valueType)
        (w.ctx.locals.val.map Translation.valueType) source := by
  let C := Translation.Environment.context env w.ctx
  obtain ⟨facts,point,run⟩ := indexed_table_witness_compiler_initial
    (fun tables => ExecutableEmission tables C) ops law w signatureTable functionTable endFits created
  have matched : Translation.Environment.Matches env ⟨w.ctx.locals,w.ft.results⟩ C := by
    refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
    simp only [C,Translation.Environment.context,w.context_results]
  have body := run.compile_executable ops law C point encoded facts.localLayout facts.locals
    facts.functionSlots matched rfl facts.signatures facts.bodyBound
  exact ⟨facts,body⟩

end Itasca.Compiler

end

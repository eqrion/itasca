import Exec.Code.Body.Relations.Common.EntryBodyExecutable
import Exec.Code.Local.Publication.FunctionPublicationHeader

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Complete-profile source encoding and the actual unfinished body establish
all header checks, including the final return. No successful finish or completed
function certificate is needed. -/
theorem witness_header_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish profile}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final profile)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val+finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    {source : List instr} (encoded : Profile.BodyEncoding profile w.body source) :
    FunctionPublicationHeader final.function ∧ final.frames.val = [] ∧ final.function.code.length ≤ U32.max := by
  have bodyFacts : CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body ∧
      StructuredCompiledBody final.function.jump_tables.val
        (ExecutableEmission (CompilerTables.ofFunction final.function) (EnvTranslation.context env w.ctx))
        w.startedState final (env.types.val.map EnvTranslation.funcType)
        (env.func_types.val.map EnvTranslation.funcType) (w.ft.results.val.map Translate.valueType)
        (w.ctx.locals.val.map Translate.valueType) source :=
    witness_body_executable ops law w signatureTable functionTable endFits created encoded
  obtain ⟨facts,target,stable,closed,_,⟨returnStart,returnCount,_,last⟩,length,codeBound⟩ := bodyFacts
  obtain ⟨_,_,_,_,_,paramsEq,localsEq,bodyStartEq,_,_⟩ := stable.fields
  have signature : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  obtain ⟨sig,lookup,_⟩ := signatureTable.lookup_source signature
  have beginFits : batchStart.val+w.bodyStart.val ≤ Usize.max := by
    have span := w.body_bytes.length
    omega
  obtain ⟨_,_,_,_,_,bodyStart,_,_⟩ := compiler_function_start_facts ops law signatures functionSlots budget batchStart
    initial w.startedState w.ctx w.typeIdx sig w.bodyStart finish lookup beginFits endFits created w.function_start
  refine ⟨⟨?_,by change 0 < final.function.code.val.length; omega,?_,?_,?_⟩,closed,codeBound⟩
  · intro synthetic
    have zero := congrArg UScalar.val synthetic.1
    have headerSpan := w.header.span
    have localsSpan := w.locals_bytes.span
    rw [bodyStartEq] at zero
    change w.startedState.function.body_start.val = 0 at zero
    omega
  · rw [localsEq,← facts.capacity]
    exact stable.capacity
  · rw [paramsEq,localsEq,facts.parameterSlots,facts.localLayout.slots]
    simp only [compilerLocals,facts.locals,w.context_locals,List.map_append,slots_append]
    omega
  · refine ⟨returnStart,returnCount,?_⟩
    simpa only [show final.function.code.length-1 = target.val by change final.function.code.val.length-1 = target.val; omega] using last

end Exec.Code

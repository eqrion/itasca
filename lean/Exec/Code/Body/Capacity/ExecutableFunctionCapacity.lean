import Exec.Code.Body.Capacity.FunctionCapacity
import Exec.Code.Body.Capacity.ExecutableEntryCapacity
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
theorem witness_executable_function_capacity {A : Type} (ops : runtime.platform.Alloc A)
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
    (compiled : runtime.bytecode.CompiledFunction) (finalBudget : runtime.compiler.Budget A)
    (finished : runtime.compiler.FunctionCompiler.finish ops final (.Ok ()) = .ok (.Ok compiled, finalBudget)) :
    FunctionCapacity profile env w.typeIdx
      (.FUNC (.mk_uN w.typeIdx.val)
        ((ModuleLocals.declared w.groups).map Translate.valueType |>.map local.LOCAL) source) compiled := by
  obtain ⟨samples, trace, bound⟩ := witness_compile_executable_capacity ops law w signatureTable functionTable
    endFits created encoded compiled finalBudget finished
  refine ⟨_, ⟨w.ft, ModuleLocals.declared w.groups, w.body, w.ctx, source, samples,
    ?_, ?_, w.context_locals, w.context_results, encoded, trace, rfl⟩, ?_⟩
  · simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
  · simp only [List.map_map]
  · simpa only [List.map_append] using bound

end Itasca.Runtime.Code

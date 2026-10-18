import Exec.Representation.FunctionCapacity
import Exec.Code.Body.Capacity.EntryCapacity
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem witness_function_capacity {A : Type} (ops : runtime.platform.Alloc A)
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
    (supported : Forall Abs.SliceInstr source)
    (compiled : runtime.bytecode.CompiledFunction) (finalBudget : runtime.compiler.Budget A)
    (finished : runtime.compiler.FunctionCompiler.finish ops final (.Ok ()) = .ok (.Ok compiled, finalBudget)) :
    FunctionCapacity profile env w.typeIdx
      (.FUNC (.mk_uN w.typeIdx.val)
        ((ModuleLocals.declared w.groups).map Translate.valueType |>.map local.LOCAL) source) compiled := by
  obtain ⟨samples, trace, bound⟩ := witness_compile_capacity ops law w signatureTable functionTable
    endFits created encoded supported compiled finalBudget finished
  refine ⟨_, ⟨w.ft, ModuleLocals.declared w.groups, w.body, w.ctx, source, samples,
    ?_, ?_, w.context_locals, w.context_results, encoded, trace, rfl⟩, ?_⟩
  · simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
  · simp only [List.map_map]
  · simpa only [List.map_append] using bound

/-- Source-indexed frame bounds retained for the defined function prefix. -/
structure ModuleCapacities (module : runtime.compiler.ExecutableModule)
    (sources : List funccode) : Prop where
  count : sources.length = module.module.env.func_type_indices.val.length
  entry : ∀ (index : Nat) (typeIndex : U32),
    module.module.env.func_type_indices.val[index]? = some typeIndex →
      ∃ compiled source, module.functions.val[index]? = some compiled ∧
        sources[index]? = some source ∧
        FunctionCapacity module.profile module.module.env typeIndex source compiled

theorem ModuleCapacities.extend {before after : runtime.compiler.ExecutableModule} {sources}
    (certificate : ModuleCapacities before sources)
    (source : after.module = before.module) (profile : after.profile = before.profile)
    (preserved : after.functions.val.take before.functions.val.length = before.functions.val) :
    ModuleCapacities after sources := by
  refine ⟨by simpa only [source] using certificate.count, ?_⟩
  intro index typeIndex found
  obtain ⟨compiled, src, foundCode, sourceLookup, code⟩ := certificate.entry index typeIndex
    (by simpa only [source] using found)
  refine ⟨compiled, src, ?_, sourceLookup, by simpa only [source, profile] using code⟩
  have bound := (List.getElem?_eq_some_iff.mp foundCode).1
  have same := (List.getElem?_eq_some_iff.mp foundCode).2
  have retained := congrArg (fun list => list[index]?) preserved
  simpa [List.getElem?_take, bound, same] using retained
end Exec.Code

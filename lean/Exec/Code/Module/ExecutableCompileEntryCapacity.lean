import Exec.Code.Body.Capacity.ExecutableFunctionCapacity
import Exec.Code.Module.CompileEntryBounds
import Exec.Code.Local.Source.SourceBatchLookup
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The scheduler's actual entry construction, issued batch validation, and
finish establish the source-indexed capacity certificate. All compiler-state
premises are supplied by the checked entry proof. -/
theorem CompileEntryWitness.compile_executable_capacity {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness ops before after batch finalBatch)
    (law : Platform.AllocCorrect ops)
    {issued : StreamBatch.Issued} (reachable : StreamBatch.Reachable issued batch)
    (bounded : issued.Bounded) (origin : before.code_start.val ≤ limits.MAX_MODULE_BYTES.val)
    (signatureTable : SignatureSequence before.signatures.val batch.env.types.val)
    (functionTable : before.func_param_slots.val.map (fun word => word.val) =
      batch.env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    {finish : Usize}
    (entry : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      w.dispatched.code w.dispatched.env w.entry.index w.dispatched.validated_end finish
      w.initial w.final w.dispatched.profile)
    {source : List instr} (encoded : Profile.BodyEncoding w.dispatched.profile entry.body source)
    :
    FunctionCapacity batch.profile batch.env entry.typeIdx
      (.FUNC (.mk_uN entry.typeIdx.val)
        ((ModuleLocals.declared entry.groups).map Translate.valueType |>.map local.LOCAL) source) w.final.function := by
  have certificate := witness_executable_function_capacity ops law entry
    (signatures := before.signatures.deref) (functionSlots := before.func_param_slots.deref)
    (by simpa [alloc.vec.Vec.deref, w.metadata.1] using signatureTable)
    (by simpa [alloc.vec.Vec.deref, w.metadata.1] using functionTable)
    (w.end_fits reachable bounded origin entry) w.created encoded
    w.final.function w.final.budget w.finished
  simpa only [w.metadata.1, w.metadata.2.1] using certificate
/-- A successful scheduler entry is paired with the original module's exact
source function using only source framing and the actual issued-worker history. -/
theorem CompileEntryWitness.compile_executable_source_capacity {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness ops before after batch finalBatch)
    (law : Platform.AllocCorrect ops)
    {issued : StreamBatch.Issued} (reachable : StreamBatch.Reachable issued batch)
    (bounded : issued.Bounded) (origin : before.code_start.val ≤ limits.MAX_MODULE_BYTES.val)
    (bounds : CodeEntry.Bounds batch.env)
    (types : ∀ ft ∈ batch.env.types.val, Profile.FuncType batch.profile ft)
    (signatureTable : SignatureSequence before.signatures.val batch.env.types.val)
    (functionTable : before.func_param_slots.val.map (fun word => word.val) =
      batch.env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (raw : ModuleBinary.Module)
    (declarations : raw.functions = batch.env.func_type_indices.val)
    (prior taken remaining : List ModuleBinary.Code)
    (split : raw.codes = prior ++ taken ++ remaining)
    (first : issued.first_func.val = prior.length)
    (count : issued.num_funcs.val = taken.length)
    (encoded : ModuleBinary.Rep (Profile.CodeEncoding issued.profile) taken issued.code.val) :
    ∃ typeIndex source,
      batch.env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
      (sourceFunctions raw)[w.entry.index.val]? = some source ∧
      FunctionCapacity batch.profile batch.env typeIndex source w.final.function := by
  obtain ⟨finish, indexEq, entry, typed⟩ := w.typed bounds
  have dispatched := StreamBatch.Reachable.dispatch reachable w.dispatch
  have identity := dispatched.validation.1
  obtain ⟨_, _, envEq, codeEq, _, firstEq, countEq, profileEq⟩ := identity
  have countBound : w.dispatched.num_validated.val < taken.length := by
    have cases := stream.CodeBatch.validate_func.cases
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      w.dispatched finalBatch w.entry.index w.initial w.final (.Ok ()) w.validated
    rcases cases with ⟨error, _, impossible, _⟩ | ⟨_, error, _, impossible, _⟩ |
      ⟨_, finish, n, next, _⟩
    · cases impossible
    · cases impossible
    · have size := (stream.CodeBatch.validate_next.accepted _ _ _ _ _ _ next).1
      simpa only [countEq, count] using size
  have entryBounds : CodeEntry.Bounds w.dispatched.env := by simpa only [w.metadata.1] using bounds
  have entryTypes : ∀ ft ∈ w.dispatched.env.types.val, Profile.FuncType w.dispatched.profile ft := by
    simpa only [w.metadata.1, w.metadata.2.1] using types
  obtain ⟨rawEntry, found, groups, body⟩ := witness_batch_source_lookup entry dispatched entryBounds entryTypes encoded countBound
  have position : w.entry.index.val = prior.length + w.dispatched.num_validated.val := by
    have batchIdentity := reachable.validation.1
    have batchFirst := batchIdentity.2.2.2.2.2.1
    rw [indexEq, batchFirst, first, w.metadata.2.2.1]
  have rawFound : raw.codes[w.entry.index.val]? = some rawEntry := by
    rw [split, position]
    exact source_entry_offset found
  have rawMember : rawEntry ∈ raw.codes := List.mem_of_getElem? rawFound
  have typeFound : batch.env.func_type_indices.val[w.entry.index.val]? = some entry.typeIdx := by
    have found : w.dispatched.env.func_type_indices.val[w.entry.index.val]? = some entry.typeIdx := by
      simp only [List.getElem?_eq_getElem entry.index_lt, entry.index_type]
    simpa only [w.metadata.1] using found
  have certificate := w.compile_executable_capacity law reachable bounded origin signatureTable functionTable entry body

  refine ⟨entry.typeIdx, sourceFunctionCode entry.typeIdx rawEntry, typeFound,
    sourceFunctions_lookup (by simpa only [declarations] using typeFound) rawFound, ?_⟩
  simpa only [sourceFunctionCode, ModuleBinary.Code.declared, ModuleLocals.declared, groups, List.map_map, Function.comp_def] using certificate
end Exec.Code

import Itasca.Runtime.Compiler.Module.CompileSchedulerAssembly
import Itasca.Runtime.Compiler.Module.SchedulerCapacities
import Itasca.Runtime.Compiler.Module.SchedulerSubmission
import Itasca.Runtime.Compiler.Body.Capacity.ExecutableFunctionCapacity
import Itasca.Runtime.Compiler.Module.CompileEntry
import Itasca.Runtime.Compiler.Local.Source.SourceBatchLookup
import Itasca.Runtime.Compiler.Body.Capacity.FunctionCapacity
import Itasca.Runtime.Compiler.Local.Source.SourceSubmission
import Itasca.Runtime.Compiler.Module.CompileSourceSetup
import Itasca.Runtime.Compiler.Module.CompileSlice

/-!
Source-derived frame capacities through compiler entry, scheduler submission and module assembly. The resulting certificate relates issued compiled functions to independent source demand.
-/

/-! ## Capacity Assembly -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Initializer lowering appends synthetic functions without changing any
source function's retained frame-capacity bound. -/
theorem CompileWitness.defined_capacities {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes profile limits executable} (w : CompileWitness allocator bytes profile limits executable)
    (law : Platform.AllocCorrect allocator) {sources}
    (pending : PendingModuleCapacities profile w.env w.scheduler.functions.val sources) :
    ModuleCapacities executable sources := by
  have initialCode := pending.collected (uninitializedModule w.env w.tail profile w.functions) rfl rfl
    (w.function_order law)
  obtain ⟨source, selected, prefixCode, _⟩ := w.initializers law
  exact initialCode.extend source selected prefixCode

theorem CompileSourceCertificate.initial_capacities {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} {w : CompileWitness ops bytes profile limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) :
    PartialModuleCapacities profile w.env (sourceFunctions c.raw) c.run.remaining.configured.functions.val := by
  have prepared := compiler_driver_configured ops law c.run
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
  rw [prepared.2.2.1]
  apply PartialModuleCapacities.empty
  rw [source_functions_length (by rw [c.functions, c.codeCount]), c.functions]

theorem CompileSourceCertificate.capacities_of_submission {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} {w : CompileWitness ops bytes profile limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops)
    (ledger : PartialModuleCapacities profile w.env (sourceFunctions c.raw) c.run.remaining.submitted.functions.val) :
    ModuleCapacities executable (sourceFunctions c.raw) := by
  have after := compiler_driver_after_submission ops c.run.remaining
  have functions := congrArg runtime.compiler.CompileScheduler.functions after
  have final : PartialModuleCapacities profile w.env (sourceFunctions c.raw) w.scheduler.functions.val := by
    simpa only [functions] using ledger
  exact w.defined_capacities law (final.complete w.functions.val (w.function_order law))
end Itasca.Runtime.Compiler

end

/-! ## Capacity Submission -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- An actual batch run preserves the per-index ledger once its actual entry
witnesses have been certified. Reachability and fixed metadata are supplied to
the entry proof, rather than assumed again for each arbitrary worker. -/
theorem CompileEntries.capacities {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (run : CompileEntries allocator before batch after finalBatch)
    {profile : ValidationProfile} {env : module.Env} {sources : List funccode} {issued : StreamBatch.Issued}
    (reachable : StreamBatch.Reachable issued batch)
    (initial : PartialModuleCapacities profile env sources before.functions.val)
    (entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.CodeBatch),
      schedulerStatic current = schedulerStatic before → StreamBatch.Reachable issued worker →
      ∀ w : CompileEntryWitness allocator current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          sources[w.entry.index.val]? = some source ∧ FunctionCapacity profile env typeIndex source w.final.function) :
    PartialModuleCapacities profile env sources after.functions.val := by
  have result := run.fold
    (fun scheduler worker => schedulerStatic scheduler = schedulerStatic before ∧
      StreamBatch.Reachable issued worker ∧ PartialModuleCapacities profile env sources scheduler.functions.val)
    ⟨rfl, reachable, initial⟩ ?_
  · exact result.2.2
  · intro current worker next nextWorker invariant w
    obtain ⟨typeIndex, source, lookup, sourceLookup, code⟩ := entries current next worker nextWorker invariant.1 invariant.2.1 w
    exact ⟨w.static.trans invariant.1, w.reachable invariant.2.1,
      w.capacities invariant.2.2 typeIndex source lookup sourceLookup code⟩

/-- Submission's queue push changes no function slot. The ledger after a
successful real batch therefore contains every previously checked entry and
each newly certified entry at its issued index. -/
theorem compiler_submit_capacities {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before after : runtime.compiler.CompileScheduler A)
    (issued : StreamBatch.Issued) (profile : ValidationProfile) (env : module.Env) (sources : List funccode)
    (initial : PartialModuleCapacities profile env sources before.functions.val)
    (entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.CodeBatch),
      schedulerStatic current = schedulerStatic before → StreamBatch.Reachable issued worker →
      ∀ w : CompileEntryWitness allocator current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          sources[w.entry.index.val]? = some source ∧ FunctionCapacity profile env typeIndex source w.final.function)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
      allocator before issued.seed = .ok (.Ok (), after)) :
    PartialModuleCapacities profile env sources after.functions.val ∧ schedulerStatic after = schedulerStatic before := by
  obtain ⟨middle, worker, run, queue, same⟩ := compiler_submit_accepted allocator law before after issued.seed accepted
  have certificates := run.capacities .seed initial entries
  rw [same]
  exact ⟨certificates, run.static⟩

theorem compiler_poll_capacities {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (batch : stream.CodeBatch)
    {profile : ValidationProfile} {env : module.Env} {sources : List funccode} (initial : PartialModuleCapacities profile env sources before.functions.val)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch
      allocator before = .ok (.Ok batch, after)) :
    PartialModuleCapacities profile env sources after.functions.val ∧ schedulerStatic after = schedulerStatic before := by
  rw [(compiler_poll_accepted allocator before after batch accepted).2]
  exact ⟨initial, rfl⟩
end Itasca.Runtime.Compiler

end

/-! ## Executable Compile Entry Capacity -/

section

namespace Itasca.Runtime.Compiler
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
    source_functions_lookup (by simpa only [declarations] using typeFound) rawFound, ?_⟩
  simpa only [sourceFunctionCode, ModuleBinary.Code.declared, ModuleLocals.declared, groups, List.map_map, Function.comp_def] using certificate
end Itasca.Runtime.Compiler

end

/-! ## Scheduler Capacity -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Captured module tables and the exact source-indexed certificate ledger
retained throughout actual eager compilation and worker retirement. -/
structure SchedulerCapacity {A : Type} (profile : ValidationProfile) (env : module.Env) (sources : List funccode)
    (scheduler : runtime.compiler.CompileScheduler A) : Prop where
  signatures : SignatureSequence scheduler.signatures.val env.types.val
  functionSlots : scheduler.func_param_slots.val.map (fun word => word.val) =
    env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType))
  origin : scheduler.code_start.val ≤ limits.MAX_MODULE_BYTES.val
  functions : PartialModuleCapacities profile env sources scheduler.functions.val

theorem SchedulerCapacity.transport {A : Type} {profile env sources}
    {before after : runtime.compiler.CompileScheduler A}
    (initial : SchedulerCapacity profile env sources before)
    (same : schedulerStatic after = schedulerStatic before)
    (functions : PartialModuleCapacities profile env sources after.functions.val) :
    SchedulerCapacity profile env sources after := by
  have fields : after.signatures = before.signatures ∧ after.func_param_slots = before.func_param_slots ∧
      after.code_start = before.code_start := by simpa [schedulerStatic] using same
  exact ⟨by simpa only [fields.1] using initial.signatures,
    by simpa only [fields.2.1] using initial.functionSlots,
    by simpa only [fields.2.2] using initial.origin, functions⟩

end Itasca.Runtime.Compiler

end

/-! ## Executable Scheduler Capacity -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- A submitted batch's real entry calls are certified against exactly its
independently decoded source slice. The entry and opcode theorems discharge
every compiler-correctness obligation internally. -/
theorem scheduler_batch_executable_capacity {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (env : module.Env) (profile : ValidationProfile) (raw : ModuleBinary.Module)
    (declarations : raw.functions = env.func_type_indices.val)
    (bounds : CodeEntry.Bounds env)
    (types : ∀ ft ∈ env.types.val, Profile.FuncType profile ft)
    (before after : runtime.compiler.CompileScheduler A) (issued : StreamBatch.Issued)
    (prior taken remaining : List ModuleBinary.Code)
    (split : raw.codes = prior ++ taken ++ remaining)
    (sameEnv : issued.env = env) (selected : issued.profile = profile)
    (first : issued.first_func.val = prior.length) (count : issued.num_funcs.val = taken.length)
    (encoded : ModuleBinary.Rep (Profile.CodeEncoding profile) taken issued.code.val)
    (bounded : issued.Bounded) (initial : SchedulerCapacity profile env (sourceFunctions raw) before)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
      ops before issued.seed = .ok (.Ok (), after)) :
    SchedulerCapacity profile env (sourceFunctions raw) after := by
  have entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.CodeBatch),
      schedulerStatic current = schedulerStatic before → StreamBatch.Reachable issued worker →
      ∀ w : CompileEntryWitness ops current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          (sourceFunctions raw)[w.entry.index.val]? = some source ∧
          FunctionCapacity profile env typeIndex source w.final.function := by
    intro current next worker nextWorker static reachable w
    have fields : current.signatures = before.signatures ∧ current.func_param_slots = before.func_param_slots ∧
        current.code_start = before.code_start := by simpa [schedulerStatic] using static
    obtain ⟨_, _, workerEnv, _, _, _, _, workerProfile⟩ := reachable.validation.1
    have envEq : worker.env = env := workerEnv.trans sameEnv
    have profileEq : worker.profile = profile := workerProfile.trans selected
    have certificate := w.compile_executable_source_capacity law reachable bounded
      (by simpa only [fields.2.2] using initial.origin)
      (by simpa only [envEq] using bounds)
      (by simpa only [envEq, profileEq] using types)
      (by simpa only [fields.1, envEq] using initial.signatures)
      (by simpa only [fields.2.1, envEq] using initial.functionSlots)
      raw (by simpa only [envEq] using declarations) prior taken remaining split first count
      (by simpa only [selected] using encoded)
    simpa only [envEq, profileEq] using certificate
  obtain ⟨functions, same⟩ := compiler_submit_capacities ops law before after issued profile env (sourceFunctions raw)
    initial.functions entries accepted
  exact initial.transport same functions

/-- The actual streaming submission loop establishes certificates for every
populated slot of the original module source list. No callback, body relation,
or independently supplied compiler certificate is a premise. -/
theorem compiler_submit_executable_source_capacities {A S : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (source : stream.Source S) (state : S) (moduleId : U64)
    (env : module.Env) (code : Slice U8) (profile : ValidationProfile) (config : stream.Config)
    (raw : ModuleBinary.Module)
    (declarations : raw.functions = env.func_type_indices.val)
    (bounds : CodeEntry.Bounds env) (types : ∀ ft ∈ env.types.val, Profile.FuncType profile ft)
    (environment tail : List U8) (available : StreamSource.Available source state environment code.val tail)
    (capacity : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (start : Usize)
    (encoded : ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding profile)) code start raw.codes (Slice.len code))
    (count : raw.codes.length = env.func_type_indices.val.length)
    (before after : runtime.compiler.CompileScheduler A) (pending : alloc.vec.Vec Usize)
    (initial : SchedulerCapacity profile env (sourceFunctions raw) before)
    (accepted : stream.submit_code_batches source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      moduleId profile state env (Slice.len code) start config before = .ok (.Ok pending, after)) :
    SchedulerCapacity profile env (sourceFunctions raw) after := by
  apply SourceSubmission.submit source (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    state moduleId env code profile config raw.codes (SchedulerCapacity profile env (sourceFunctions raw))
    environment tail available capacity start encoded count ?_ ?_ before after pending initial accepted
  · intro current next issued prior taken remaining split moduleEq selected sameEnv first counted encoded bounded ready accepted
    exact scheduler_batch_executable_capacity ops law env profile raw declarations bounds types current next issued
      prior taken remaining split sameEnv selected first counted encoded bounded ready accepted
  · intro current next worker ready accepted
    obtain ⟨functions, same⟩ := compiler_poll_capacities ops current next worker ready.functions accepted
    exact ready.transport same functions
end Itasca.Runtime.Compiler

end

/-! ## Compile Executable Capacities -/

section

/-! Source-ordered executablecapacities certificates from the actual compiler driver.
Shared setup fixes reader coordinates; this module discharges its own submission fold. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual successful compilation establishes all defined-function source
certificates for the complete independently encoded profile. The scheduler,
reader, compiler callbacks and final assembly are discharged internally. -/
theorem CompileSourceCertificate.executable_capacities {A : Type} {ops : runtime.platform.Alloc A}
    {bytes profile limits executable} {w : CompileWitness ops bytes profile limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) :
    ModuleCapacities executable (sourceFunctions c.raw) := by
  obtain ⟨signatures,slots,origin⟩ := c.scheduler_setup law
  have initial : SchedulerCapacity profile w.env (sourceFunctions c.raw) c.run.remaining.configured :=
    ⟨signatures, slots, origin, c.initial_capacities law⟩
  have submitted := c.run.remaining.submit_call
  rw [c.code_length] at submitted
  have certified := compiler_submit_executable_source_capacities ops law
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    {bytes, code_start := w.codeStart, code_end := w.codeEnd} 0#u64
    w.env c.code profile c.run.remaining.config c.raw c.functions c.entryBounds
    c.environmentProfile.1 c.environment.val c.tail.val c.available c.codeBound
    c.run.remaining.entries c.entries c.codeCount c.run.remaining.configured c.run.remaining.submitted
    c.run.remaining.pending initial submitted
  exact c.capacities_of_submission law certified.functions

/-- Public compilation of a module in either complete profile produces
source-ordered frame-capacity certificates for the exact canonical module syntax. -/
theorem compile_executable_capacities {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : runtime.compiler.CompileLimits) (executable : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with ops bytes profile limits = .ok (.Ok executable)) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw) ∧
      ModuleElaboration.Matches executable.module.env executable.module.tail raw ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧ ModuleElaboration.Profile raw profile ∧
      ModuleElaboration.AccessorTypes executable.module.env raw ∧
      ModuleCapacities executable (sourceFunctions raw) ∧
      executable.profile = profile := by
  obtain ⟨w⟩ := compile_accepted ops bytes profile limits executable accepted
  obtain ⟨c⟩ := w.source_certificate law
  have certificates := c.executable_capacities law
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors⟩ := (w.source_validated law).1
  have same := Profile.module_unique encoded c.encoded
  subst raw
  exact ⟨c.raw, c.encoded, elaborated, matched, typed, restrictions, accessors,
    certificates, (w.initializers law).2.1⟩
end Itasca.Runtime.Compiler

end

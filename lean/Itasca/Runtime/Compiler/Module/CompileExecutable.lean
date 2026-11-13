import Itasca.Runtime.Compiler.Body.Relations.Entry.EntryBodyExecutable
import Itasca.Runtime.Compiler.Module.CompileEntry
import Itasca.Runtime.Compiler.Local.Initializer.InitializerExpressionAvailable
import Itasca.Runtime.Compiler.Module.ExecutableCollectedFunctions
import Itasca.Runtime.Compiler.Module.CompileAssembly
import Itasca.Runtime.Compiler.Module.CompileSourceCertificate
import Itasca.Runtime.Compiler.Module.CompileDriverFrame
import Itasca.Runtime.Compiler.Module.ExecutableSchedulerFunctions
import Itasca.Runtime.Compiler.Module.CompileSchedulerAssembly
import Itasca.Runtime.Compiler.Module.SchedulerSubmission
import Itasca.Runtime.Compiler.Local.Source.SourceSegmentPrograms
import Itasca.Runtime.Compiler.Module.CompileSourceSetup
import Itasca.Runtime.Compiler.Module.CompileSlice

/-!
Executable-function certificates through entry compilation, scheduler submission and whole-module assembly. The final result retains source function ordering and each compiled body certificate.
-/

/-! ## Compile Entry Executable -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The scheduler's actual entry construction, issued batch validation, and
finish establish the source-indexed function certificate. All compiler-state
premises are supplied by the checked entry proof. -/
theorem CompileEntryWitness.compile_executable {A : Type} {ops : runtime.platform.Alloc A}
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
      w.initial w.final)
    {source : List instr} (encoded : Profile.BodyEncoding entry.body source) :
    DefinedExecutableFunctionCode batch.env entry.typeIdx
      (.FUNC (.mk_uN entry.typeIdx.val)
        ((ModuleLocals.declared entry.groups).map Translate.valueType |>.map local.LOCAL) source) w.final.function := by
  have certificate := witness_compile_executable ops law entry
    (signatures := before.signatures.deref) (functionSlots := before.func_param_slots.deref)
    (by simpa [alloc.vec.Vec.deref, w.metadata.1] using signatureTable)
    (by simpa [alloc.vec.Vec.deref, w.metadata.1] using functionTable)
    (w.end_fits reachable bounded origin entry) w.created encoded
    w.final.function w.final.budget w.finished
  simpa only [w.metadata.1] using certificate
end Itasca.Runtime.Compiler

end

/-! ## Executable Compile Assembly -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
theorem CompileWitness.defined_executable_functions {A : Type} {allocator : runtime.platform.Alloc A}
    {bytes limits executable} (w : CompileWitness allocator bytes limits executable)
    (law : Platform.AllocCorrect allocator) {sources}
    (pending : PendingExecutableModuleFunctions w.env w.scheduler.functions.val sources) :
    ExecutableModuleFunctions executable sources ∧ InitializerMappings executable := by
  have initialCode := pending.collected (uninitializedModule w.env w.tail w.functions) rfl
    (w.function_order law)
  obtain ⟨source, prefixCode, initializers⟩ := w.initializers law
  exact ⟨initialCode.extend source prefixCode, initializers⟩
end Itasca.Runtime.Compiler

end

/-! ## Executable Compile Scheduler Assembly -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
theorem CompileSourceCertificate.initial_executable_functions {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} {w : CompileWitness ops bytes limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) :
    PartialExecutableModuleFunctions w.env (sourceFunctions c.raw) c.run.remaining.configured.functions.val := by
  have prepared := compiler_driver_configured ops law c.run
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
    (by simp [initialScheduler, alloc.vec.Vec.new])
  rw [prepared.2.2.1]
  apply PartialExecutableModuleFunctions.empty
  rw [source_functions_length (by rw [c.functions, c.codeCount]), c.functions]

/-- Once actual submission has filled the canonical ledger, the remaining
driver phases, collection and initializer lowering establish module coverage.
No further compiler relation or callback premise is required. -/
theorem CompileSourceCertificate.executable_functions_of_submission {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} {w : CompileWitness ops bytes limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops)
    (ledger : PartialExecutableModuleFunctions w.env (sourceFunctions c.raw) c.run.remaining.submitted.functions.val) :
    ExecutableModuleFunctions executable (sourceFunctions c.raw) ∧ InitializerMappings executable := by
  have after := compiler_driver_after_submission ops c.run.remaining
  have functions := congrArg runtime.compiler.CompileScheduler.functions after
  have final : PartialExecutableModuleFunctions w.env (sourceFunctions c.raw) w.scheduler.functions.val := by
    simpa only [functions] using ledger
  exact w.defined_executable_functions law (final.complete w.functions.val (w.function_order law))
end Itasca.Runtime.Compiler

end

/-! ## Executable Scheduler Submission -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
theorem CompileEntries.executable_functions {A : Type} {allocator : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (run : CompileEntries allocator before batch after finalBatch)
    {env : metadata.Env} {sources : List funccode} {issued : StreamBatch.Issued}
    (reachable : StreamBatch.Reachable issued batch)
    (initial : PartialExecutableModuleFunctions env sources before.functions.val)
    (entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.CodeBatch),
      schedulerStatic current = schedulerStatic before → StreamBatch.Reachable issued worker →
      ∀ w : CompileEntryWitness allocator current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          sources[w.entry.index.val]? = some source ∧ DefinedExecutableFunctionCode env typeIndex source w.final.function) :
    PartialExecutableModuleFunctions env sources after.functions.val := by
  have result := run.fold
    (fun scheduler worker => schedulerStatic scheduler = schedulerStatic before ∧
      StreamBatch.Reachable issued worker ∧ PartialExecutableModuleFunctions env sources scheduler.functions.val)
    ⟨rfl, reachable, initial⟩ ?_
  · exact result.2.2
  · intro current worker next nextWorker invariant w
    obtain ⟨typeIndex, source, lookup, sourceLookup, code⟩ := entries current next worker nextWorker invariant.1 invariant.2.1 w
    exact ⟨w.static.trans invariant.1, w.reachable invariant.2.1,
      w.executable_functions invariant.2.2 typeIndex source lookup sourceLookup code⟩

/-- Submission's queue push changes no function slot. The ledger after a
successful real batch therefore contains every previously checked entry and
each newly certified entry at its issued index. -/
theorem compiler_submit_executable_functions {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before after : runtime.compiler.CompileScheduler A)
    (issued : StreamBatch.Issued) (env : metadata.Env) (sources : List funccode)
    (initial : PartialExecutableModuleFunctions env sources before.functions.val)
    (entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.CodeBatch),
      schedulerStatic current = schedulerStatic before → StreamBatch.Reachable issued worker →
      ∀ w : CompileEntryWitness allocator current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          sources[w.entry.index.val]? = some source ∧ DefinedExecutableFunctionCode env typeIndex source w.final.function)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
      allocator before issued.seed = .ok (.Ok (), after)) :
    PartialExecutableModuleFunctions env sources after.functions.val ∧ schedulerStatic after = schedulerStatic before := by
  obtain ⟨middle, worker, run, queue, same⟩ := compiler_submit_accepted allocator law before after issued.seed accepted
  have certificates := run.executable_functions .seed initial entries
  rw [same]
  exact ⟨certificates, run.static⟩

theorem compiler_poll_executable_functions {A : Type} (allocator : runtime.platform.Alloc A)
    (before after : runtime.compiler.CompileScheduler A) (batch : stream.CodeBatch)
    {env : metadata.Env} {sources : List funccode} (initial : PartialExecutableModuleFunctions env sources before.functions.val)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch
      allocator before = .ok (.Ok batch, after)) :
    PartialExecutableModuleFunctions env sources after.functions.val ∧ schedulerStatic after = schedulerStatic before := by
  rw [(compiler_poll_accepted allocator before after batch accepted).2]
  exact ⟨initial, rfl⟩
end Itasca.Runtime.Compiler

end

/-! ## Source Compile Executable Entry -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- A successful scheduler entry is paired with the original module's exact
source function using only source framing and the actual issued-worker history. -/
theorem CompileEntryWitness.compile_source_executable {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.CompileScheduler A} {batch finalBatch : stream.CodeBatch}
    (w : CompileEntryWitness ops before after batch finalBatch)
    (law : Platform.AllocCorrect ops)
    {issued : StreamBatch.Issued} (reachable : StreamBatch.Reachable issued batch)
    (bounded : issued.Bounded) (origin : before.code_start.val ≤ limits.MAX_MODULE_BYTES.val)
    (bounds : CodeEntry.Bounds batch.env)
    (signatureTable : SignatureSequence before.signatures.val batch.env.types.val)
    (functionTable : before.func_param_slots.val.map (fun word => word.val) =
      batch.env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (raw : ModuleBinary.Module)
    (declarations : raw.functions = batch.env.func_type_indices.val)
    (prior taken remaining : List ModuleBinary.Code)
    (split : raw.codes = prior ++ taken ++ remaining)
    (first : issued.first_func.val = prior.length)
    (count : issued.num_funcs.val = taken.length)
    (encoded : ModuleBinary.Rep (Profile.CodeEncoding) taken issued.code.val) :
    ∃ typeIndex source,
      batch.env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
      (sourceFunctions raw)[w.entry.index.val]? = some source ∧
      DefinedExecutableFunctionCode batch.env typeIndex source w.final.function := by
  obtain ⟨finish, indexEq, entry, typed⟩ := w.typed bounds
  have dispatched := StreamBatch.Reachable.dispatch reachable w.dispatch
  have identity := dispatched.validation.1
  obtain ⟨_, _, envEq, codeEq, _, firstEq, countEq⟩ := identity
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
  obtain ⟨rawEntry, found, groups, body⟩ := witness_batch_source_lookup entry dispatched entryBounds encoded countBound
  have position : w.entry.index.val = prior.length + w.dispatched.num_validated.val := by
    have batchIdentity := reachable.validation.1
    have batchFirst := batchIdentity.2.2.2.2.2.1
    rw [indexEq, batchFirst, first, w.metadata.2.1]
  have rawFound : raw.codes[w.entry.index.val]? = some rawEntry := by
    rw [split, position]
    exact source_entry_offset found
  have rawMember : rawEntry ∈ raw.codes := List.mem_of_getElem? rawFound
  have typeFound : batch.env.func_type_indices.val[w.entry.index.val]? = some entry.typeIdx := by
    have found : w.dispatched.env.func_type_indices.val[w.entry.index.val]? = some entry.typeIdx := by
      simp only [List.getElem?_eq_getElem entry.index_lt, entry.index_type]
    simpa only [w.metadata.1] using found
  have certificate := w.compile_executable law reachable bounded origin signatureTable functionTable entry body
  refine ⟨entry.typeIdx, sourceFunctionCode entry.typeIdx rawEntry, typeFound,
    source_functions_lookup (by simpa only [declarations] using typeFound) rawFound, ?_⟩
  simpa only [sourceFunctionCode, ModuleBinary.Code.declared, ModuleLocals.declared, groups, List.map_map, Function.comp_def] using certificate
end Itasca.Runtime.Compiler

end

/-! ## Scheduler Executable -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Captured module tables and the exact source-indexed certificate ledger
retained throughout actual eager compilation and worker retirement. -/
structure SchedulerExecutable {A : Type} (env : metadata.Env) (sources : List funccode)
    (scheduler : runtime.compiler.CompileScheduler A) : Prop where
  signatures : SignatureSequence scheduler.signatures.val env.types.val
  functionSlots : scheduler.func_param_slots.val.map (fun word => word.val) =
    env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType))
  origin : scheduler.code_start.val ≤ limits.MAX_MODULE_BYTES.val
  functions : PartialExecutableModuleFunctions env sources scheduler.functions.val

theorem SchedulerExecutable.transport {A : Type} {env sources}
    {before after : runtime.compiler.CompileScheduler A}
    (initial : SchedulerExecutable env sources before)
    (same : schedulerStatic after = schedulerStatic before)
    (functions : PartialExecutableModuleFunctions env sources after.functions.val) :
    SchedulerExecutable env sources after := by
  have fields : after.signatures = before.signatures ∧ after.func_param_slots = before.func_param_slots ∧
      after.code_start = before.code_start := by simpa [schedulerStatic] using same
  exact ⟨by simpa only [fields.1] using initial.signatures,
    by simpa only [fields.2.1] using initial.functionSlots,
    by simpa only [fields.2.2] using initial.origin, functions⟩

/-- A submitted batch's real entry calls are certified against exactly its
independently decoded source slice. The entry and opcode theorems discharge
every compiler-correctness obligation internally. -/
theorem scheduler_batch_executable {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (env : metadata.Env) (raw : ModuleBinary.Module)
    (declarations : raw.functions = env.func_type_indices.val)
    (bounds : CodeEntry.Bounds env)
    (before after : runtime.compiler.CompileScheduler A) (issued : StreamBatch.Issued)
    (prior taken remaining : List ModuleBinary.Code)
    (split : raw.codes = prior ++ taken ++ remaining)
    (sameEnv : issued.env = env)
    (first : issued.first_func.val = prior.length) (count : issued.num_funcs.val = taken.length)
    (encoded : ModuleBinary.Rep (Profile.CodeEncoding) taken issued.code.val)
    (bounded : issued.Bounded) (initial : SchedulerExecutable env (sourceFunctions raw) before)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
      ops before issued.seed = .ok (.Ok (), after)) :
    SchedulerExecutable env (sourceFunctions raw) after := by
  have entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.CodeBatch),
      schedulerStatic current = schedulerStatic before → StreamBatch.Reachable issued worker →
      ∀ w : CompileEntryWitness ops current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          (sourceFunctions raw)[w.entry.index.val]? = some source ∧
          DefinedExecutableFunctionCode env typeIndex source w.final.function := by
    intro current next worker nextWorker static reachable w
    have fields : current.signatures = before.signatures ∧ current.func_param_slots = before.func_param_slots ∧
        current.code_start = before.code_start := by simpa [schedulerStatic] using static
    obtain ⟨_, _, workerEnv, _, _, _, _⟩ := reachable.validation.1
    have envEq : worker.env = env := workerEnv.trans sameEnv
    have certificate := w.compile_source_executable law reachable bounded
      (by simpa only [fields.2.2] using initial.origin)
      (by simpa only [envEq] using bounds)
      (by simpa only [fields.1, envEq] using initial.signatures)
      (by simpa only [fields.2.1, envEq] using initial.functionSlots)
      raw (by simpa only [envEq] using declarations) prior taken remaining split first count
      encoded
    simpa only [envEq] using certificate
  obtain ⟨functions, same⟩ := compiler_submit_executable_functions ops law before after issued env (sourceFunctions raw)
    initial.functions entries accepted
  exact initial.transport same functions

/-- The actual streaming submission loop establishes certificates for every
populated slot of the original module source list. No callback, body relation,
or independently supplied compiler certificate is a premise. -/
theorem compiler_submit_source_executable_functions {A S : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (source : stream.Source S) (state : S) (moduleId : U64)
    (env : metadata.Env) (code : Slice U8) (config : stream.Config)
    (raw : ModuleBinary.Module)
    (declarations : raw.functions = env.func_type_indices.val)
    (bounds : CodeEntry.Bounds env)
    (environment tail : List U8) (available : StreamSource.Available source state environment code.val tail)
    (capacity : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (start : Usize)
    (encoded : ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding)) code start raw.codes (Slice.len code))
    (count : raw.codes.length = env.func_type_indices.val.length)
    (before after : runtime.compiler.CompileScheduler A) (pending : alloc.vec.Vec Usize)
    (initial : SchedulerExecutable env (sourceFunctions raw) before)
    (accepted : stream.submit_code_batches source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      moduleId state env (Slice.len code) start config before = .ok (.Ok pending, after)) :
    SchedulerExecutable env (sourceFunctions raw) after := by
  apply SourceSubmission.submit source (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    state moduleId env code config raw.codes (SchedulerExecutable env (sourceFunctions raw))
    environment tail available capacity start encoded count ?_ ?_ before after pending initial accepted
  · intro current next issued prior taken remaining split moduleEq sameEnv first counted encoded bounded ready accepted
    exact scheduler_batch_executable ops law env raw declarations bounds current next issued
      prior taken remaining split sameEnv first counted encoded bounded ready accepted
  · intro current next worker ready accepted
    obtain ⟨functions, same⟩ := compiler_poll_executable_functions ops current next worker ready.functions accepted
    exact ready.transport same functions
end Itasca.Runtime.Compiler

end

/-! ## Compile Executable -/

section

/-! Source-ordered executable certificates from the actual compiler driver.
Shared setup fixes reader coordinates; this module discharges its own submission fold. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
theorem CompileSourceCertificate.executable_functions {A : Type} {ops : runtime.platform.Alloc A}
    {bytes limits executable} {w : CompileWitness ops bytes limits executable}
    (c : CompileSourceCertificate w) (law : Platform.AllocCorrect ops) :
    ExecutableModuleFunctions executable (sourceFunctions c.raw) ∧ InitializerMappings executable := by
  obtain ⟨signatures,slots,origin⟩ := c.scheduler_setup law
  have initial : SchedulerExecutable w.env (sourceFunctions c.raw) c.run.remaining.configured :=
    ⟨signatures, slots, origin, c.initial_executable_functions law⟩
  have submitted := c.run.remaining.submit_call
  rw [c.code_length] at submitted
  have certified := compiler_submit_source_executable_functions ops law
    runtime.compiler.CompileSource.Insts.ItascaStreamSource
    {bytes, code_start := w.codeStart, code_end := w.codeEnd} 0#u64
    w.env c.code c.run.remaining.config c.raw c.functions c.entryBounds
    c.environment.val c.tail.val c.available c.codeBound
    c.run.remaining.entries c.entries c.codeCount c.run.remaining.configured c.run.remaining.submitted
    c.run.remaining.pending initial submitted
  exact c.executable_functions_of_submission law certified.functions

/-- Public successful compilation produces
source-ordered certificates for the exact canonical module syntax. -/
theorem compile_executable_functions {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) (executable : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with ops bytes limits = .ok (.Ok executable)) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding) raw bytes.val ∧
      ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw) ∧
      ModuleElaboration.Matches executable.module.env executable.module.tail raw ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧ ModuleElaboration.Restrictions raw ∧
      ModuleElaboration.AccessorTypes executable.module.env raw ∧
      ExecutableModuleFunctions executable (sourceFunctions raw) ∧ InitializerMappings executable := by
  obtain ⟨w⟩ := compile_accepted ops bytes limits executable accepted
  obtain ⟨c⟩ := w.source_certificate law
  have certificates := c.executable_functions law
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors⟩ := (w.source_validated law).1
  have same := ModuleBinary.ModuleEncodingWith.unique Profile.code_prefix_unique encoded c.encoded
  subst raw
  exact ⟨c.raw, c.encoded, elaborated, matched, typed, restrictions, accessors,
    certificates.1, certificates.2⟩
end Itasca.Runtime.Compiler

end

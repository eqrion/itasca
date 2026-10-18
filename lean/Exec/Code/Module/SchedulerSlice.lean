import Exec.Code.Module.SchedulerSubmission
import Exec.Code.Module.SourceCompileEntry
import Exec.Code.Local.Source.SourceSubmission
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Captured module tables and the exact source-indexed certificate ledger
retained throughout actual eager compilation and worker retirement. -/
structure SchedulerSlice {A : Type} (env : module.Env) (sources : List funccode)
    (scheduler : runtime.compiler.CompileScheduler A) : Prop where
  signatures : SignatureSequence scheduler.signatures.val env.types.val
  functionSlots : scheduler.func_param_slots.val.map (fun word => word.val) =
    env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType))
  origin : scheduler.code_start.val ≤ limits.MAX_MODULE_BYTES.val
  functions : PartialModuleFunctions env sources scheduler.functions.val

theorem SchedulerSlice.transport {A : Type} {env sources}
    {before after : runtime.compiler.CompileScheduler A}
    (initial : SchedulerSlice env sources before)
    (same : schedulerStatic after = schedulerStatic before)
    (functions : PartialModuleFunctions env sources after.functions.val) :
    SchedulerSlice env sources after := by
  have fields : after.signatures = before.signatures ∧ after.func_param_slots = before.func_param_slots ∧
      after.code_start = before.code_start := by simpa [schedulerStatic] using same
  exact ⟨by simpa only [fields.1] using initial.signatures,
    by simpa only [fields.2.1] using initial.functionSlots,
    by simpa only [fields.2.2] using initial.origin, functions⟩

/-- A submitted batch's real entry calls are certified against exactly its
independently decoded source slice. The entry and opcode theorems discharge
every compiler-correctness obligation internally. -/
theorem scheduler_batch_slice {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (env : module.Env) (profile : ValidationProfile) (raw : ModuleBinary.Module)
    (subset : ModuleSlice raw) (declarations : raw.functions = env.func_type_indices.val)
    (bounds : CodeEntry.Bounds env)
    (types : ∀ ft ∈ env.types.val, Profile.FuncType profile ft)
    (before after : runtime.compiler.CompileScheduler A) (issued : StreamBatch.Issued)
    (prior taken remaining : List ModuleBinary.Code)
    (split : raw.codes = prior ++ taken ++ remaining)
    (sameEnv : issued.env = env) (selected : issued.profile = profile)
    (first : issued.first_func.val = prior.length) (count : issued.num_funcs.val = taken.length)
    (encoded : ModuleBinary.Rep (Profile.CodeEncoding profile) taken issued.code.val)
    (bounded : issued.Bounded) (initial : SchedulerSlice env (sourceFunctions raw) before)
    (accepted : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
      ops before issued.seed = .ok (.Ok (), after)) :
    SchedulerSlice env (sourceFunctions raw) after := by
  have entries : ∀ (current next : runtime.compiler.CompileScheduler A) (worker nextWorker : stream.CodeBatch),
      schedulerStatic current = schedulerStatic before → StreamBatch.Reachable issued worker →
      ∀ w : CompileEntryWitness ops current next worker nextWorker,
        ∃ typeIndex source, env.func_type_indices.val[w.entry.index.val]? = some typeIndex ∧
          (sourceFunctions raw)[w.entry.index.val]? = some source ∧
          DefinedFunctionCode env typeIndex source w.final.function := by
    intro current next worker nextWorker static reachable w
    have fields : current.signatures = before.signatures ∧ current.func_param_slots = before.func_param_slots ∧
        current.code_start = before.code_start := by simpa [schedulerStatic] using static
    obtain ⟨_, _, workerEnv, _, _, _, _, workerProfile⟩ := reachable.validation.1
    have envEq : worker.env = env := workerEnv.trans sameEnv
    have profileEq : worker.profile = profile := workerProfile.trans selected
    have certificate := w.compile_source_slice law reachable bounded
      (by simpa only [fields.2.2] using initial.origin)
      (by simpa only [envEq] using bounds)
      (by simpa only [envEq, profileEq] using types)
      (by simpa only [fields.1, envEq] using initial.signatures)
      (by simpa only [fields.2.1, envEq] using initial.functionSlots)
      raw subset (by simpa only [envEq] using declarations) prior taken remaining split first count
      (by simpa only [selected] using encoded)
    simpa only [envEq] using certificate
  obtain ⟨functions, same⟩ := compiler_submit_functions ops law before after issued env (sourceFunctions raw)
    initial.functions entries accepted
  exact initial.transport same functions

/-- The actual streaming submission loop establishes certificates for every
populated slot of the original module source list. No callback, body relation,
or independently supplied compiler certificate is a premise. -/
theorem compiler_submit_source_functions {A S : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (source : stream.Source S) (state : S) (moduleId : U64)
    (env : module.Env) (code : Slice U8) (profile : ValidationProfile) (config : stream.Config)
    (raw : ModuleBinary.Module) (subset : ModuleSlice raw)
    (declarations : raw.functions = env.func_type_indices.val)
    (bounds : CodeEntry.Bounds env) (types : ∀ ft ∈ env.types.val, Profile.FuncType profile ft)
    (environment tail : List U8) (available : StreamSource.Available source state environment code.val tail)
    (capacity : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (start : Usize)
    (encoded : ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding profile)) code start raw.codes (Slice.len code))
    (count : raw.codes.length = env.func_type_indices.val.length)
    (before after : runtime.compiler.CompileScheduler A) (pending : alloc.vec.Vec Usize)
    (initial : SchedulerSlice env (sourceFunctions raw) before)
    (accepted : stream.submit_code_batches source
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      moduleId profile state env (Slice.len code) start config before = .ok (.Ok pending, after)) :
    SchedulerSlice env (sourceFunctions raw) after := by
  apply SourceSubmission.submit source (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
    state moduleId env code profile config raw.codes (SchedulerSlice env (sourceFunctions raw))
    environment tail available capacity start encoded count ?_ ?_ before after pending initial accepted
  · intro current next issued prior taken remaining split moduleEq selected sameEnv first counted encoded bounded ready accepted
    exact scheduler_batch_slice ops law env profile raw subset declarations bounds types current next issued
      prior taken remaining split sameEnv selected first counted encoded bounded ready accepted
  · intro current next worker ready accepted
    obtain ⟨functions, same⟩ := compiler_poll_functions ops current next worker ready.functions accepted
    exact ready.transport same functions
end Exec.Code

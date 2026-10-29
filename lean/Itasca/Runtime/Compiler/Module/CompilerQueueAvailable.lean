import Itasca.Runtime.Compiler.Module.CompileSubmit
import Mathlib.Data.List.Forall2
import Itasca.Runtime.Compiler.Module.PreparedBatchSource
import Itasca.Runtime.Compiler.Module.SourceEntryPrepared
import Itasca.Runtime.Compiler.Module.BatchLoopAvailable
import Itasca.Runtime.Compiler.Module.SourceQueuePolicy
import Itasca.Runtime.Compiler.Module.SchedulerSubmission

/-!
Compiler queue availability and completed-worker collection. Prepared batch encoding and successful submission establish the retained queue readiness certificate.
-/

/-! ## Completed Worker Queue -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- A queued worker retains its issued identity and a proved successful finish. -/
def CompletedWorker (issued : StreamBatch.Issued) (worker : Itasca.stream.CodeBatch) : Prop :=
  StreamBatch.Identity issued worker ∧ Itasca.stream.CodeBatch.finish worker = .ok (.Ok ())

/-- The actual reverse-order poll selects the final logical issued worker. -/
theorem completed_workers_last {queue : List StreamBatch.Issued} {workers : List Itasca.stream.CodeBatch}
    (related : List.Forall₂ CompletedWorker queue workers) (nonempty : queue ≠ []) :
    ∃ issued rest worker previous, queue = rest++[issued] ∧ workers = previous++[worker] ∧
      List.Forall₂ CompletedWorker rest previous ∧ CompletedWorker issued worker := by
  induction related with
  | nil => exact False.elim (nonempty rfl)
  | @cons issued worker queue workers same related ih =>
    by_cases empty : queue = []
    · subst queue
      cases related
      exact ⟨issued,[],worker,[],rfl,rfl,.nil,same⟩
    · obtain ⟨last,rest,final,previous,queueEq,workersEq,paired,ready⟩ := ih empty
      exact ⟨last,issued::rest,final,worker::previous,by simp only [queueEq,List.cons_append],
        by simp only [workersEq,List.cons_append],.cons same paired,ready⟩

/-- Appending the actual successful worker retains the complete queue relation. -/
theorem completed_workers_append {queue workers issued worker}
    (held : List.Forall₂ CompletedWorker queue workers) (ready : CompletedWorker issued worker) :
    List.Forall₂ CompletedWorker (queue++[issued]) (workers++[worker]) :=
  List.rel_append held (.cons ready .nil)

end Itasca.Runtime.Compiler

end

/-! ## Prepared Batch Encoding -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

private def sourceOrdinal (env : module.Env) (index : Nat)
    (bounded : index < env.func_type_indices.val.length) : Usize :=
  Usize.ofNatCore index (by have cap := env.func_type_indices.property; scalar_tac)

/-- Independent entry encoding and typing construct the prepared source
sequence. The remaining assumptions bound only pure source preparation and
independently validated operand demand. -/
theorem PreparedBatchSource.of_encoded (data : Slice U8) (env : module.Env) (profile : ValidationProfile)
    (bodyBytes localCount peak index : Nat) (start finish : Usize) (entries : List ModuleBinary.Code)
    (typed : ModuleCode.EntriesTyped (profile := profile) env index entries)
    (encoded : ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncodingWithinLimits profile)) data start entries finish)
    (bounds : CodeEntry.Bounds env) (environment : Profile.Environment profile env)
    (limits : Profile.EnvironmentWithinLimits env)
    (maxima : ∀ (ordinal position next : Usize) (entry : ModuleBinary.Code),
      ModuleBinary.At (Profile.CodeEncodingWithinLimits profile) data position entry next →
      ∀ w : CodeEntry.Prepared data env ordinal position profile, w.finish = next →
      Profile.Body profile w.body env w.ctx.locals w.typeIdx →
      w.body.length ≤ bodyBytes ∧ w.ctx.locals.val.length ≤ localCount ∧
      (independentBodyDemand w.body env w.ctx w.typeIdx).operands ≤ peak) :
    PreparedBatchSource data env profile bodyBytes localCount peak index start entries finish := by
  induction entries generalizing index start with
  | nil =>
    have same := encoded.rep_nil
    subst finish
    exact .nil index start
  | cons entry entries ih =>
    cases typed with
    | cons head rest =>
      obtain ⟨indexBound,entryTyped,_⟩ := head
      have fullTyped := Profile.EntryTyped.of_core entryTyped (environment.1 _ (List.getElem_mem _))
      let ordinal := sourceOrdinal env index indexBound
      have value : ordinal.val = index := rfl
      obtain ⟨next,entryBytes,remaining⟩ := encoded.rep_cons
      obtain ⟨w,ending,body⟩ := source_entry_prepared data env ordinal start next profile entry
        (by simpa only [value] using indexBound) (by simpa only [value] using fullTyped)
        bounds environment limits entryBytes
      obtain ⟨bytes,locals,operands⟩ := maxima ordinal start next entry entryBytes w ending body
      exact .cons ordinal value (by simpa only [value] using indexBound) (by simpa only [value] using fullTyped)
        entryBytes w ending bytes locals operands (ih (index+1) next rest remaining)

end Itasca.Runtime.Compiler

end

/-! ## Submit Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Eager submission compiles every independently prepared source entry,
publishes its completed worker, and retains aggregate numerical resource and
source-slot invariants. Queue publication uses bounded allocation availability. -/
theorem compiler_submit_batch_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (base : runtime.compiler.Budget A) (bodyBytes localCount peak : Nat)
    (before : runtime.compiler.CompileScheduler A) (issued : StreamBatch.Issued)
    (entries : List ModuleBinary.Code)
    (source : PreparedBatchSource issued.code issued.env issued.profile bodyBytes localCount peak
      issued.first_func.val 0#usize entries (Slice.len issued.code))
    (count : entries.length = issued.num_funcs.val) (bounded : issued.Bounded)
    (envelope : FunctionDemandEnvelope base issued.env.func_type_indices.val.length bodyBytes localCount peak bound)
    (paid : CompilationBudgetEffect base before.budget
      (fun counter => issued.first_func.val*functionDemandRate bodyBytes localCount counter))
    (slots : FunctionSlotPrefix issued.env.func_type_indices.val.length issued.first_func.val before.functions.val)
    (bounds : CodeEntry.Bounds issued.env) (environment : Profile.Environment issued.profile issued.env)
    (limits : Profile.EnvironmentWithinLimits issued.env)
    (signatures : SignatureSequence before.signatures.val issued.env.types.val)
    (functionSlots : before.func_param_slots.val.map (fun word => word.val) =
      issued.env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (origin : before.code_start.val ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (queueCapacity : before.completed.length < Usize.max) (queueReserve : before.completed.length+1 ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch ops before issued.seed
      ⦃ out => out.1 = .Ok () ∧
        FunctionSlotPrefix issued.env.func_type_indices.val.length (issued.first_func.val+issued.num_funcs.val) out.2.functions.val ∧
        CompilationBudgetEffect base out.2.budget
          (fun counter => (issued.first_func.val+issued.num_funcs.val)*functionDemandRate bodyBytes localCount counter) ∧
        ∃ worker, out.2.completed.val = before.completed.val++[worker] ∧
          Itasca.stream.CodeBatch.finish worker = .ok (.Ok ()) ⦄ := by
  have arithmetic : before.code_start.val+issued.code_offset.val+issued.code.length ≤ Usize.max := by
    have wordRoom : Itasca.limits.MAX_MODULE_BYTES.val+Itasca.limits.MAX_MODULE_BYTES.val ≤ Usize.max := by
      simp only [Itasca.limits.MAX_MODULE_BYTES]
      scalar_tac
    have coordinates := bounded.2.2
    omega
  obtain ⟨middle,worker,compiled,validated,ended,noError,queue,published,charged⟩ := compiler_batch_loop_available ops law bound allocation
    base bodyBytes localCount peak before issued.seed 0#usize (Slice.len issued.code) entries
    (by simpa only [StreamBatch.Issued.seed,show (0#usize).val = 0 from rfl,Nat.add_zero] using source)
    envelope (by simpa [StreamBatch.Issued.seed] using paid) (by simpa [StreamBatch.Issued.seed] using slots)
    rfl rfl rfl rfl (by simpa [StreamBatch.Issued.seed] using count) bounded.2.1 bounds environment limits signatures functionSlots bounded.2.2 arithmetic
  have run := (submit_loop_accepted ops before middle issued.seed worker 0#usize (.Ok ()) compiled).2
  have identity := (run.reachable .seed).validation.1
  obtain ⟨_,_,_,sameCode,_,_,sameCount,_⟩ := identity
  have finished : Itasca.stream.CodeBatch.finish worker = .ok (.Ok ()) := by
    apply (Itasca.stream.CodeBatch.finish.accepted_iff worker).mpr
    exact ⟨noError,validated.trans sameCount.symm,ended.trans (by rw [sameCode])⟩
  obtain ⟨⟨reply,budget,completed⟩,pushed,status,sameBudget,appended⟩ := WP.spec_imp_exists
    (budget_push_available ops bound allocation middle.budget middle.completed worker
      (by simpa only [queue] using queueCapacity) (by simpa only [queue] using queueReserve))
  dsimp only at status sameBudget appended
  subst reply budget
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
  rw [compiled]
  simp only [submitPack,bind_ok,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,pushed,
    runtime.compiler.visitor_result,WP.spec_ok]
  refine ⟨True.intro,published,charged,worker,?_,finished⟩
  rw [appended,queue]

end Itasca.Runtime.Compiler

end

/-! ## Compiler Queue Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- Source-only maxima for independently encoded valid prepared entries. These
bounds concern source bytes, expanded locals, and the independent operand
analysis; they never quantify over compiler runs or emitted certificates. -/
def SourcePreparationMaxima (env : module.Env) (profile : ValidationProfile)
    (bodyBytes localCount peak : Nat) : Prop :=
  ∀ (data : Slice U8) (ordinal position next : Usize) (entry : ModuleBinary.Code),
    ModuleBinary.At (Profile.CodeEncodingWithinLimits profile) data position entry next →
    ∀ w : CodeEntry.Prepared data env ordinal position profile, w.finish = next →
    Profile.Body profile w.body env w.ctx.locals w.typeIdx →
    w.body.length ≤ bodyBytes ∧ w.ctx.locals.val.length ≤ localCount ∧
    (independentBodyDemand w.body env w.ctx w.typeIdx).operands ≤ peak

/-- The compiler's local numerical and publication state at the source cursor. -/
structure SchedulerCompilationReady {A : Type} (env : module.Env) (base : runtime.compiler.Budget A)
    (bodyBytes localCount cursor : Nat) (scheduler : runtime.compiler.CompileScheduler A) : Prop where
  signatures : SignatureSequence scheduler.signatures.val env.types.val
  functionSlots : scheduler.func_param_slots.val.map (fun word => word.val) =
    env.func_types.val.map (fun ty => signatureSlots ty.params.val)
  origin : scheduler.code_start.val ≤ Itasca.limits.MAX_MODULE_BYTES.val
  slots : FunctionSlotPrefix env.func_type_indices.val.length cursor scheduler.functions.val
  paid : CompilationBudgetEffect base scheduler.budget
    (fun counter => cursor*functionDemandRate bodyBytes localCount counter)

/-- Completed workers remain paired with their exact issued identities while
source slots and the aggregate module budget advance independently of polling. -/
def CompilerQueued {A : Type} (env : module.Env) (base : runtime.compiler.Budget A)
    (bodyBytes localCount : Nat) (_id : U64) (queue : List StreamBatch.Issued)
    (cursor : Nat) (scheduler : runtime.compiler.CompileScheduler A) : Prop :=
  SchedulerCompilationReady env base bodyBytes localCount cursor scheduler ∧
    List.Forall₂ CompletedWorker queue scheduler.completed.val

private theorem four_room (length : Nat) (bounded : length < 4) : length < Usize.max := by
  have room : 4 ≤ Usize.max := by scalar_tac
  omega

/-- The concrete eager compiler satisfies a local accepting queue policy under
independent source maxima, aggregate numerical demand, and allocation
availability. The policy uses actual compiler workers and reverse-order polls. -/
theorem compiler_queue_policy {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (env : module.Env) (profile : ValidationProfile) (base : runtime.compiler.Budget A)
    (bodyBytes localCount peak : Nat)
    (envelope : FunctionDemandEnvelope base env.func_type_indices.val.length bodyBytes localCount peak bound)
    (maxima : SourcePreparationMaxima env profile bodyBytes localCount peak)
    (queueRoom : 4 ≤ bound) :
    StreamAvailability.QueuePolicy (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      ⟨25000#usize,4#usize⟩ env profile (CompilerQueued env base bodyBytes localCount) := by
  constructor
  · decide
  · decide
  · intro id queue cursor issued before held valid sameEnv moduleId first queueCapacity
    obtain ⟨ready,workers⟩ := held
    obtain ⟨entries,count,typed,encoded⟩ := valid.entries
    have selected := valid.validation_profile
    have source := PreparedBatchSource.of_encoded issued.code issued.env issued.profile bodyBytes localCount peak
      issued.first_func.val 0#usize (Slice.len issued.code) entries
      (by simpa only [selected] using typed) ⟨issued.code.val,by simpa only [selected] using encoded,by constructor <;> simp⟩
      valid.entry_bounds (by simpa only [selected] using valid.profile) (by simpa only [selected] using valid.limits)
      (by cases sameEnv; cases selected; exact maxima issued.code)
    have length := workers.length_eq
    have capacity : before.completed.length < 4 := by
      simpa only [alloc.vec.Vec.length,show (4#usize).val = 4 from rfl] using length ▸ queueCapacity
    obtain ⟨⟨reply,after⟩,called,status,slots,paid,worker,queueEq,finished⟩ := WP.spec_imp_exists
      (compiler_submit_batch_available ops law bound allocation base bodyBytes localCount peak before issued entries source count valid.bounded
        (by simpa only [sameEnv] using envelope) (by simpa only [sameEnv,first] using ready.paid)
        (by simpa only [sameEnv,first] using ready.slots) valid.entry_bounds
        (by simpa only [selected] using valid.profile) (by simpa only [selected] using valid.limits)
        (by simpa only [sameEnv] using ready.signatures) (by simpa only [sameEnv] using ready.functionSlots) ready.origin
        (four_room _ capacity) (by omega))
    dsimp only at status slots paid queueEq finished
    subst reply
    obtain ⟨middle,actual,run,actualQueue,shape⟩ := compiler_submit_accepted ops law before after issued.seed called
    have sameWorker : actual = worker := by
      rw [queueEq] at actualQueue
      exact List.cons.inj (List.append_cancel_left actualQueue.symm) |>.1
    subst actual
    have identity := (run.reachable .seed).validation.1
    have static : schedulerStatic after = schedulerStatic before := by rw [shape]; exact run.static
    have fields : after.signatures = before.signatures ∧ after.func_param_slots = before.func_param_slots ∧
        after.code_start = before.code_start := by simpa only [schedulerStatic,Prod.mk.injEq] using static
    refine ⟨after,called,⟨?_,?_⟩⟩
    · exact ⟨by simpa only [fields.1] using ready.signatures,by simpa only [fields.2.1] using ready.functionSlots,
        by simpa only [fields.2.2] using ready.origin,by simpa only [sameEnv,first] using slots,
        by simpa only [sameEnv,first] using paid⟩
    · rw [queueEq]
      exact completed_workers_append workers ⟨identity,finished⟩
  · intro id queue cursor before held nonempty
    obtain ⟨ready,workers⟩ := held
    obtain ⟨issued,rest,worker,previous,queueEq,completedEq,paired,identity,finished⟩ := completed_workers_last workers nonempty
    let completed := alloc.vec.Vec.from previous (by have bound := before.completed.property; rw [completedEq] at bound; simp only [List.length_append,List.length_singleton] at bound; omega)
    let after := {before with completed := completed}
    have polled : runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch ops before = .ok (.Ok worker,after) := by
      simp [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.poll_code_batch,
        alloc.vec.Vec.pop,completedEq,core.option.Option.ok_or,after,completed]
    refine ⟨issued,rest,worker,after,?_,polled,identity,finished,?_,?_⟩
    · rw [queueEq]
      exact (List.perm_append_singleton _ _).symm
    · exact ⟨ready.signatures,ready.functionSlots,ready.origin,ready.slots,ready.paid⟩
    · simpa only [after,completed,alloc.vec.Vec.from_val] using paired

end Itasca.Runtime.Compiler

end

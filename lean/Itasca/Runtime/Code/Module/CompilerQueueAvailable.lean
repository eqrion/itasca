import Itasca.Runtime.Code.Module.SourceQueuePolicy
import Itasca.Runtime.Code.Module.PreparedBatchEncoding
import Itasca.Runtime.Code.Module.SubmitAvailable
import Itasca.Runtime.Code.Module.CompletedWorkerQueue
import Itasca.Runtime.Code.Module.SchedulerSubmission

namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code

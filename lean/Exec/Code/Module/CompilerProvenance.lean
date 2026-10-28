import Exec.Code.Module.EnvironmentFrame
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
open Itasca

/-- Every completed worker comes from one issued batch in a history with unique
batch identifiers. The history is an internal invariant of the actual driver. -/
structure SchedulerTracks {A : Type} (_id : U64) (history : List StreamBatch.Issued)
    (scheduler : runtime.compiler.CompileScheduler A) : Prop where
  unique : ∀ left ∈ history, ∀ right ∈ history, left.batch_id = right.batch_id → left = right
  workers : ∀ batch ∈ scheduler.completed.val, ∃ issued ∈ history, StreamBatch.Reachable issued batch

theorem SchedulerTracks.queue {A : Type} {id history} {before after : runtime.compiler.CompileScheduler A}
    (tracked : SchedulerTracks id history before) (same : after.completed = before.completed) :
    SchedulerTracks id history after := by
  exact ⟨tracked.unique, by simpa only [same] using tracked.workers⟩

/-- The concrete compiler satisfies the canonical streaming scheduler's
provenance contract. Allocation decisions remain unrestricted. -/
theorem compiler_provenance {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (profile : ValidationProfile) :
    StreamScheduler.Provenance
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
      SchedulerTracks profile := by
  constructor
  · intro id history before chunk after accepted tracked
    have same : before = after := by
      simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor,
        runtime.compiler.CompileScheduler.Insts.ItascaModuleModuleVisitor,
        runtime.compiler.CompileScheduler.Insts.ItascaModuleModuleVisitor.on_custom_section,
        Result.ok.injEq, Prod.mk.injEq, true_and] using accepted
    subst after
    exact tracked
  · intro id history before region after tracked accepted
    have same : before = after := Result.ok_injective accepted
    subst after
    exact tracked
  · intro id history before env config after tracked accepted
    exact tracked.queue (congrArg Prod.fst (compiler_environment_frame allocator before after env config accepted))
  · intro id history issued before after tracked moduleId bounded envBounds selected fresh accepted
    obtain ⟨middle, worker, run, queue, _⟩ := compiler_submit_accepted allocator law before after issued.seed accepted
    constructor
    · intro left hl right hr equal
      rcases List.mem_append.mp hl with hl | hl <;> rcases List.mem_append.mp hr with hr | hr
      · exact tracked.unique left hl right hr equal
      · have rightEq := List.mem_singleton.mp hr
        subst right
        exact (fresh left hl equal).elim
      · have leftEq := List.mem_singleton.mp hl
        subst left
        exact (fresh right hr equal.symm).elim
      · exact (List.mem_singleton.mp hl).trans (List.mem_singleton.mp hr).symm
    · intro batch member
      rw [queue] at member
      rcases List.mem_append.mp member with old | new
      · obtain ⟨origin, member, reachable⟩ := tracked.workers batch old
        exact ⟨origin, List.mem_append_left _ member, reachable⟩
      · have same := List.mem_singleton.mp new
        subst batch
        exact ⟨issued, by simp, run.reachable .seed⟩
  · intro id history before batch after tracked accepted
    obtain ⟨queue, same⟩ := compiler_poll_accepted allocator before after batch accepted
    constructor
    · refine ⟨tracked.unique, ?_⟩
      intro worker member
      exact tracked.workers worker (by rw [queue]; exact List.mem_append_left _ member)
    · intro issued member moduleId batchId
      obtain ⟨origin, originMember, reachable⟩ := tracked.workers batch (by rw [queue]; simp)
      have identity := reachable.validation.1
      have sameOrigin := tracked.unique origin originMember issued member (identity.2.1.symm.trans batchId.symm)
      subst origin
      exact reachable
  · intro id history before after tracked accepted
    have same : before = after := by
      simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor,
        runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.code_end,
        Result.ok.injEq, Prod.mk.injEq, true_and] using accepted
    subst after
    exact tracked
  · intro id history before tail after tracked accepted
    have same : {before with tail := some tail} = after := by
      simpa only [runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor,
        runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready,
        Result.ok.injEq, Prod.mk.injEq, true_and] using accepted
    subst after
    exact tracked.queue rfl
end Itasca.Runtime.Code

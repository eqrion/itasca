import Exec.Code.Module.SchedulerSubmissionSafety
import Exec.Code.Module.Stream
import Itasca.Stream.InvariantDriver

namespace Exec.Code
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- The remaining internal entry obligation. Each input worker comes from
actual issued-batch operations and each compiler scheduler retains its captured
metadata. This contract will be discharged by the reached body callback proof. -/
def ReachedEntriesTotal {A : Type} (ops : runtime.platform.Alloc A)
    (profile : ValidationProfile) : Prop :=
  ∀ (env : module.Env) (issued : StreamBatch.Issued) (scheduler : CompileScheduler A)
    (worker : stream.CodeBatch), issued.env = env → issued.Bounded → CodeEntry.Bounds env →
    issued.profile = profile → SchedulerReady env issued.first_func.val scheduler →
    StreamBatch.Reachable issued worker → CompileScheduler.compile_entry ops scheduler worker ⦃ _ => True ⦄

theorem compiler_scheduler_callbacks_on {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (profile : ValidationProfile)
    (entries : ReachedEntriesTotal ops profile) :
    StreamScheduler.CallbacksOn (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      SchedulerInitial SchedulerReady (fun _ => True) profile := by
  constructor
  · intro scheduler chunk
    exact ⟨(.Ok (),scheduler),rfl⟩
  · intro before chunk after accepted held
    have same : before = after := by simpa [CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      CompileScheduler.Insts.ItascaModuleModuleVisitor,
      CompileScheduler.Insts.ItascaModuleModuleVisitor.on_custom_section] using accepted
    simpa only [same] using held
  · intro env cursor before chunk after accepted held
    have same : before = after := by simpa [CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      CompileScheduler.Insts.ItascaModuleModuleVisitor,
      CompileScheduler.Insts.ItascaModuleModuleVisitor.on_custom_section] using accepted
    simpa only [same] using held
  · intro scheduler region held
    simpa [CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      CompileScheduler.Insts.ItascaStreamStreamingVisitor.custom_region] using held
  · intro env cursor scheduler region held
    simpa [CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      CompileScheduler.Insts.ItascaStreamStreamingVisitor.custom_region] using held
  · intro scheduler env held _ _
    exact compiler_environment_safety ops law scheduler env held
  · intro env
    constructor
    · intro scheduler issued held sameEnv bounded bounds selected
      exact compiler_submit_safety ops law env issued sameEnv bounded scheduler held
        (fun current worker ready reached => entries env issued current worker sameEnv bounded
          (by simpa only [sameEnv] using bounds) selected ready reached)
    · intro cursor scheduler held
      exact compiler_poll_safety ops env cursor scheduler held
  · intro env scheduler held
    simpa [CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      CompileScheduler.Insts.ItascaStreamStreamingVisitor.code_end] using held
  · intro env scheduler tail held
    simp only [CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready,WP.spec_ok]
    intro _
    exact ⟨held.signatures,held.functionSlots,held.functions,held.origin,held.queue,held.cursorBound⟩

/-- Successful streaming retains the final scheduler ledger needed by function
collection and initializer headroom. Rejected streams need no post-state ledger. -/
theorem compiler_stream_spec_of_entries {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (profile : ValidationProfile)
    (entries : ReachedEntriesTotal ops profile) (source : CompileSource)
    (sourceBounds : SourceBounds source) (scheduler : CompileScheduler A)
    (initial : SchedulerInitial scheduler) (storage : module.Env) :
    stream.validate_streaming CompileSource.Insts.ItascaStreamSource
      (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64 profile source scheduler storage ⦃ out =>
        out.1 = .Ok () → SchedulerReady out.2.2 out.2.2.func_type_indices.val.length out.2.1 ⦄ := by
  exact stream.validate_streaming.profile_spec_on CompileSource.Insts.ItascaStreamSource
    (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64 source scheduler storage
    (source_callbacks_total source sourceBounds) SchedulerInitial SchedulerReady (fun _ => True)
    (compiler_scheduler_callbacks_on ops law profile entries) initial (by intros; trivial)

/-- All streaming phases of actual eager compilation return once the remaining
reached entry proof is supplied. No arbitrary-state callback totality is assumed. -/
theorem compiler_stream_total_of_entries {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (profile : ValidationProfile)
    (entries : ReachedEntriesTotal ops profile) (source : CompileSource)
    (sourceBounds : SourceBounds source) (scheduler : CompileScheduler A)
    (initial : SchedulerInitial scheduler) (storage : module.Env) :
    ∃ out, stream.validate_streaming CompileSource.Insts.ItascaStreamSource
      (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64 profile source scheduler storage = .ok out := by
  exact stream.validate_streaming.profile_total_on CompileSource.Insts.ItascaStreamSource
    (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64 source scheduler storage
    (source_callbacks_total source sourceBounds) SchedulerInitial SchedulerReady (fun _ => True)
    (compiler_scheduler_callbacks_on ops law profile entries) initial (by intros; trivial)

end Exec.Code

import Exec.Code.Module.SchedulerDriverSafety
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
open runtime.compiler

/-- Signature restrictions retained from actual profile environment decoding. -/
def ProfileEnvironment (profile : ValidationProfile) (env : module.Env) : Prop :=
  Profile.Environment profile env ∧ Profile.EnvironmentWithinLimits profile env

def ReachedProfileEntriesTotal {A : Type} (ops : runtime.platform.Alloc A)
    (profile : ValidationProfile) : Prop :=
  ∀ (env : module.Env) (issued : StreamBatch.Issued) (scheduler : CompileScheduler A)
    (worker : stream.CodeBatch), issued.env = env → issued.Bounded → CodeEntry.Bounds env →
    issued.profile = profile → ProfileEnvironment profile env →
    SchedulerReady env issued.first_func.val scheduler →
    StreamBatch.Reachable issued worker → CompileScheduler.compile_entry ops scheduler worker ⦃ _ => True ⦄

theorem compiler_scheduler_profile_callbacks_on {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (profile : ValidationProfile)
    (entries : ReachedProfileEntriesTotal ops profile) :
    StreamScheduler.CallbacksOn (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops)
      SchedulerInitial (fun env cursor scheduler => SchedulerReady env cursor scheduler ∧ ProfileEnvironment profile env)
      (ProfileEnvironment profile) profile := by
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
  · intro scheduler env held admitted bounds
    apply WP.spec_mono (compiler_environment_safety ops law scheduler env held)
    intro out fresh config accepted
    exact ⟨fresh config accepted,admitted⟩
  · intro env
    constructor
    · intro scheduler issued held sameEnv bounded bounds selected
      apply WP.spec_mono (compiler_submit_safety ops law env issued sameEnv bounded scheduler held.1
        (fun current worker ready reached => entries env issued current worker sameEnv bounded
          (by simpa only [sameEnv] using bounds) selected held.2 ready reached))
      intro out fresh accepted
      exact ⟨fresh accepted,held.2⟩
    · intro cursor scheduler held
      apply WP.spec_mono (compiler_poll_safety ops env cursor scheduler held.1)
      intro out fresh batch accepted
      exact ⟨fresh batch accepted,held.2⟩
  · intro env scheduler held
    simpa [CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      CompileScheduler.Insts.ItascaStreamStreamingVisitor.code_end] using held
  · intro env scheduler tail held
    simp only [CompileScheduler.Insts.ItascaStreamStreamingVisitor,
      CompileScheduler.Insts.ItascaStreamStreamingVisitor.tail_ready,WP.spec_ok]
    intro _
    exact ⟨⟨held.1.signatures,held.1.functionSlots,held.1.functions,held.1.origin,held.1.queue,held.1.cursorBound⟩,held.2⟩

/-- Actual environment decoding supplies the profile restriction before any
worker is issued. It is retained through every reached scheduler state. -/
theorem compiler_stream_spec_of_profile_entries {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (profile : ValidationProfile)
    (entries : ReachedProfileEntriesTotal ops profile) (source : CompileSource)
    (sourceBounds : SourceBounds source) (scheduler : CompileScheduler A)
    (initial : SchedulerInitial scheduler) (storage : module.Env) :
    stream.validate_streaming CompileSource.Insts.ItascaStreamSource
      (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64 profile source scheduler storage ⦃ out =>
        out.1 = .Ok () → SchedulerReady out.2.2 out.2.2.func_type_indices.val.length out.2.1 ⦄ := by
  apply WP.spec_mono (stream.validate_streaming.profile_spec_on CompileSource.Insts.ItascaStreamSource
    (CompileScheduler.Insts.ItascaStreamStreamingVisitor ops) 0#u64 source scheduler storage
    (source_callbacks_total source sourceBounds) SchedulerInitial
    (fun env cursor scheduler => SchedulerReady env cursor scheduler ∧ ProfileEnvironment profile env)
    (ProfileEnvironment profile) (compiler_scheduler_profile_callbacks_on ops law profile entries) initial
    (by intro bytes env next bounded accepted
        exact (ModuleEnv.profile_accepted_entry_conditions bytes env next profile bounded accepted).2))
  intro out fresh accepted
  exact (fresh accepted).1
end Exec.Code

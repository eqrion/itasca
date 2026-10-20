import Exec.Interp.Host.OpenCallFootprint
import Exec.Interp.Host.OpenExecutionLoop
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std

def PendingStore {M P : Type} (before : runtime.store.Store M) : CallPhase M P → Prop
  | .done _ => True
  | .pending _ store _ _ _ _ _ _ => store=before

theorem PhaseStore.pending {M P : Type} {before : runtime.store.Store M} {phase : CallPhase M P}
    (held : PhaseStore before phase) : PendingStore before phase := by
  cases phase with
  | done => trivial
  | pending => exact held

theorem completed_pending_store {M P : Type} (before : runtime.store.Store M)
    (run : Result (Answer M P)) (phase : CallPhase M P) (actual : completed run=.ok phase) :
    PendingStore before phase := by
  unfold completed at actual
  obtain ⟨answer,called,tail⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
  simp only [Result.ok.injEq] at tail
  cases tail
  trivial

/-- Suspending an instruction cannot hide a committed store mutation. Native
noncall instructions finish normally before their store effects are observed. -/
theorem prepareDispatch_pending_store {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (frameIndex inst function base : Usize)
    (instruction : runtime.bytecode.Instr) (phase : CallPhase M P)
    (actual : prepareDispatch memory hooks floats allocator exec store platform frameIndex inst function base instruction=.ok phase) :
    PendingStore store phase := by
  cases instruction
  case Call func callee =>
    exact (prepareDirect_store memory hooks floats allocator exec store platform inst base func callee phase actual).pending
  case CallIndirect entry index callee =>
    exact (prepareIndirect_store memory hooks floats allocator exec store platform inst function base entry index callee phase actual).pending
  all_goals exact completed_pending_store store _ phase actual

theorem prepareStep_pending_store {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (phase : CallPhase M P)
    (actual : prepareStep memory hooks floats allocator exec store platform=.ok phase) :
    PendingStore store phase := by
  unfold prepareStep at actual
  repeat' first
    | (simp only [Std.bind_assoc,bind_ok,lift] at actual)
    | exact prepareDispatch_pending_store memory hooks floats allocator _ store platform _ _ _ _ _ phase actual
    | (split at actual)
    | (obtain ⟨value,called,actual⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
       cases value
       try simp only [Std.uncurry] at actual)
    | (simp only [Result.ok.injEq] at actual
       cases actual
       trivial)

end Exec.Interp.OpenCall

import Exec.Interp.Host.OpenAdminCall
import Itasca.Support.Result
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std

def PhaseStore {M P : Type} (before : runtime.store.Store M) : CallPhase M P → Prop
  | .done answer => answer.2.2.1=before
  | .pending _ store _ _ _ _ _ _ => store=before

/-- Native call preparation changes only execution scratch and frame state;
every returned or suspended phase retains the original concrete store. -/
theorem prepareCall_store {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (address : runtime.FuncAddr) (base : Usize)
    (phase : CallPhase M P)
    (actual : prepareCall memory hooks floats allocator exec store platform address base=.ok phase) :
    PhaseStore store phase := by
  unfold prepareCall at actual
  repeat' first
    | (simp only [Std.bind_assoc,bind_ok,lift] at actual)
    | (split at actual)
    | (obtain ⟨value,called,actual⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
       cases value
       try simp only [Std.uncurry] at actual)
    | (simp only [Result.ok.injEq] at actual
       cases actual
       exact rfl)

theorem prepareDirect_store {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (inst base : Usize) (func callee : U32)
    (phase : CallPhase M P)
    (actual : prepareDirect memory hooks floats allocator exec store platform inst base func callee=.ok phase) :
    PhaseStore store phase := by
  unfold prepareDirect at actual
  repeat' first
    | (simp only [Std.bind_assoc,bind_ok,lift] at actual)
    | exact prepareCall_store memory hooks floats allocator _ store platform _ _ phase actual
    | (split at actual)
    | (obtain ⟨value,called,actual⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
       cases value
       try simp only [Std.uncurry] at actual)

theorem prepareIndirect_store {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (inst function base : Usize) (entry index callee : U32)
    (phase : CallPhase M P)
    (actual : prepareIndirect memory hooks floats allocator exec store platform inst function base entry index callee=.ok phase) :
    PhaseStore store phase := by
  unfold prepareIndirect at actual
  repeat' first
    | (simp only [Std.bind_assoc,bind_ok,lift] at actual)
    | exact prepareCall_store memory hooks floats allocator _ store platform _ _ phase actual
    | (split at actual)
    | (obtain ⟨value,called,actual⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
       cases value
       try simp only [Std.uncurry] at actual)
    | (simp only [Result.ok.injEq] at actual
       cases actual
       exact rfl)
end Exec.Interp.OpenCall

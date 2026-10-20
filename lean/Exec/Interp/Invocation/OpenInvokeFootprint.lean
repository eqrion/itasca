import Exec.Interp.Host.OpenStepFootprint
import Exec.Interp.Invocation.OpenInvoke
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std
def InvokeStore {M P : Type} (before : runtime.store.Store M) : InvokePhase M P → Prop
  | .done answer => answer.2.2.1=before
  | .waiting phase _ _ => PhaseStore before phase

/-- Invocation setup rejects without store effects or prepares a first call
whose entry store is exactly the original store. -/
theorem prepareInvoke_store {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (address : runtime.FuncAddr)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value) (phase : InvokePhase M P)
    (actual : prepareInvoke memory hooks floats allocator exec store platform address args results=.ok phase) :
    InvokeStore store phase := by
  unfold prepareInvoke at actual
  repeat' first
    | (simp only [Std.bind_assoc,bind_ok,lift] at actual)
    | (split at actual)
    | (obtain ⟨value,called,actual⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
       cases value
       try simp only [Std.uncurry] at actual)
    | (simp only [Result.ok.injEq] at actual
       cases actual
       first | exact rfl | exact prepareCall_store memory hooks floats allocator _ store platform _ _ _ called)
end Exec.Interp.OpenCall

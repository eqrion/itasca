import Exec.Interp.Host.HostResume
import Itasca.Support.Result
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Checked resumption cannot create a host-stack error when the concrete
control implementation did not report host-stack overflow. -/
theorem hostResume_status {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (address : runtime.FuncAddr) (base : Usize)
    (values : alloc.vec.Vec runtime.Value) (status : core.result.Result Unit runtime.platform.HostError)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution)
    (actual : hostResume memory exec store address base values status=.ok out)
    (noOverflow : status≠.Err .StackOverflow) : out.1=.Ok () ∨ out.1=.Err (.Trap .Host) := by
  cases status with
  | Err error=>
    cases error with
    | StackOverflow=>exact False.elim (noOverflow rfl)
    | Trap=>simp only [hostResume,Result.ok.injEq] at actual;subst out;exact Or.inr rfl
  | Ok unit=>
    cases unit
    unfold hostResume at actual
    repeat' first
      | (simp only [bind_tc_eq,Std.bind_assoc,bind_ok] at actual)
      | (split at actual)
      | (obtain ⟨value,called,actual⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
         cases value
         try simp only [Std.uncurry] at actual)
      | (simp only [Result.ok.injEq] at actual
         cases actual
         first | exact Or.inl rfl | exact Or.inr rfl)
end Exec.Interp

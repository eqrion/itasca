import Exec.Generated.Equations
import Exec.Store.Invariant.NormalResult

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Every normal result of the remaining initializer/start computation carries
the committed flag, independently of start-function termination or outcome. -/
theorem instantiate_tail_committed {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (identity : runtime.InstanceAddr) (store : runtime.store.Store M) (platform : P)
    (result : core.result.Result runtime.InstanceAddr runtime.ExecError)
    (after : runtime.store.Store M) (host : P) (committed : Bool)
    (run : runtime.store.instantiate.Store.commit_instance memory hooks floats allocator store platform identity false =
      .ok (result, after, host, committed)) : committed = true := by
  unfold runtime.store.instantiate.Store.commit_instance at run
  obtain ⟨⟨status, state, context⟩, initRun, run⟩ := normal_bind_exists _ _ _ run
  simp only [uncurry_apply_pair] at run
  cases status with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok] at run
    exact (congrArg (fun out => out.2.2.2) (Result.ok_injective run)).symm
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at run
    obtain ⟨inst, instRun, run⟩ := normal_bind_exists _ _ _ run
    simp only [runtime.compiler.ExecutableModule.env, Exec.module.Module.env,
      Itasca.module.Module.impl.env, Exec.module.Env.start, Itasca.module.Env.impl.start, bind_ok] at run
    split at run
    · exact (congrArg (fun out => out.2.2.2) (Result.ok_injective run)).symm
    · obtain ⟨index, indexRun, run⟩ := normal_bind_exists _ _ _ run
      obtain ⟨address, addressRun, run⟩ := normal_bind_exists _ _ _ run
      obtain ⟨execution, executionRun, run⟩ := normal_bind_exists _ _ _ run
      obtain ⟨arguments, argumentRun, run⟩ := normal_bind_exists _ _ _ run
      obtain ⟨⟨status, execution, finalStore, finalHost, values⟩, invokeRun, run⟩ := normal_bind_exists _ _ _ run
      simp only [uncurry_apply_pair] at run
      cases status <;> simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok] at run <;>
        exact (congrArg (fun out => out.2.2.2) (Result.ok_injective run)).symm

end Exec.Store

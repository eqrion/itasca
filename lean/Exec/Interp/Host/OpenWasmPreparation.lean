import Exec.Interp.Host.OpenCallFootprint
import Exec.Interp.Host.OpenStep
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std

/-- A known Wasm entry cannot suspend in a host callback. Resumable call
preparation is exactly the ordinary native call with its result tagged done. -/
theorem prepareCall_wasm {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (address : runtime.FuncAddr) (base : Usize)
    (function : runtime.store.Function) (instanceIndex functionIndex : Usize)
    (found : store.funcs.val[address.index.val]?=some function)
    (wasm : function.code=.Wasm instanceIndex functionIndex)
    (interrupts : hooks.interrupt platform ⦃ _=>True ⦄) :
    prepareCall memory hooks floats allocator exec store platform address base=
      completed (runtime.interp.call memory hooks floats allocator exec store platform address base) := by
  obtain ⟨⟨decision,nextPlatform⟩,decisionEq,_⟩ := WP.spec_imp_exists interrupts
  have functionEq : alloc.vec.Vec.index_usize store.funcs address.index=.ok function := by
    obtain ⟨value,actual,same⟩ := WP.spec_imp_exists (vec_index_given store.funcs address.index function found)
    simpa only [same] using actual
  unfold prepareCall completed runtime.interp.call
  rw [interrupt_eq memory hooks platform nextPlatform decision decisionEq]
  simp only [Std.bind_assoc]
  cases decision with
  | Terminate =>
    simp [interruptResult,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,bind_ok]
  | Continue =>
    simp only [interruptResult,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,
      alloc.vec.Vec.index_slice_index,functionEq,wasm,Std.bind_assoc]
    repeat' first | rfl |
      (simp only [Std.uncurry,Std.bind_assoc,bind_ok,lift,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,core.convert.FromSame.from]) |
      (congr 1; funext x) |
      (cases x <;> simp_all only [Std.uncurry,Std.bind_assoc,bind_ok,lift]) |
      (split <;> simp_all only [Std.bind_assoc,bind_ok,lift])
end Exec.Interp.OpenCall

import Exec.Interp.Invocation.InvokeChecks
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Lift an accepted-argument contract through the actual public checker.
Rejection retains the exact unchanged execution, store, platform, and results. -/
theorem invoke_with_checked_outcome {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (args : Slice runtime.Value)
    (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (property : (core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P × alloc.vec.Vec runtime.Value) → Prop)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()) →
      runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results ⦃ out => property out ⦄div) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out =>
        (∃ error, runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Err error) ∧
          out = (.Err error,exec,store,platform,results)) ∨
        (runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()) ∧ property out) ⦄div := by
  obtain ⟨answer,checked,decision⟩ := WP.spec_imp_exists
    (check_values_effect memory store args (alloc.vec.Vec.deref signature.params))
  cases answer with
  | Ok unit =>
    cases unit
    apply WP.dspec_mono (accepted checked)
    intro out post
    exact Or.inr ⟨checked,post⟩
  | Err error =>
    obtain ⟨found,lookup,same⟩ := WP.spec_imp_exists
      (func_type_lookup memory store address function signature owner hf hs)
    subst found
    have returned : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results =
        .ok (.Err error,exec,store,platform,results) := by
      simp [runtime.interp.invoke_with,lookup,checked,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    rw [returned]
    apply WP.dspec.ret
    exact Or.inl ⟨error,checked,rfl⟩
end Exec.Interp

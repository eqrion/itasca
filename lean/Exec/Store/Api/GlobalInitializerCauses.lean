import Exec.Store.Api.GlobalAllocationCauses
import Exec.Store.Api.GlobalErrors
import Exec.Store.Initialization.InitializerResourceCauses
import Exec.Code.Local.Initializer.InitializerMappings
namespace Exec.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem add_global_resource_cause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.Instance) (global : Itasca.module.Global)
    (function : Usize) (code : runtime.bytecode.CompiledFunction) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hg : inst.module.module.env.globals.val[index.val]? = some global)
    (hmapping : inst.module.global_initializers.val[index.val]? = some function)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Code.InitializerCode code global.init global.gtype.valtype)
    (resolved : Interp.InitializerResolution store inst global.init global.gtype.valtype words)
    (bindings : InitializerBindings store inst)
    (bound : objectCount store ≤ Usize.max)
    (error : runtime.ExecError) (after : runtime.store.Store M) (host : P)
    (run : runtime.store.instantiate.Store.add_instance_global memory hooks floats allocator store platform instIndex index = .ok (.Err error,after,host)) :
    after = store ∧ host = platform ∧
      (Interp.SyntheticPreparationCause allocator store code error ∨ GlobalAllocationCause allocator store error) := by
  obtain ⟨evaluated, evalRun, sameStore, sameHost, success⟩ := WP.spec_imp_exists
    (eval_const_exec_owned memory hooks floats allocator law store platform instIndex function
      inst code global.init global.gtype.valtype words hi hc compiled resolved bindings)
  rcases evaluated with ⟨value, after, host⟩
  dsimp only at sameStore sameHost success evalRun
  subst after host
  have errors := eval_const_exec_resource_causes memory hooks floats allocator law store platform instIndex function
    inst code global.init global.gtype.valtype words hi hc compiled resolved
    (initializer_reference_bound resolved bindings)
  rw [evalRun] at errors
  simp only [WP.spec_ok] at errors
  unfold runtime.store.instantiate.Store.add_instance_global at run
  simp only [Code.initializer_vec_index store.instances instIndex inst hi,
    runtime.compiler.ExecutableModule.env, module.Module.env, Itasca.module.Module.impl.env,
    module.Env.globals, Itasca.module.Env.impl.globals, bind_ok] at run
  rw [Code.initializer_slice_index inst.module.module.env.globals.deref index global (by simpa [alloc.vec.Vec.deref] using hg)] at run
  simp only [bind_ok,
    Code.initializer_vec_index inst.module.global_initializers index function hmapping,
    evalRun] at run
  cases value with
  | Err rejected =>
    have cause := errors.2.2.2 rejected rfl
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
    exact ⟨rfl,rfl,Or.inl cause⟩
  | Ok value =>
    obtain ⟨owned,typed⟩ := success value rfl
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
    obtain ⟨⟨status,changed⟩,defined,run⟩ := normal_bind_exists _ _ _ run
    have cause := define_global_resource_causes memory allocator law store global.gtype value bound typed.symm owned
    rw [defined,WP.spec_ok] at cause
    cases status with
    | Err rejected =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
      obtain ⟨rfl,rfl,rfl⟩ := run
      obtain ⟨same,cause⟩ := cause rejected rfl
      exact ⟨same,rfl,Or.inr cause⟩
    | Ok address =>
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
      obtain ⟨⟨current,back⟩,read,run⟩ := normal_bind_exists _ _ _ run
      simp only [uncurry_apply_pair] at run
      obtain ⟨addresses,pushed,run⟩ := normal_bind_exists _ _ _ run
      simp at run
end Exec.Store

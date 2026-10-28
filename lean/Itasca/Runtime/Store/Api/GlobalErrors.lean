import Itasca.Runtime.Store.Invariant.DefinitionErrors
import Itasca.Runtime.Store.Initialization.InitializerErrors
import Itasca.Runtime.Code.Local.Initializer.InitializerMappings
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem add_global_errors {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (global : Itasca.module.Global)
    (function : Usize) (code : runtime.bytecode.CompiledFunction) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hg : inst.module.module.env.globals.val[index.val]? = some global)
    (hmapping : inst.module.global_initializers.val[index.val]? = some function)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Code.InitializerCode code global.init global.gtype.valtype)
    (resolved : Interp.InitializerResolution store inst global.init global.gtype.valtype words)
    (bindings : InitializerBindings store inst)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × P)
    (run : runtime.store.instantiate.Store.add_instance_global memory hooks floats allocator store platform instIndex index = .ok out) :
    ErrorAllowed ResourceError out.1 := by
  obtain ⟨evaluated, evalRun, sameStore, sameHost, success⟩ := WP.spec_imp_exists
    (eval_const_owned memory hooks floats allocator law store platform instIndex function
      inst code global.init global.gtype.valtype words hi hc compiled resolved bindings)
  rcases evaluated with ⟨value, after, host⟩
  dsimp only at sameStore sameHost success evalRun
  subst after host
  have errors := eval_const_errors memory hooks floats allocator law store platform instIndex function
    inst code global.init global.gtype.valtype words hi hc compiled resolved
    (initializer_reference_bound resolved bindings)
  rw [evalRun] at errors
  simp only [WP.spec_ok] at errors
  unfold runtime.store.instantiate.Store.add_instance_global at run
  simp only [Code.initializer_vec_index store.instances instIndex inst hi,
    runtime.compiler.ExecutableModule.env, Itasca.module.Module.impl.env, Itasca.module.Env.impl.globals, bind_ok] at run
  rw [Code.initializer_slice_index inst.module.module.env.globals.deref index global (by simpa [alloc.vec.Vec.deref] using hg)] at run
  simp only [bind_ok,
    Code.initializer_vec_index inst.module.global_initializers index function hmapping,
    evalRun] at run
  cases value with
  | Err error =>
    obtain ⟨resource, rfl⟩ := errors.2.2.2 error rfl
    repeat' allocation_error_step run using allocator, law
  | Ok value =>
    obtain ⟨owned, typed⟩ := success value rfl
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at run
    obtain ⟨⟨status, after⟩, defined, rest⟩ := normal_bind_exists _ _ _ run
    have cause := define_global_errors memory allocator law store global.gtype value typed.symm owned.1 _ defined
    clear run
    rename' rest => run
    repeat' allocation_error_step run using allocator, law

end Itasca.Runtime.Store

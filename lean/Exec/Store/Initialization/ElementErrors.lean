import Exec.Store.Initialization.ElementValueErrors
import Exec.Store.Preparation.AllocationErrors
import Exec.Code.Local.Initializer.InitializerMappings
namespace Exec.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 8192

theorem add_element_errors {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.Instance) (segment : Itasca.module.Element)
    (found : store.instances.val[instIndex.val]? = some inst)
    (element : inst.module.module.env.elements.val[index.val]? = some segment)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × P)
    (run : runtime.store.instantiate.Store.add_instance_element memory hooks floats allocator store platform instIndex index = .ok out) :
    ErrorAllowed ResourceError out.1 := by
  unfold runtime.store.instantiate.Store.add_instance_element at run
  simp only [Code.initializer_vec_index store.instances instIndex inst found,
    runtime.compiler.ExecutableModule.env, module.Module.env, Itasca.module.Module.impl.env,
    module.Env.elements, Itasca.module.Env.impl.elements, bind_ok] at run
  rw [Code.initializer_slice_index inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using element)] at run
  obtain ⟨reserved, reserveRun⟩ := reserve_wrapper_eq allocator law (alloc.vec.Vec.new U64) segment.init.len
  simp only [bind_ok, reserveRun] at run
  cases reserved with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at run
    repeat' allocation_error_step run using allocator, law
  | true =>
    simp only [↓reduceIte, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at run
    obtain ⟨⟨after, host, values, status⟩, loopRun, sameStore, sameHost, bound, errors⟩ := WP.spec_imp_exists
      (element_initializers_loop_errors memory hooks floats allocator law store platform instIndex index
        segment.init.len inst segment found element (by simp) certificates bindings
        (alloc.vec.Vec.new U64) 0#usize (.Ok ()) True.intro (by simp) (by scalar_tac))
    rw [loopRun] at run
    repeat' allocation_error_step run using allocator, law

end Exec.Store

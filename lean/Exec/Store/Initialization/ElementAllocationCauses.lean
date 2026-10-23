import Exec.Store.Initialization.ElementValueCauses
import Exec.Store.Preparation.AllocationCauses
import Exec.Store.Preparation.AllocationErrors
import Exec.Code.Local.Initializer.InitializerMappings
namespace Exec.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 8192

/-- Segment storage refusals retain their exact source-sized initial request,
final store-vector request, or source initializer witness. -/
def ElementAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (segment : Itasca.module.Element) (error : runtime.ExecError) : Prop :=
  (error = .Exhausted .Allocation ∧
    (allocator.reserve (alloc.vec.Vec.new U64) segment.init.len = .ok (false,alloc.vec.Vec.new U64) ∨
      allocator.reserve store.elems 1#usize = .ok (false,store.elems))) ∨
  ElementInitializerCause allocator store inst index segment error

theorem add_element_resource_cause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.module.Element)
    (found : store.instances.val[instIndex.val]? = some inst)
    (element : inst.module.module.env.elements.val[index.val]? = some segment)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (error : runtime.ExecError) (after : runtime.store.Store M) (host : P)
    (run : runtime.store.instantiate.Store.add_instance_element memory hooks floats allocator store platform instIndex index = .ok (.Err error,after,host)) :
    after = store ∧ host = platform ∧ ElementAllocationCause allocator store inst index segment error := by
  unfold runtime.store.instantiate.Store.add_instance_element at run
  simp only [Code.initializer_vec_index store.instances instIndex inst found,
    runtime.compiler.ExecutableModule.env, module.Module.env, Itasca.module.Module.impl.env,
    module.Env.elements, Itasca.module.Env.impl.elements, bind_ok] at run
  rw [Code.initializer_slice_index inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using element)] at run
  obtain ⟨reserved, reserveRun,refusal⟩ := reserve_with_cause allocator law (alloc.vec.Vec.new U64) segment.init.len
  simp only [bind_ok, reserveRun] at run
  cases reserved with
  | false =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
    exact ⟨rfl,rfl,Or.inl ⟨rfl,Or.inl refusal⟩⟩
  | true =>
    simp only [↓reduceIte,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
    obtain ⟨⟨evaluated,finalHost,values,status⟩,loopRun,sameStore,sameHost,bound,errors⟩ := WP.spec_imp_exists
      (element_initializers_loop_causes memory hooks floats allocator law store platform instIndex index
        segment.init.len inst segment found element (by simp) certificates bindings
        (alloc.vec.Vec.new U64) 0#usize (.Ok ()) True.intro (by simp) (by scalar_tac))
    dsimp only at sameStore sameHost bound errors
    subst evaluated finalHost
    rw [loopRun] at run
    simp only [bind_ok,uncurry_apply_pair] at run
    cases status with
    | Err rejected =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
      obtain ⟨rfl,rfl,rfl⟩ := run
      exact ⟨rfl,rfl,Or.inr errors⟩
    | Ok done =>
      cases done
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
      obtain ⟨answer,reserved,refused⟩ := reserve_with_cause allocator law store.elems 1#usize
      rw [reserved] at run
      cases answer
      · simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
        obtain ⟨rfl,rfl,rfl⟩ := run
        exact ⟨rfl,rfl,Or.inl ⟨rfl,Or.inr refused⟩⟩
      · simp [core.result.Result.Insts.CoreOpsTry.branch,
          runtime.compiler.ExecutableModule.env,module.Module.env,Itasca.module.Module.impl.env,
          module.Env.elements,Itasca.module.Env.impl.elements] at run
        obtain ⟨current,read,run⟩ := normal_bind_exists _ _ _ run
        obtain ⟨declared,read,run⟩ := normal_bind_exists _ _ _ run
        obtain ⟨elements,pushed,run⟩ := normal_bind_exists _ _ _ run
        obtain ⟨⟨current,back⟩,read,run⟩ := normal_bind_exists _ _ _ run
        simp only [uncurry_apply_pair] at run
        obtain ⟨addresses,mapped,run⟩ := normal_bind_exists _ _ _ run
        simp at run
end Exec.Store

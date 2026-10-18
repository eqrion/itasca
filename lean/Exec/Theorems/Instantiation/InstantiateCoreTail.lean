import Exec.Theorems.Composition.Certified.CertifiedCoreSegments
import Exec.Store.Instantiation.InstantiateNoStart
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Store
/-- Without a start function, the committed instantiation tail always returns
normally, preserves the Store invariant, and leaves the platform unchanged.
Segment bounds failures remain ordinary Wasm traps. -/
theorem instantiate_tail_core_no_start {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (identity : runtime.InstanceAddr)
    (inst : runtime.store.Instance) (bytes : Slice U8) (profile : Itasca.ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module))
    (found : store.instances.val[identity.index.val]? = some inst)
    (code : CodeInterpretation) (certified : CertifiedCoreStore view code store)
    (imports : InitializerImports store inst)
    (types : SegmentTypeBindings store inst) (noStart : inst.module.module.env.start = none) :
    instantiate_tail memory hooks floats allocator identity store platform
      ⦃ out => CertifiedCoreStore view code out.2.1 ∧ SegmentObjectMetadata view store out.2.1 ∧
        out.2.2.1 = platform ∧ out.2.2.2 = true ∧
        (∀ address, out.1 = .Ok address → address = identity) ⦄ := by
  have bindings := certified.shape.initializer_bindings (List.mem_of_getElem? found)
  have initialized := initialize_segments_certified_core memory hooks floats allocator view laws law
    store platform identity.index inst bytes profile limits accepted found code certified imports bindings types
  unfold instantiate_tail
  step with initialized as ⟨result, after, host, afterCertified, extension, metadata, sameHost⟩
  subst host
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, afterCertified, metadata]
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have afterFound : after.instances.val[identity.index.val]? = some inst := by
      rw [metadata.space.instances]
      exact found
    step with Interp.vec_index_given after.instances identity.index inst afterFound as ⟨actual, equal⟩
    subst actual
    simp [runtime.compiler.ExecutableModule.env, Exec.module.Module.env,
      Itasca.module.Module.impl.env, Exec.module.Env.start, Itasca.module.Env.impl.start,
      noStart, afterCertified, metadata]

end Exec.Theorems

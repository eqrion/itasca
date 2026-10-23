import Exec.Generated.Equations
import Exec.Store.Initialization.SegmentInitializeShape

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Structural store validity provides the finite constant-read bindings needed
by the compiler's synthetic initialization code. -/
theorem Shape.initializer_bindings {M : Type} {view : M → Slice U8}
    {store : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (shape : Shape view store) (found : inst ∈ store.instances.val) :
    InitializerBindings store inst := by
  have instanceShape := shape.instances inst found
  refine ⟨?_, shape.globals⟩
  intro address member
  exact (instanceShape.2.2.2.2.2.2.2.2.1 address member).2

/-- Without a start function, the committed instantiation tail always returns
normally, preserves the Store invariant, and leaves the platform unchanged.
Segment bounds failures remain ordinary Wasm traps. -/
theorem instantiate_tail_no_start {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (identity : runtime.InstanceAddr)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8) (profile : Itasca.ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module))
    (found : store.instances.val[identity.index.val]? = some inst)
    (shape : Shape view store) (imports : InitializerImports store inst)
    (types : SegmentTypeBindings store inst) (noStart : inst.module.module.env.start = none) :
    runtime.store.instantiate.Store.commit_instance memory hooks floats allocator store platform identity false
      ⦃ out => Shape view out.2.1 ∧ SegmentAddressSpace store out.2.1 ∧
        out.2.2.1 = platform ∧ out.2.2.2 = true ∧
        (∀ address, out.1 = .Ok address → address = identity) ⦄ := by
  have bindings := shape.initializer_bindings (List.mem_of_getElem? found)
  have instanceShape := shape.instances inst (List.mem_of_getElem? found)
  have total := initialize_segments_compiled memory hooks floats allocator view laws law
    store platform identity.index inst bytes profile limits accepted found instanceShape imports bindings
  have valid := initialize_segments_compiled_shape memory hooks floats allocator view laws law
    store platform identity.index inst bytes profile limits accepted found shape imports bindings types
  have combined := segment_specs_and total valid
  unfold runtime.store.instantiate.Store.commit_instance
  step with combined as ⟨result, after, host, metadata, sameHost, afterShape, segmentTypes⟩
  subst host
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, afterShape, metadata]
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have afterFound : after.instances.val[identity.index.val]? = some inst := by
      rw [metadata.instances]
      exact found
    step with Interp.vec_index_given after.instances identity.index inst afterFound as ⟨actual, equal⟩
    subst actual
    simp [runtime.compiler.ExecutableModule.env, Exec.module.Module.env,
      Itasca.module.Module.impl.env, Exec.module.Env.start, Itasca.module.Env.impl.start,
      noStart, afterShape, metadata]

end Exec.Store

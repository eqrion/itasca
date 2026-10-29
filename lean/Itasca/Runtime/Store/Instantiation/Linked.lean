import Itasca.Runtime.Store.Instantiation.Classified
import Itasca.Runtime.Store.Instantiation.PreparedRunCertificates

/-!
Linked instantiation and completed map bounds. Publication boundaries and the resolved, unexecuted start function remain explicit.
-/

/-! ## Instantiate Linked -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Every actual instantiation computation either returns an ordinary precommit
rejection retaining the old store prefix, or reaches a fully shaped committed
store and executes exactly the segment/start tail. This decomposition imposes
no normal-return or termination premise on the computation. -/
theorem instantiate_inner_linked_decomposition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    {tables memories} (cache : Cache module.module.env tables memories)
    (valid : Valid module.module.env module.profile)
    (dataValid : ∀ data ∈ module.module.tail.data.val, Itasca.ModuleData.Valid module.module.env data)
    (compiled : Code.InitializerMappings module)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (outcome : Result (core.result.Result runtime.Instantiated runtime.ExecError × runtime.store.Store M × P × Bool))
    (run : runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false = outcome) :
    (∃ error staged, outcome = .ok (.Err error, staged, platform, false) ∧ StagedPrefix before staged) ∨
    ∃ ready inst, Shape view ready ∧ ready.instances.val[before.instances.len.val]? = some inst ∧
      inst.module = module ∧ InitializerImports ready inst ∧ SegmentTypeBindings ready inst ∧ SegmentAccounting ready ∧ InstantiationCode before ready inst ∧
      Nonempty (LinkedPreparedRun memory hooks floats allocator view before module imports platform ready) ∧
      runtime.store.instantiate.Store.commit_instance memory hooks floats allocator ready platform ⟨before.id, before.instances.len⟩ false =
        outcome := by
  have classified := instantiate_inner_classified_decomposition memory hooks floats allocator law view laws
    before module imports platform shape accounted cache valid dataValid compiled handles outcome run
  rcases classified with ⟨error, staged, returned, retained, _⟩ | committed
  · exact Or.inl ⟨error, staged, returned, retained⟩
  · exact Or.inr committed

end Itasca.Runtime.Store

end

/-! ## Instantiate Linked Bounds -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The accepted public compiler and actual instantiation calls establish the
committed payload bounds. Rejections before commitment still retain the exact
old prefix required by rollback. No preparation or execution certificate is an
input: the successful branch produces its concrete preparation trace. -/
theorem instantiate_compiled_linked_bounded_decomposition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (shape : Shape view before) (accounted : SegmentAccounting before) (bounded : SegmentBounds before)
    (bytes : Slice U8) (profile : Itasca.ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module))
    (handles : ∀ external ∈ imports.val, ExternalIssued before external) :
    (∃ error staged,
      runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false =
        .ok (.Err error, staged, platform, false) ∧ StagedPrefix before staged) ∨
    ∃ ready inst, Shape view ready ∧ ready.instances.val[before.instances.len.val]? = some inst ∧
      inst.module = module ∧ InitializerImports ready inst ∧ SegmentTypeBindings ready inst ∧
      SegmentAccounting ready ∧ InstantiationCode before ready inst ∧ SegmentBounds ready ∧
      Nonempty (LinkedPreparedRun memory hooks floats allocator view before module imports platform ready) ∧
      runtime.store.instantiate.Store.commit_instance memory hooks floats allocator ready platform ⟨before.id, before.instances.len⟩ false =
        runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false := by
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits module accepted
  obtain ⟨tables, memories, cache⟩ := witness.cache law
  have certificates := witness.initializers law
  obtain ⟨valid, dataValid⟩ := witness.semantic law
  have actualValid : Itasca.ModuleEnv.Valid module.module.env module.profile := by
    rw [certificates.2.1]
    exact valid
  have decomposition := instantiate_inner_linked_decomposition memory hooks floats allocator law view laws
    before module imports platform shape accounted cache actualValid dataValid certificates.2.2.2 handles _ rfl
  rcases decomposition with rejected | ⟨ready, inst, readyShape, found, source, initializers, types, counts, code, ⟨trace⟩, tail⟩
  · exact Or.inl rejected
  · exact Or.inr ⟨ready, inst, readyShape, found, source, initializers, types, counts, code,
      trace.toPreparedRun.compiled_segment_bounds laws law shape accounted bounded bytes profile limits accepted, ⟨trace⟩, tail⟩
end Itasca.Runtime.Store

end

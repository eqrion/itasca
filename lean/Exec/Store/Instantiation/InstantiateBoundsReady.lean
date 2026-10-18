import Exec.Store.Instantiation.InstantiatePrepared
import Exec.Store.Instantiation.PreparedRunBounds
namespace Exec.Store
open Aeneas Aeneas.Std

/-- The accepted public compiler and actual instantiation calls establish the
committed payload bounds. Rejections before commitment still retain the exact
old prefix required by rollback. No preparation or execution certificate is an
input: the successful branch produces its concrete preparation trace. -/
theorem instantiate_compiled_bounded_decomposition {M P F A : Type}
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
      Nonempty (PreparedRun memory hooks floats allocator view before module platform ready) ∧
      instantiate_tail memory hooks floats allocator ⟨before.id, before.instances.len⟩ ready platform =
        runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false := by
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits module accepted
  obtain ⟨tables, memories, cache⟩ := witness.cache law
  have certificates := witness.initializers law
  obtain ⟨valid, dataValid⟩ := witness.semantic law
  have actualValid : Itasca.ModuleEnv.Valid module.module.env module.profile := by
    rw [certificates.2.1]
    exact valid
  have decomposition := instantiate_inner_prepared_decomposition memory hooks floats allocator law view laws
    before module imports platform shape accounted cache actualValid dataValid certificates.2.2.2 handles _ rfl
  rcases decomposition with rejected | ⟨ready, inst, readyShape, found, source, initializers, types, counts, code, ⟨trace⟩, tail⟩
  · exact Or.inl rejected
  · exact Or.inr ⟨ready, inst, readyShape, found, source, initializers, types, counts, code,
      trace.compiled_segment_bounds laws law shape accounted bounded bytes profile limits accepted, ⟨trace⟩, tail⟩
end Exec.Store

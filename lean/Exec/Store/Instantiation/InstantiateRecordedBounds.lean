import Exec.Store.Instantiation.PrepareInstanceClassified
import Exec.Store.Instantiation.InstantiateRecording
import Exec.Store.Instantiation.PreparedRunBounds
namespace Exec.Store
open Aeneas Aeneas.Std

/-- The accepted public compiler and actual instantiation calls establish the
committed payload bounds. Rejections before commitment still retain the exact
old prefix required by rollback. No preparation or execution certificate is an
input: the successful branch produces its concrete preparation trace. -/
theorem instantiate_recorded_linked_bounded_decomposition {M P F A : Type}
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
      recordedInstantiateInner memory hooks floats allocator before module imports platform false [] =
        .ok ((.Err error, staged, platform, false),[]) ∧ StagedPrefix before staged) ∨
    ∃ ready inst, Shape view ready ∧ ready.instances.val[before.instances.len.val]? = some inst ∧
      inst.module = module ∧ InitializerImports ready inst ∧ SegmentTypeBindings ready inst ∧
      SegmentAccounting ready ∧ InstantiationCode before ready inst ∧ SegmentBounds ready ∧
      Nonempty (LinkedPreparedRun memory hooks floats allocator view before module imports platform ready) ∧
      recordedInstantiateTail memory hooks floats allocator ⟨before.id, before.instances.len⟩ ready platform [] =
        recordedInstantiateInner memory hooks floats allocator before module imports platform false [] := by
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits module accepted
  obtain ⟨tables, memories, cache⟩ := witness.cache law
  have certificates := witness.initializers law
  obtain ⟨valid, dataValid⟩ := witness.semantic law
  have actualValid : Itasca.ModuleEnv.Valid module.module.env module.profile := by
    rw [certificates.2.1]
    exact valid
  rcases prepare_instance_classified memory hooks floats allocator law view laws before module imports
      platform shape accounted cache actualValid dataValid certificates.2.2.2 handles _ rfl with
    ⟨error, staged, prepared, retained, _, _⟩ |
      ⟨staged, items, charged, ready, inst, charge, rfl, readyShape, found, source, initializers, types, counts,
        code, ⟨trace⟩, prepared⟩
  · refine Or.inl ⟨error, staged, ?_, retained⟩
    simp [recordedInstantiateInner, prepared, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
  · refine Or.inr ⟨_, inst, readyShape, found, source, initializers, types, counts, code,
      trace.toPreparedRun.compiled_segment_bounds laws law shape accounted bounded bytes profile limits accepted,
      ⟨trace⟩, ?_⟩
    simp only [recordedInstantiateInner, prepared, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      uncurry_apply_pair, charge]
end Exec.Store

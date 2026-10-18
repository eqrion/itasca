import Exec.Store.Instantiation.InstantiateDecomposition
import Exec.Store.Instantiation.InstantiateTailCommit

namespace Exec.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Every normally returned precommit branch is a rejection, preserves the
platform, and retains every old store object. This theorem concerns the false
commit flag; postcommit execution safety is a separate interpreter theorem. -/
theorem instantiate_inner_precommit {M P F A : Type}
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
    (result : core.result.Result runtime.InstanceAddr runtime.ExecError)
    (after : runtime.store.Store M) (host : P)
    (run : runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false =
      .ok (result, after, host, false)) : host = platform ∧ (∃ error, result = .Err error) ∧ StagedPrefix before after := by
  have parts := instantiate_inner_decomposition memory hooks floats allocator law view laws before module
    imports platform shape accounted cache valid dataValid compiled handles _ run
  rcases parts with ⟨error, staged, rejected, retained⟩ | ⟨ready, inst, shaped, found, source, initialized, types, accounting, code, continued⟩
  · have equal := Result.ok_injective rejected
    cases equal
    exact ⟨rfl, ⟨error, rfl⟩, retained⟩
  · have flag := instantiate_tail_committed memory hooks floats allocator
      ⟨before.id, before.instances.len⟩ ready platform result after host false continued
    cases flag

end Exec.Store

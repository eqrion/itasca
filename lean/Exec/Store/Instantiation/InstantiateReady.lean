import Exec.Store.Instantiation.InstantiateDecomposition

namespace Exec.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- Every actual normally returned committed path reaches a fully shaped store
before executing segments or its optional start function. The remaining actual
computation is retained explicitly, so host execution is not assumed safe. -/
theorem instantiate_inner_committed_ready {M P F A : Type}
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
      .ok (result, after, host, true)) :
    ∃ ready inst, Shape view ready ∧ ready.instances.val[before.instances.len.val]? = some inst ∧
      inst.module = module ∧ InitializerImports ready inst ∧ SegmentTypeBindings ready inst ∧ SegmentAccounting ready ∧ InstantiationCode before ready inst ∧
      instantiate_tail memory hooks floats allocator ⟨before.id, before.instances.len⟩ ready platform =
        .ok (result, after, host, true) := by
  have parts := instantiate_inner_decomposition memory hooks floats allocator law view laws before module
    imports platform shape accounted cache valid dataValid compiled handles _ run
  rcases parts with ⟨error, staged, rejected, retained⟩ | ready
  · have flag := congrArg (fun out => out.2.2.2) (Result.ok_injective rejected)
    cases flag
  · exact ready

end Exec.Store

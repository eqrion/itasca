import Exec.Store.Instantiation.InstantiatePrepared
namespace Exec.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv

/-- Every actual instantiation computation either returns an ordinary precommit
rejection retaining the old store prefix, or reaches a fully shaped committed
store and executes exactly the segment/start tail. This decomposition imposes
no normal-return or termination premise on the computation. -/
theorem instantiate_inner_decomposition {M P F A : Type}
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
    (outcome : Result (core.result.Result runtime.InstanceAddr runtime.ExecError × runtime.store.Store M × P × Bool))
    (run : runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false = outcome) :
    (∃ error staged, outcome = .ok (.Err error, staged, platform, false) ∧ StagedPrefix before staged) ∨
    ∃ ready inst, Shape view ready ∧ ready.instances.val[before.instances.len.val]? = some inst ∧
      inst.module = module ∧ InitializerImports ready inst ∧ SegmentTypeBindings ready inst ∧ SegmentAccounting ready ∧ InstantiationCode before ready inst ∧
      runtime.store.instantiate.Store.commit_instance memory hooks floats allocator ready platform ⟨before.id, before.instances.len⟩ false =
        outcome := by
  have decomposition := instantiate_inner_prepared_decomposition memory hooks floats allocator law view laws
    before module imports platform shape accounted cache valid dataValid compiled handles outcome run
  rcases decomposition with rejected | ⟨ready, inst, shape, found, source, imports, types, accounting, code, trace, tail⟩
  · exact Or.inl rejected
  · exact Or.inr ⟨ready, inst, shape, found, source, imports, types, accounting, code, tail⟩
end Exec.Store

import Itasca.Runtime.Store.Instantiation.PrepareInstanceClassified
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std Itasca.ModuleEnv

/-- Every actual instantiation computation either returns an ordinary precommit
rejection retaining the old store prefix, or reaches a fully shaped committed
store and executes exactly the segment/start tail. This decomposition imposes
no normal-return or termination premise on the computation. -/
theorem instantiate_inner_classified_decomposition {M P F A : Type}
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
    (∃ error staged, outcome = .ok (.Err error, staged, platform, false) ∧ StagedPrefix before staged ∧ PrecommitError module.profile error ∧ PrecommitOrigins memory view before staged module imports error) ∨
    ∃ ready inst, Shape view ready ∧ ready.instances.val[before.instances.len.val]? = some inst ∧
      inst.module = module ∧ InitializerImports ready inst ∧ SegmentTypeBindings ready inst ∧ SegmentAccounting ready ∧ InstantiationCode before ready inst ∧
      Nonempty (LinkedPreparedRun memory hooks floats allocator view before module imports platform ready) ∧
      runtime.store.instantiate.Store.commit_instance memory hooks floats allocator ready platform ⟨before.id, before.instances.len⟩ false =
        outcome := by
  unfold runtime.store.instantiate.Store.instantiate_inner at run
  rcases prepare_instance_classified memory hooks floats allocator law view laws before module imports
      platform shape accounted cache valid dataValid compiled handles _ rfl with
    ⟨error, staged, prepared, rest⟩ | ⟨staged, items, charged, ready, inst, charge, rfl, rest⟩
  · rw [prepared] at run
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, uncurry_apply_pair] at run
    exact Or.inl ⟨error, staged, run.symm, rest⟩
  · obtain ⟨shaped, found, source, imported, types, accounting, code, linked, prepared⟩ := rest
    rw [prepared] at run
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair, charge] at run
    exact Or.inr ⟨_, inst, shaped, found, source, imported, types, accounting, code, linked, run⟩
end Itasca.Runtime.Store

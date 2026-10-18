import Exec.Store.Instantiation.InstantiatePrefix
import Exec.Store.Invariant.Rollback

namespace Exec.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- A normally returned precommit failure of the actual inner implementation
makes the public wrapper return that error with the exact original store and
platform. The staged-prefix obligation is derived from compiled initializer
certificates and source typing, rather than assumed. -/
theorem instantiate_precommit_rollback {M P F A : Type}
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
      .ok (result, after, host, false)):
    runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform =
      .ok (result, before, platform) := by
  obtain ⟨sameHost, ⟨error, sameResult⟩, retained⟩ := instantiate_inner_precommit memory hooks floats allocator
    law view laws before module imports platform shape accounted cache valid dataValid compiled handles result after host run
  subst host
  subst result
  have checked := instantiate_rollback memory hooks floats allocator before after module imports platform platform error retained run
  obtain ⟨⟨answer, finalStore, finalHost⟩, executed, answerEq, storeEq, hostEq⟩ := WP.spec_imp_exists checked
  subst answer
  subst finalStore
  subst finalHost
  exact executed

end Exec.Store

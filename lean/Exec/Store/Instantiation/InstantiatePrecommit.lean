import Exec.Store.Instantiation.InstantiateClassified
import Exec.Store.Instantiation.TailCommit
import Exec.Store.Instantiation.PreparedRunBounds
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- A normally returning precommit rejection of an actually compiled module
has one of the documented API/resource/Wasm1-precheck causes. In particular,
Wasm2 traps cannot originate before publication. Foreign handles are admitted
by ExternalIssued and retain their explicit WrongStore outcome. -/
theorem instantiate_compiled_precommit_origins {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    (bytes : Slice U8) (profile : Itasca.ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module))
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (error : runtime.ExecError) (staged : runtime.store.Store M) (host : P)
    (run : runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false =
      .ok (.Err error, staged, host, false)) :
    PrecommitError profile error ∧ host = platform ∧ StagedPrefix before staged ∧
      PrecommitOrigins memory view before staged module imports error := by
  obtain ⟨witness⟩ := Code.compile_accepted allocator bytes profile limits module accepted
  obtain ⟨tables, memories, cache⟩ := witness.cache law
  have certificates := witness.initializers law
  obtain ⟨valid, dataValid⟩ := witness.semantic law
  have actualValid : Itasca.ModuleEnv.Valid module.module.env module.profile := by
    rw [certificates.2.1]
    exact valid
  have decomposition := instantiate_inner_classified_decomposition memory hooks floats allocator law view laws
    before module imports platform shape accounted cache actualValid dataValid certificates.2.2.2 handles _ run
  rcases decomposition with ⟨rejected, after, outcome, retained, cause, origins⟩ |
      ⟨ready, inst, readyShape, found, source, initializers, types, counts, code, trace, tail⟩
  · simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq] at outcome
    obtain ⟨rfl, rfl, rfl, _⟩ := outcome
    exact ⟨by simpa only [certificates.2.1] using cause, rfl, retained, origins⟩
  · have committed := instantiate_tail_committed_result memory hooks floats allocator ⟨before.id, before.instances.len⟩
      ready platform _ tail
    contradiction

end Itasca.Runtime.Store

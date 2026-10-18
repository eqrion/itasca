import Exec.Store.Instantiation.InstantiatePrecommit
import Exec.Store.Instantiation.PrecommitSource
import Exec.Code.Module.CompileSource
namespace Exec.Store
open Aeneas Aeneas.Std Itasca

/-- An actual Wasm1 precommit trap identifies a source active-segment bounds
failure and the public API restores the exact old store and platform. This
rejection guarantee needs no instruction-subset or execution certificate. -/
theorem instantiate_compiled_wasm1_bounds {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (shape : Shape view before) (accounted : SegmentAccounting before)
    (code : CodeInterpretation) (sourceSyntax : StoreSyntax code before)
    (bytes : Slice U8) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes .Wasm1 limits = .ok (.Ok module))
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (trap : runtime.Trap) (staged : runtime.store.Store M) (host : P)
    (run : runtime.store.instantiate.Store.instantiate_inner memory hooks floats allocator before module imports platform false =
      .ok (.Err (.Trap trap), staged, host, false)) :
    ∃ raw inst,
      ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding .Wasm1) raw bytes.val .Wasm1 ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧
      staged.instances.val[before.instances.length]? = some inst ∧ inst.module = module ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ result after nextPlatform => result = .Err (.Trap trap) ∧ after = before ∧ nextPlatform = platform ∧
          SpecExt.Wasm1.BoundsRollback (decodeStore view code before)
            (decodeStore view (installCode code before.instances.length (Code.sourceFunctions raw)) staged)
            (decodeInstance staged inst) (raw.elements.map ModuleElaboration.element)
            (raw.data.map ModuleData.translate) (decodeStore view code after) ⦄ := by
  obtain ⟨cause, sameHost, retained, origins⟩ := instantiate_compiled_precommit_origins
    memory hooks floats allocator law view laws before module imports platform shape accounted
    bytes .Wasm1 limits accepted handles (.Trap trap) staged host run
  subst host
  obtain ⟨validated, profile, size⟩ := Code.compile_source_validated allocator law bytes .Wasm1 limits module accepted
  obtain ⟨raw, encoded, elaborated, matched, typed, restrictions, accessors⟩ := validated
  obtain ⟨inst, found, source, bounds⟩ := origins.source_bounds retained code sourceSyntax raw elaborated typed matched
  refine ⟨raw, inst, encoded, typed, found, source, ?_⟩
  obtain ⟨out, publicRun, returned, sameStore, samePlatform⟩ := WP.spec_imp_exists
    (instantiate_rollback memory hooks floats allocator before staged module imports
      platform platform (.Trap trap) retained run)
  rw [publicRun, WP.spec_ok]
  refine ⟨returned, sameStore, samePlatform, ?_⟩
  rw [sameStore]
  exact .reject bounds
end Exec.Store

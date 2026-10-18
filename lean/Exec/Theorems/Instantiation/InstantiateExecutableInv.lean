import Exec.Theorems.Api.ExecutableInv
import Exec.Theorems.Instantiation.InstantiateExecutableApiSource
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

theorem instantiate_compiled_executable_invariant {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (correct : Platform.FloatOpsCorrect floats)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : ExecutableInv view oldCode before)
    (hostFree : CoreHostFree before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module)) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ out => ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1 ∧ InstantiationSourceOutcome view oldCode
            (installCode oldCode before.instances.length (Code.sourceFunctions raw)) before module imports raw platform
            out.1 out.2.1 out.2.2 ⦄div := by
  obtain ⟨raw,encoded,typed,run⟩ := instantiate_compiled_executable_api_source memory hooks floats allocator
    view laws correct law interrupts before module imports platform oldCode old.toCertifiedApiStore hostFree
    old.segmentAccounting handles bytes profile limits accepted
  refine ⟨raw,encoded,typed,?_⟩
  apply WP.dspec_mono run
  rintro out ⟨certified,capacities,accounted,outcome⟩
  exact ⟨⟨certified,accounted,capacities old.capacities⟩,outcome⟩

end Exec.Theorems

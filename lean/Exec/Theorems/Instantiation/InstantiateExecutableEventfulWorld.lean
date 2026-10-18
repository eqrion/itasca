import Exec.Theorems.Instantiation.InstantiateExecutableEventfulExtension
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- Actual public instantiation supplies the fresh ghost world and agreement
on all previously issued keys. It never asks the caller to preassign source
bodies at future instance keys. Callback hypotheses remain exactly those of
the existing fixed-world instantiation theorem. -/
theorem instantiate_compiled_executable_eventful_world {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (correct : Platform.FloatOpsCorrect floats)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : ExecutableInv view oldCode before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module)) 
    (raw : ModuleBinary.Module)
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile)
    (sound : Platform.HostSound hooks
      (ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)))
      (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw))))
    (preserve : ∀ store, ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (externs : ∀ store, ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ store, ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer →
      ∀ value ∈ answer.2.2.2.val, IssuedValue answer.2.2.1 value) :
    Module_ok (ModuleElaboration.moduleOf raw) ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ out => ∃ afterCode : CodeInterpretation,
          CodeAgreesOn before oldCode afterCode ∧ ExecutableInv view afterCode out.2.1 ∧
          Extend_store (decodeStore view oldCode before) (decodeStore view afterCode out.2.1) ∧
          EventfulInstantiationSourceOutcome view oldCode afterCode before module imports raw platform
            out.1 out.2.1 out.2.2 ⦄div := by
  obtain ⟨typed,run⟩ := instantiate_compiled_executable_eventful_source_extends
    memory hooks floats allocator view laws correct law interrupts before module imports platform
    oldCode old handles bytes profile limits accepted raw encoded sound preserve externs issued
  refine ⟨typed,WP.dspec_mono run ?_⟩
  intro out result
  exact ⟨installCode oldCode before.instances.length (Code.sourceFunctions raw),
    installCode_agrees before oldCode (Code.sourceFunctions raw),result⟩
end Exec.Theorems

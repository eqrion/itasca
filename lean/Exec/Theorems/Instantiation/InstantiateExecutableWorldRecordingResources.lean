import Exec.Theorems.Instantiation.InstantiateExecutableWorldRecording
import Exec.Theorems.Instantiation.InstantiateExecutableWorldResources
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- Every normal raw result carries the exact log returned by the transparent
instantiation recorder, with one final code interpretation for all guarantees. -/
theorem instantiate_compiled_executable_world_recording_resources {M P F A : Type}
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
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀ c store, ExecutableInv view c store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (externs : ∀ c store, ExecutableInv view c store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ c store, ExecutableInv view c store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer →
      ∀ value ∈ answer.2.2.2.val, IssuedValue answer.2.2.1 value) :
    Module_ok (ModuleElaboration.moduleOf raw) ∧
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ out => ∃ events, recordedInstantiateWith memory hooks floats allocator before module imports platform [] = .ok (out,events) ∧
          ∃ afterCode, CodeAgreesOn before oldCode afterCode ∧
          ExecutableInv view afterCode out.2.1 ∧ Interp.FrameStorePrefix before out.2.1 ∧
          Extend_store (decodeStore view oldCode before)
            (decodeStore view afterCode out.2.1) ∧
          RecordedInstantiationSourceOutcome view oldCode
            afterCode before module imports raw platform
            events out.1 out.2.1 out.2.2 ∧
          (∀error,out.1=.Err error → WorldExecutableInstantiationResourceCause memory hooks floats allocator
            view oldCode before module imports platform raw out.2.1 error) ⦄div := by
  obtain ⟨typed,recorded⟩ := instantiate_compiled_executable_world_recording_source memory hooks floats allocator
    view laws correct law interrupts before module imports platform oldCode old handles bytes profile limits
    accepted raw encoded sound preserve externs issued
  have causes := (instantiate_compiled_executable_world_resource_causes memory hooks floats allocator
    view laws correct law interrupts before module imports platform oldCode old handles bytes profile limits
    accepted raw encoded sound preserve externs issued).2
  refine ⟨typed,?_⟩
  generalize actual : runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform=call at recorded causes
  cases recorded with
  | ret held =>
    obtain ⟨events,graph,afterCode,agrees,fresh,kept,extension,source⟩ := held
    exact WP.dspec.ret ⟨events,graph,afterCode,agrees,fresh,kept,extension,source,by simpa only [WP.dspec_ok] using causes⟩
  | div => exact WP.dspec.div _
end Exec.Theorems

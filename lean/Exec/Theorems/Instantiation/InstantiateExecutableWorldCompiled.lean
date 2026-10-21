import Exec.Theorems.Instantiation.InstantiateExecutableWorldRecordedCompiled

/-! Ordinary compiled instantiation packages projected from recorded packages.
Accepted-compilation and all-input boundaries retain their distinct return guarantees. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- The source package follows from the actual accepted compiler result;
no separately supplied raw module or encoding premise is required. -/
theorem instantiate_compiled_executable_world_packaged {M P F A : Type}
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
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module)) :
    CompiledWorldInstantiation memory hooks floats allocator view before module imports platform oldCode bytes profile := by
  exact (instantiate_compiled_executable_world_recorded_packaged memory hooks floats allocator view laws correct law
    interrupts before module imports platform oldCode old handles bytes profile limits accepted).erase

/-- Arbitrary input bytes return a reported compilation error or a canonical
source package supporting an evolving-code callback contract. -/
theorem compile_executable_world_packaged {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (correct : Platform.FloatOpsCorrect floats)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (before : runtime.store.Store M)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : ExecutableInv view oldCode before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits) :
    runtime.compiler.compile_with allocator bytes profile limits ⦃ result =>
      match result with
      | .Err _ => True
      | .Ok module => CompiledWorldInstantiation memory hooks floats allocator view before module imports platform oldCode bytes profile ⦄ := by
  apply WP.spec_mono (compile_executable_world_recorded_packaged memory hooks floats allocator view laws correct law
    interrupts before imports platform oldCode old handles bytes profile limits)
  intro result package
  cases result with
  | Err error => trivial
  | Ok module => exact package.erase
end Exec.Theorems

import Exec.Theorems.Instantiation.InstantiateExecutableEventfulExtension
import Exec.Code.Module.CompileTotal
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- Successful compilation chooses the canonical source syntax before the
caller supplies host laws for that exact installed interpretation. -/
def CompiledEventfulInstantiation {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (before : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (platform : P) (oldCode : CodeInterpretation) (bytes : Slice U8)
    (profile : ValidationProfile) : Prop :=
  ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
    Module_ok (ModuleElaboration.moduleOf raw) ∧
    ∀ (_sound : Platform.HostSound hooks
      (ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)))
      (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw))))
    (_preserve : ∀ store, ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (_externs : ∀ store, ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (_issued : ∀ store, ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer →
      ∀ value ∈ answer.2.2.2.val, IssuedValue answer.2.2.1 value),
      runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform
        ⦃ out => ExecutableInv view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1 ∧
          Extend_store (decodeStore view oldCode before)
            (decodeStore view (installCode oldCode before.instances.length (Code.sourceFunctions raw)) out.2.1) ∧
          EventfulInstantiationSourceOutcome view oldCode
            (installCode oldCode before.instances.length (Code.sourceFunctions raw)) before module imports raw platform
            out.1 out.2.1 out.2.2 ⦄div

/-- The source package follows from the actual accepted compiler result;
no separately supplied raw module or encoding premise is required. -/
theorem instantiate_compiled_executable_eventful_packaged {M P F A : Type}
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
    CompiledEventfulInstantiation memory hooks floats allocator view before module imports platform oldCode bytes profile := by
  obtain ⟨raw,encoded,elaborated,matched,typed,rest⟩ :=
    Code.compile_executable_functions allocator law bytes profile limits module accepted
  refine ⟨raw,encoded,typed,?_⟩
  intro sound preserve externs issued
  exact (instantiate_compiled_executable_eventful_source_extends memory hooks floats allocator view laws correct law
    interrupts before module imports platform oldCode old handles bytes profile limits accepted
    raw encoded sound preserve externs issued).2

/-- Arbitrary input bytes return a reported compilation error or a canonical
source package whose host laws are quantified only after its source is known. -/
theorem compile_executable_eventful_packaged {M P F A : Type}
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
      | .Ok module => CompiledEventfulInstantiation memory hooks floats allocator view before module imports platform oldCode bytes profile ⦄ := by
  obtain ⟨result,actual,_⟩ := WP.spec_imp_exists (Code.compile_with_total allocator law bytes profile limits)
  rw [actual]
  simp only [WP.spec_ok]
  cases result with
  | Err error => trivial
  | Ok module =>
    exact instantiate_compiled_executable_eventful_packaged memory hooks floats allocator view laws correct law
      interrupts before module imports platform oldCode old handles bytes profile limits actual
end Exec.Theorems

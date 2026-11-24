import Itasca.Results.Definitions.Compiler.Compilation
import Itasca.Runtime.Compiler.Module.Compilation
import Itasca.Runtime.Integration.Compilation
import Itasca.Runtime.Compiler.Module.DriverAndCodeRegions

/-!
# Compilation

Soundness, normal return and completeness of `runtime.compiler.compile_with` and
`runtime.compiler.compile_default_with` for WebAssembly Core 2.0.

Acceptance yields `Integration.CompilationSource`: one independently encoded,
elaborated and typed source module, with matching metadata and accessor types.
The runtime protocol connects actual accepted compilation to instantiation and
execution. Emission/layout certificates are internal construction details.

Soundness and normal return need only `Platform.AllocCorrect`. Completeness additionally needs
independent source validity, the source-only `Compiler.CompileEligible` envelope, and
`Platform.AllocationAvailable`; see [Platform](Definitions/Platform.lean).
-/

open Aeneas Aeneas.Std

namespace Itasca

open Itasca Integration

/-- Accepted compilation supplies one typed source module and matching metadata.
The runtime protocol uses the same acceptance evidence to establish instantiation
and execution behavior, without a public emitted-code certificate. -/
theorem Compiler.compile_with.sound {A} (ops : runtime.platform.Alloc A)
    (allocator_correct : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) (executable : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with ops bytes limits = .ok (.Ok executable)) :
    CompilationSource bytes executable :=
  (compile_accepted_certificate ops allocator_correct bytes limits executable accepted).source

/-- Arbitrary input returns an ordinary result, and success carries the source/metadata association. The result may be a Rust error, including allocation refusal. -/
theorem Compiler.compile_with.spec {A} (ops : runtime.platform.Alloc A)
    (allocator_correct : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) :
    runtime.compiler.compile_with ops bytes limits ⦃ result =>
      ∀ executable, result = .Ok executable → CompilationSource bytes executable ⦄ := by
  obtain ⟨result,run,_⟩ := WP.spec_imp_exists (Compiler.compile_with_total ops allocator_correct bytes limits)
  rw [run,WP.spec_ok]
  intro executable accepted
  exact (compile_accepted_certificate ops allocator_correct bytes limits executable (by simpa only [accepted] using run)).source

/-- The default-limit public compiler has the same source/metadata association and normal-return
guarantee, including its actual error conversion. -/
theorem Compiler.compile_default_with.spec {A} (ops : runtime.platform.Alloc A)
    (allocator_correct : Platform.AllocCorrect ops) (bytes : Slice U8) :
    runtime.compiler.compile_default_with ops bytes ⦃ result =>
      ∀ executable, result = .Ok executable → CompilationSource bytes executable ⦄ := by
  unfold runtime.compiler.compile_default_with
  step with Compiler.compiler_default_limits_total as ⟨limits⟩
  step with Compiler.compile_with.spec ops allocator_correct bytes limits as ⟨result,certificate⟩
  cases result with
  | Ok executable => simpa using certificate
  | Err error => cases error <;> simp

/-- Independent source validity and explicit compiler eligibility imply actual
successful compilation with the source/metadata association. Allocation availability bounds
individual requests; it is not an assumption of successful compilation or of an accepted callback
trace.

The source budget computes the conservative body, local and operand allowances;
callers do not choose auxiliary maxima or metadata witnesses. It need not accept every module whose actual output happens to lie exactly at the
configured limits. -/
theorem Compiler.compile_with.complete {A : Type} (ops : runtime.platform.Alloc A)
    (allocator_correct : Platform.AllocCorrect ops)
    (bytes : Slice U8) (raw : Binary.Module)
    (limits : runtime.compiler.CompileLimits) (valid_source : Compiler.ValidCompilationSource bytes raw)
    (source_eligible : Compiler.CompileEligible bytes raw limits)
    (allocation_available : Platform.AllocationAvailable ops (Compiler.compilationBudget bytes.length raw).allocation) :
    ∃ executable, runtime.compiler.compile_with ops bytes limits = .ok (.Ok executable) ∧
      CompilationSource bytes executable := by
  obtain ⟨executable, accepted, certificate⟩ := compile_complete ops allocator_correct _ allocation_available bytes raw limits valid_source
    (source_eligible.internal valid_source)
  exact ⟨executable, accepted, certificate.source⟩

/-- `complete` as an Aeneas normal-return contract: successful Rust return and its source
certificate. -/
theorem Compiler.compile_with.complete_spec {A : Type} (ops : runtime.platform.Alloc A)
    (allocator_correct : Platform.AllocCorrect ops)
    (bytes : Slice U8) (raw : Binary.Module)
    (limits : runtime.compiler.CompileLimits) (valid_source : Compiler.ValidCompilationSource bytes raw)
    (source_eligible : Compiler.CompileEligible bytes raw limits)
    (allocation_available : Platform.AllocationAvailable ops (Compiler.compilationBudget bytes.length raw).allocation) :
    runtime.compiler.compile_with ops bytes limits ⦃ result =>
      ∃ executable, result = .Ok executable ∧ CompilationSource bytes executable ⦄ := by
  obtain ⟨executable,compiled,certificate⟩ := compile_complete ops allocator_correct _ allocation_available bytes raw limits valid_source
    (source_eligible.internal valid_source)
  rw [compiled,WP.spec_ok]
  exact ⟨executable,rfl,certificate.source⟩

end Itasca

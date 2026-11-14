import Itasca.Runtime.Compiler.Module.CompileTotal
import Itasca.Runtime.Integration.Compilation.Complete

/-!
# Compilation

Soundness, normal return and completeness of `runtime.compiler.compile_with` and
`runtime.compiler.compile_default_with` for WebAssembly Core 2.0.

Acceptance yields `Integration.CompilationCertificate`: one independently encoded, elaborated, typed
source module, related to the compiled code by `Integration.ModuleCodeRel`
(metadata, accessor types, function and initializer code, and decoded frame capacities). The code
relations are syntactic; they assume no machine execution. The certificate lives with its
construction in `Runtime/Integration/Compilation/Certificate.lean` because internal host-publication proofs use it.

Soundness and normal return need only `Platform.AllocCorrect`. Completeness additionally needs
independent source validity, the source-only `Compiler.CompileEligible` envelope, and
`Platform.AllocationAvailable`; see [Contracts](../Runtime/Contracts.lean).
-/

open Aeneas Aeneas.Std

namespace Itasca.Runtime

open Itasca Integration

/-- Every accepted compilation constructs its source module and complete module code relation
under the allocator law. Neither an accepted-body nor an opcode-subset premise is needed. -/
theorem runtime.compiler.compile_with.sound {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) (executable : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with ops bytes limits = .ok (.Ok executable)) :
    CompilationCertificate bytes executable :=
  compile_accepted_certificate ops law bytes limits executable accepted

/-- Arbitrary input returns an ordinary result, and success carries the constructed compilation
certificate. The result may be a Rust error, including allocation refusal. -/
theorem runtime.compiler.compile_with.spec {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) :
    runtime.compiler.compile_with ops bytes limits ⦃ result =>
      ∀ executable, result = .Ok executable → CompilationCertificate bytes executable ⦄ := by
  obtain ⟨result,run,_⟩ := WP.spec_imp_exists (Compiler.compile_with_total ops law bytes limits)
  rw [run,WP.spec_ok]
  intro executable accepted
  exact compile_accepted_certificate ops law bytes limits executable (by simpa only [accepted] using run)

/-- The default-limit public compiler has the same constructed certificate and normal-return
guarantee, including its actual error conversion. -/
theorem runtime.compiler.compile_default_with.spec {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8) :
    runtime.compiler.compile_default_with ops bytes ⦃ result =>
      ∀ executable, result = .Ok executable → CompilationCertificate bytes executable ⦄ := by
  unfold runtime.compiler.compile_default_with
  step with Compiler.compiler_default_limits_total as ⟨limits⟩
  step with runtime.compiler.compile_with.spec ops law bytes limits as ⟨result,certificate⟩
  cases result with
  | Ok executable => simpa using certificate
  | Err error => cases error <;> simp

/-- Independent source validity and explicit compiler eligibility imply actual
successful compilation with the constructed module certificate. Allocation availability bounds
individual requests; it is not an assumption of successful compilation or of an accepted callback
trace.

The conservative eligibility envelope includes uniform valid-source body, expanded-local, and
operand maxima. It need not accept every module whose actual output happens to lie exactly at the
configured limits. -/
theorem runtime.compiler.compile_with.complete {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (bytes : Slice U8) (raw : ModuleBinary.Module)
    (limits : runtime.compiler.CompileLimits) (valid : Compiler.ValidCompilationSource bytes raw)
    (eligible : Compiler.CompileEligible A bytes raw limits bound) :
    ∃ executable, runtime.compiler.compile_with ops bytes limits = .ok (.Ok executable) ∧
      CompilationCertificate bytes executable :=
  compile_complete ops law bound allocation bytes raw limits valid eligible

/-- `complete` as an Aeneas normal-return contract: successful Rust return and its source
certificate. -/
theorem runtime.compiler.compile_with.complete_spec {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (bytes : Slice U8) (raw : ModuleBinary.Module)
    (limits : runtime.compiler.CompileLimits) (valid : Compiler.ValidCompilationSource bytes raw)
    (eligible : Compiler.CompileEligible A bytes raw limits bound) :
    runtime.compiler.compile_with ops bytes limits ⦃ result =>
      ∃ executable, result = .Ok executable ∧ CompilationCertificate bytes executable ⦄ := by
  obtain ⟨executable,compiled,certificate⟩ := compile_complete ops law bound allocation bytes raw limits valid eligible
  rw [compiled,WP.spec_ok]
  exact ⟨executable,rfl,certificate⟩

end Itasca.Runtime

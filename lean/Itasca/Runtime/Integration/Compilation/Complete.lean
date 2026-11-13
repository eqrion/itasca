import Itasca.Runtime.Integration.Compilation.Certificate
import Itasca.Runtime.Compiler.Module.CompilationAvailable

/-!
Independent complete-profile source validity and explicit compiler eligibility imply actual successful compilation with the constructed module certificate. Allocation availability bounds individual requests; it is not an assumption of successful compilation or of an accepted callback trace. The conservative eligibility envelope includes uniform valid-source body, expanded-local, and operand maxima. It need not accept every module whose actual output happens to lie exactly at the configured limits.

Main declarations: `compile_complete`. A direct consumer is `Itasca.Results.Compile`.
-/

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca

/-- Independent complete-profile source validity and explicit compiler
eligibility imply actual successful compilation with the constructed module
certificate. Allocation availability bounds individual requests; it is not an
assumption of successful compilation or of an accepted callback trace.

The conservative eligibility envelope includes uniform valid-source body,
expanded-local, and operand maxima. It need not accept every module whose
actual output happens to lie exactly at the configured limits. -/
theorem compile_complete {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (bytes : Slice U8) (raw : ModuleBinary.Module)
    (limits : runtime.compiler.CompileLimits) (valid : Compiler.ValidCompilationSource bytes raw)
    (eligible : Compiler.CompileEligible A bytes raw limits bound) :
    ∃ executable, runtime.compiler.compile_with ops bytes limits = .ok (.Ok executable) ∧
      CompilationCertificate bytes executable := by
  obtain ⟨executable,compiled⟩ := Compiler.compile_with_available ops law bound allocation bytes raw limits valid eligible
  exact ⟨executable,compiled,compile_accepted_certificate ops law bytes limits executable compiled⟩

end Itasca.Runtime.Integration

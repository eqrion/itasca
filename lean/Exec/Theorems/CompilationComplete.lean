import Exec.Theorems.Compilation
import Exec.Code.Module.CompilationAvailable

namespace Itasca.Runtime.Theorems
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
    (bytes : Slice U8) (profile : ValidationProfile) (raw : ModuleBinary.Module)
    (limits : runtime.compiler.CompileLimits) (valid : Code.ValidCompilationSource bytes profile raw)
    (eligible : Code.CompileEligible A bytes profile raw limits bound) :
    ∃ executable, runtime.compiler.compile_with ops bytes profile limits = .ok (.Ok executable) ∧
      CompilationCertificate bytes profile executable := by
  obtain ⟨executable,compiled⟩ := Code.compile_with_available ops law bound allocation bytes profile raw limits valid eligible
  exact ⟨executable,compiled,compile_accepted_certificate ops law bytes profile limits executable compiled⟩

end Itasca.Runtime.Theorems

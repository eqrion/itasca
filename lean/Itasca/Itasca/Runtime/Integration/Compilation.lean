import Itasca.Runtime.Compiler.Module.Definitions
import Itasca.Runtime.Compiler.Module.Compilation
import Itasca.Runtime.Compiler.Module.BatchLoopAvailable

/-! ## Certificate -/

section

/-!
Constructs module-level compiler correspondence with exact source ordering,
function-local instruction/table certificates, initializers, and decoded frame
capacities. The syntactic `ModuleCodeRel` and `CompilationCertificate` definitions
are in [the interface](../../Results/Definitions/Compiler/Compilation.lean).
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca

/-- T1: every actual accepted compilation constructs its source and complete
module code relation under the allocator law. -/
theorem compile_accepted_certificate {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8)
    (limits : runtime.compiler.CompileLimits) (executable : runtime.compiler.ExecutableModule)
    (accepted : runtime.compiler.compile_with ops bytes limits = .ok (.Ok executable)) :
    CompilationCertificate bytes executable := by
  obtain ⟨raw,encoded,elaborated,metadata,typed,restrictions,accessors,functions,initializers⟩ :=
    Compiler.compile_executable_functions ops law bytes limits executable accepted
  obtain ⟨other,otherEncoded,_,_,_,_,_,capacities⟩ :=
    Compiler.compile_executable_capacities ops law bytes limits executable accepted
  have same := Binary.module_unique encoded otherEncoded
  subst other
  exact ⟨raw,encoded,elaborated,typed,restrictions,⟨metadata,accessors,functions,initializers,capacities⟩⟩
end Itasca.Integration

end

/-! ## Complete -/

section

/-!
Independent complete source validity and explicit compiler eligibility imply actual successful compilation with the constructed module certificate. Allocation availability bounds individual requests; it is not an assumption of successful compilation or of an accepted callback trace. The conservative eligibility envelope includes uniform valid-source body, expanded-local, and operand maxima. It need not accept every module whose actual output happens to lie exactly at the configured limits.

Main declarations: `compile_complete`.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca

/-- Independent complete source validity and explicit compiler
eligibility imply actual successful compilation with the constructed module
certificate. Allocation availability bounds individual requests; it is not an
assumption of successful compilation or of an accepted callback trace.

The conservative eligibility envelope includes uniform valid-source body,
expanded-local, and operand maxima. It need not accept every module whose
actual output happens to lie exactly at the configured limits. -/
theorem compile_complete {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (bytes : Slice U8) (raw : Binary.Module)
    (limits : runtime.compiler.CompileLimits) (valid : Compiler.ValidCompilationSource bytes raw)
    (eligible : Compiler.InternalCompileEligible bytes raw limits bound) :
    ∃ executable, runtime.compiler.compile_with ops bytes limits = .ok (.Ok executable) ∧
      CompilationCertificate bytes executable := by
  obtain ⟨executable,compiled⟩ := Compiler.compile_with_available ops law bound allocation bytes raw limits valid eligible
  exact ⟨executable,compiled,compile_accepted_certificate ops law bytes limits executable compiled⟩

end Itasca.Integration

end

namespace Itasca.Integration
open Aeneas Aeneas.Std

/-- Forget private emission certificates while retaining the full source and
metadata association that public clients use. -/
theorem CompilationCertificate.source {bytes : Slice U8} {executable : runtime.compiler.ExecutableModule}
    (certificate : CompilationCertificate bytes executable) : CompilationSource bytes executable := by
  obtain ⟨raw, encoded, elaborated, typed, restrictions, relation⟩ := certificate
  exact ⟨raw, Binary.Source.moduleEncoding encoded, elaborated, typed, restrictions, relation.metadata, relation.accessors⟩

end Itasca.Integration

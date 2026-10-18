import Exec.Theorems.Composition.Certified.CertifiedSupportedCode
import Exec.Theorems.Composition.Certified.CertifiedSupportedSegments
import Exec.Interp.StructuredMachine.ExecutableFunctionHeads
import Exec.Abs.Executable
namespace Exec.Theorems
/-- Complete-profile static execution evidence, including indexed branch tables. -/
abbrev CertifiedExecutableStore {M : Type} := @CertifiedSupportedStore Interp.Executable.emission Abs.ExecutableInstr M
end Exec.Theorems

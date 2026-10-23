import Exec.Theorems.Composition.Certified.CertifiedSupportedCode
import Exec.Theorems.Composition.Certified.CertifiedSupportedSegments
import Exec.Interp.StructuredMachine.StatefulProjection
import Exec.Interp.StructuredMachine.SupportedHeadCoverage
import Exec.Interp.StructuredMachine.SimdPoint
import Exec.Interp.StructuredMachine.IndirectPoint
import Exec.Abs.BinaryInstr
namespace Exec.Theorems
/-- Complete-profile static execution evidence, including indexed branch tables. -/
abbrev CertifiedExecutableStore {M : Type} := @CertifiedSupportedStore M
end Exec.Theorems

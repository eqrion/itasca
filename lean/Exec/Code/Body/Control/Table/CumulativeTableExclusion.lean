import Exec.Code.Local.Control.Table.StructuredCodeTableExclusion
import Exec.Code.Body.Lowering.Simd.SimdEmissionExclusion
import Exec.Code.Local.Relations.Common.StatefulEmission
namespace Exec.Code
open Aeneas.Std

theorem StatefulEmission.not_branchTable {pairs C before instruction emitted after}
    (h : StatefulEmission pairs C before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  cases h with
  | instruction stack input output op => cases op <;> simp [Abs.Stateful.Instruction.source]

theorem SimdEmission.not_branchTable {immediates constants C before instruction emitted after}
    (h : SimdEmission immediates constants C before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  intro same
  have tag := h.allowed.source_tag
  simp only [same,Abs.simdSourceTag] at tag
  contradiction

end Exec.Code

import Exec.Code.Local.Control.Table.StructuredCodeTableExclusion
import Exec.Code.Body.Lowering.Simd.SimdEmissionExclusion
namespace Exec.Code
open Aeneas.Std

theorem StatefulEmission.not_branchTable {pairs C before instruction emitted after}
    (h : StatefulEmission pairs C before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  cases h with
  | instruction stack input output op => cases op <;> simp [Abs.Stateful.Instruction.source]

theorem CumulativeEmission.not_branchTable {pairs C before instruction emitted after}
    (h : CumulativeEmission pairs C before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  cases h with
  | left h => exact h.not_branchTable depths fallback
  | right h => exact h.not_branchTable depths fallback
  | indirect h => cases h; simp

theorem SimdEmission.not_branchTable {immediates constants C before instruction emitted after}
    (h : SimdEmission immediates constants C before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  intro same
  have tag := h.allowed.source_tag
  simp only [same,Abs.simdSourceTag] at tag
  contradiction

theorem SimdCumulativeEmission.not_branchTable {tables C before instruction emitted after}
    (h : SimdCumulativeEmission tables C before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  cases h with
  | left h => exact h.not_branchTable depths fallback
  | right h => exact h.not_branchTable depths fallback
end Exec.Code

import Exec.Abs.Simd.Exclusion
import Exec.Code.Body.Lowering.Simd.SimdCumulativeEmission
import Exec.Code.Local.Lowering.Simd.SimdSourceSignature
namespace Exec.Code

theorem LinearEmission.simd_tag {locals before source emitted after}
    (head : LinearEmission locals before source emitted after) : Abs.simdSourceTag source = false := by
  cases head with
  | binary stack ty op => cases op <;> rfl
  | numeric stack op => cases op <;> rfl
  | _ => rfl

theorem CoreEmission.simd_tag {C before source emitted after}
    (head : CoreEmission C before source emitted after) : Abs.simdSourceTag source = false := by
  cases head with
  | pure head => exact head.simd_tag
  | load stack op => cases op <;> rfl
  | store stack op => cases op <;> rfl
  | _ => rfl

theorem FloatCoreEmission.simd_tag {C before source emitted after}
    (head : FloatCoreEmission C before source emitted after) : Abs.simdSourceTag source = false := by
  cases head with
  | core head => exact head.simd_tag
  | scalar stack op => cases op <;> rfl

theorem CumulativeEmission.simd_tag {pairs C before source emitted after}
    (head : CumulativeEmission pairs C before source emitted after) : Abs.simdSourceTag source = false := by
  cases head with
  | left head => exact head.simd_tag
  | right head => cases head with
    | instruction stack input output op => cases op <;> rfl
  | indirect head => cases head; rfl

theorem SimdCumulativeEmission.simd {tables C before source emitted after}
    (allowed : Abs.SimdInstr source)
    (head : SimdCumulativeEmission tables C before source emitted after) :
    SimdEmission tables.simd tables.constants C before source emitted after := by
  cases head with
  | right head => exact head
  | left head => have := allowed.source_tag.symm.trans head.simd_tag; contradiction

theorem SimdCumulativeEmission.cumulative {tables C before source emitted after}
    (allowed : Abs.CumulativeInstr source)
    (head : SimdCumulativeEmission tables C before source emitted after) :
    CumulativeEmission tables.indirect C before source emitted after := by
  cases head with
  | left head => exact head
  | right head => exact False.elim (head.allowed.not_cumulative allowed)
end Exec.Code

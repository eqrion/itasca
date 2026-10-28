import Exec.Abs.Simd.Exclusion
import Exec.Code.Local.Relations.Common.ScalarEmission
import Exec.Code.Local.Lowering.Simd.SimdSourceSignature
namespace Itasca.Runtime.Code

theorem LinearEmission.simd_tag {locals before source emitted after}
    (head : LinearEmission locals before source emitted after) : Abs.simdSourceTag source = false := by
  cases head with
  | binary stack ty op => cases op <;> rfl
  | numeric stack op => cases op <;> rfl
  | _ => rfl

theorem ScalarEmission.simd_tag {C before source emitted after}
    (head : ScalarEmission C before source emitted after) : Abs.simdSourceTag source = false := by
  cases head with
  | linear head => exact head.simd_tag
  | load stack op => cases op <;> rfl
  | store stack op => cases op <;> rfl
  | float stack op => cases op <;> rfl
  | _ => rfl
end Itasca.Runtime.Code

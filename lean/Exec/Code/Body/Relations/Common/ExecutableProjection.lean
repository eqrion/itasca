import Exec.Code.Body.Relations.Common.ExecutableEmission
import Exec.Code.Body.Lowering.Simd.SimdEmissionExclusion
import Exec.Abs.ExecutableExclusion
namespace Itasca.Runtime.Code
open Aeneas.Std

theorem LinearEmission.executable_extension_tag {locals before source emitted after}
    (head : LinearEmission locals before source emitted after) : Abs.executableExtensionTag source = false := by
  cases head with
  | binary stack ty op => cases op <;> rfl
  | numeric stack op => cases op with
    | conversion op => cases op <;> rfl
    | _ => rfl
  | _ => rfl

theorem ScalarEmission.executable_extension_tag {C before source emitted after}
    (head : ScalarEmission C before source emitted after) : Abs.executableExtensionTag source = false := by
  cases head with
  | linear h => exact h.executable_extension_tag
  | float stack op => cases op <;> rfl
  | _ => rfl

theorem ExecutableEmission.typed_select_inv {tables C before declared emitted after}
    (head : ExecutableEmission tables C before (.SELECT (some declared)) emitted after) :
    TypedSelectEmission C before (.SELECT (some declared)) emitted after := by
  generalize equal : instr.SELECT (some declared) = source at head
  cases head with
  | scalar h => have tag := h.executable_extension_tag; rw [← equal] at tag; cases tag
  | stateful h => cases h with
    | instruction stack input output op => cases op <;> cases equal
  | indirect h => cases h; cases equal
  | simd h => have tag := h.allowed.executable_extension_tag; rw [← equal] at tag; cases tag
  | typedSelect h => subst equal; exact h
  | branchTable => cases equal

end Itasca.Runtime.Code

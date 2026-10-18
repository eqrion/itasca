import Exec.Code.Body.Relations.Common.ExecutableEmission
import Exec.Code.Body.Lowering.Simd.SimdEmissionExclusion
import Exec.Abs.ExecutableExclusion
namespace Exec.Code
open Aeneas.Std

theorem LinearEmission.executable_extension_tag {locals before source emitted after}
    (head : LinearEmission locals before source emitted after) : Abs.executableExtensionTag source = false := by
  cases head with
  | binary stack ty op => cases op <;> rfl
  | numeric stack op => cases op with
    | conversion op => cases op <;> rfl
    | _ => rfl
  | _ => rfl

theorem CoreEmission.executable_extension_tag {C before source emitted after}
    (head : CoreEmission C before source emitted after) : Abs.executableExtensionTag source = false := by
  cases head with
  | pure h => exact h.executable_extension_tag
  | _ => rfl

theorem FloatCoreEmission.executable_extension_tag {C before source emitted after}
    (head : FloatCoreEmission C before source emitted after) : Abs.executableExtensionTag source = false := by
  cases head with
  | core h => exact h.executable_extension_tag
  | scalar stack op => cases op <;> rfl

theorem CumulativeEmission.executable_extension_tag {pairs C before source emitted after}
    (head : CumulativeEmission pairs C before source emitted after) : Abs.executableExtensionTag source = false := by
  cases head with
  | left h => exact h.executable_extension_tag
  | right h => cases h with
    | instruction stack input output op => cases op <;> rfl
  | indirect h => cases h; rfl

theorem SimdCumulativeEmission.executable_extension_tag {tables C before source emitted after}
    (head : SimdCumulativeEmission tables C before source emitted after) : Abs.executableExtensionTag source = false := by
  cases head with
  | left h => exact h.executable_extension_tag
  | right h => exact h.allowed.executable_extension_tag

/-- Unrelated source families retain their original exact emission certificate. -/
theorem ExecutableEmission.base_inv {tables C before source emitted after}
    (head : ExecutableEmission tables C before source emitted after)
    (ordinary : Abs.executableExtensionTag source = false) :
    SimdCumulativeEmission tables C before source emitted after := by
  cases head with
  | base h => exact h
  | typedSelect h => cases h; cases ordinary
  | branchTable => cases ordinary

theorem ExecutableEmission.typed_select_inv {tables C before declared emitted after}
    (head : ExecutableEmission tables C before (.SELECT (some declared)) emitted after) :
    TypedSelectEmission C before (.SELECT (some declared)) emitted after := by
  cases head with
  | base h => have impossible := h.executable_extension_tag; cases impossible
  | typedSelect h => exact h

/-- A branch-table gate contains its exact header and selector stack shape;
target correctness is retained separately by the structural layout. -/
theorem ExecutableEmission.branch_table_inv {tables C before depths fallback emitted after}
    (head : ExecutableEmission tables C before (.BR_TABLE depths fallback) emitted after) :
    ∃ selector start len, before = after ++ [.I32] ∧ emitted = [.JumpTable selector start len] := by
  cases head with
  | base h => have impossible := h.executable_extension_tag; cases impossible
  | typedSelect h => cases h
  | branchTable stack depths fallback selector start len => exact ⟨selector,start,len,rfl,rfl⟩
end Exec.Code

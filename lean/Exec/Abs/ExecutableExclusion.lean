import Exec.Abs.Executable
import Exec.Abs.Simd.Exclusion
namespace Exec.Abs

/-- The two source heads added after the scalar/stateful/SIMD union. -/
def executableExtensionTag : instr → Bool
  | .SELECT (some _) | .BR_TABLE .. => true
  | _ => false

theorem SliceInstr.executable_extension_tag {source} (allowed : SliceInstr source) :
    executableExtensionTag source = false := by
  cases allowed with
  | numeric op => cases op with
    | conversion op => cases op <;> rfl
    | _ => rfl
  | _ => rfl

theorem CoreInstr.executable_extension_tag {source} (allowed : CoreInstr source) :
    executableExtensionTag source = false := by
  cases allowed with
  | slice h => exact h.executable_extension_tag
  | _ => rfl

theorem FloatCoreInstr.executable_extension_tag {source} (allowed : FloatCoreInstr source) :
    executableExtensionTag source = false := by
  cases allowed with
  | core h => exact h.executable_extension_tag
  | scalar op => cases op <;> rfl
  | _ => rfl

theorem CumulativeInstr.executable_extension_tag {source} (allowed : CumulativeInstr source) :
    executableExtensionTag source = false := by
  cases allowed with
  | core h => exact h.executable_extension_tag
  | stateful op => cases op <;> rfl
  | _ => rfl

theorem SimdInstr.executable_extension_tag {source} (allowed : SimdInstr source) :
    executableExtensionTag source = false := by
  have tag := allowed.source_tag
  cases source <;> simp_all [executableExtensionTag,simdSourceTag]

theorem SimdCumulativeInstr.executable_extension_tag {source} (allowed : SimdCumulativeInstr source) :
    executableExtensionTag source = false := by
  cases allowed with
  | cumulative h => exact h.executable_extension_tag
  | simd h => exact h.executable_extension_tag
  | _ => rfl
end Exec.Abs

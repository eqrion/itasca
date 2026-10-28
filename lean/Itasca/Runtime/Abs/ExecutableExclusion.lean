import Itasca.Runtime.Abs.BinaryInstr
import Itasca.Runtime.Abs.Simd.Exclusion
namespace Itasca.Runtime.Abs

/-- The two source heads added after the scalar/stateful/SIMD union. -/
def executableExtensionTag : instr → Bool
  | .SELECT (some _) | .BR_TABLE .. => true
  | _ => false

theorem PureHead.executable_extension_tag {source} (allowed : PureHead source) :
    executableExtensionTag source = false := by
  cases allowed with
  | numeric op => cases op with
    | conversion op => cases op <;> rfl
    | _ => rfl
  | _ => rfl

theorem CoreHead.executable_extension_tag {source} (allowed : CoreHead source) :
    executableExtensionTag source = false := by
  cases allowed with
  | pure h => exact h.executable_extension_tag
  | _ => rfl

theorem ScalarHead.executable_extension_tag {source} (allowed : ScalarHead source) :
    executableExtensionTag source = false := by
  cases allowed with
  | core h => exact h.executable_extension_tag
  | float op => cases op <;> rfl

theorem SimdInstr.executable_extension_tag {source} (allowed : SimdInstr source) :
    executableExtensionTag source = false := by
  have tag := allowed.source_tag
  cases source <;> simp_all [executableExtensionTag,simdSourceTag]

end Itasca.Runtime.Abs

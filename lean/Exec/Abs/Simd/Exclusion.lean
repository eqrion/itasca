import Exec.Abs.Simd.Source
import Exec.Abs.Core
namespace Exec.Abs

/-- Source constructor tag used only to separate scalar/reference/control
heads from SIMD heads in cumulative syntactic certificates. -/
def simdSourceTag : instr → Bool
  | .VCONST _ _ | .VVUNOP _ _ | .VVBINOP _ _ | .VVTERNOP _ _ | .VVTESTOP _ _
  | .VUNOP _ _ | .VBINOP _ _ | .VTESTOP _ _ | .VRELOP _ _ | .VSHIFTOP _ _
  | .VBITMASK _ | .VSWIZZLE _ | .VSHUFFLE _ _ | .VSPLAT _ | .VEXTRACT_LANE _ _ _
  | .VREPLACE_LANE _ _ | .VEXTUNOP _ _ _ | .VEXTBINOP _ _ _ | .VNARROW _ _ _
  | .VCVTOP _ _ _ | .VLOAD _ _ _ | .VLOAD_LANE _ _ _ _ | .VSTORE _ _ | .VSTORE_LANE _ _ _ _ => true
  | _ => false

theorem SimdInstr.source_tag {source} (allowed : SimdInstr source) : simdSourceTag source = true := by
  cases allowed with
  | pure signature => cases signature <;> rfl
  | memory signature => cases signature <;> rfl
  | constant => rfl

theorem PureHead.simd_tag {source} (allowed : PureHead source) : simdSourceTag source = false := by
  cases allowed with
  | numeric op => cases op <;> rfl
  | _ => rfl

theorem CoreHead.simd_tag {source} (allowed : CoreHead source) : simdSourceTag source = false := by
  cases allowed with
  | pure old => exact old.simd_tag
  | load op arg => cases op <;> rfl
  | store op arg => cases op <;> rfl
  | _ => rfl

theorem ScalarHead.simd_tag {source} (allowed : ScalarHead source) : simdSourceTag source = false := by
  cases allowed with
  | core old => exact old.simd_tag
  | float op => cases op <;> rfl

end Exec.Abs

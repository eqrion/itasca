import Exec.Abs.Simd.Source
import Exec.Abs.Cumulative
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

theorem SliceInstr.simd_tag {source} (allowed : SliceInstr source) : simdSourceTag source = false := by
  cases allowed with
  | numeric op => cases op <;> rfl
  | _ => rfl

theorem CoreInstr.simd_tag {source} (allowed : CoreInstr source) : simdSourceTag source = false := by
  cases allowed with
  | slice old => exact old.simd_tag
  | load op arg => cases op <;> rfl
  | store op arg => cases op <;> rfl
  | _ => rfl

theorem FloatCoreInstr.simd_tag {source} (allowed : FloatCoreInstr source) : simdSourceTag source = false := by
  cases allowed with
  | core old => exact old.simd_tag
  | scalar op => cases op <;> rfl
  | _ => rfl

theorem CumulativeInstr.simd_tag {source} (allowed : CumulativeInstr source) : simdSourceTag source = false := by
  cases allowed with
  | core old => exact old.simd_tag
  | stateful op => cases op <;> rfl
  | _ => rfl

theorem SimdInstr.not_cumulative {source} (allowed : SimdInstr source) : ¬ CumulativeInstr source := by
  intro old
  have := allowed.source_tag.symm.trans old.simd_tag
  contradiction
end Exec.Abs

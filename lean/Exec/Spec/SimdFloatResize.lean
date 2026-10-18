import Exec.Spec.SimdFloatUnaryChoices
import Exec.Spec.FloatPromote
import Exec.Spec.FloatConvert
namespace Exec.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

inductive FloatResize where | demote | promote

def FloatResize.input : FloatResize → Fnn | .demote => .F64 | .promote => .F32

def FloatResize.output : FloatResize → Fnn | .demote => .F32 | .promote => .F64

def floatResizeChoices : FloatResize → fN → List fN
  | .demote,a => demote__ 64 32 a
  | .promote,a => promote__ 32 64 a

def floatResizeSource (kind : FloatResize) : vcvtop__ :=
  match kind with
  | .demote => .mk_vcvtop___3 .F64 2 .F32 4 (.DEMOTE .ZERO)
  | .promote => .mk_vcvtop___3 .F32 4 .F64 2 .PROMOTELOW

theorem float_resize_source_wf (kind : FloatResize) :
    wf_vcvtop__ (shapeOf (lanetype_Fnn kind.input)) (shapeOf (lanetype_Fnn kind.output)) (floatResizeSource kind) := by
  cases kind <;> apply wf_vcvtop__.vcvtop___case_3
  · exact .vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 _ _ _ _ _ (by decide)
  · rfl
  · rfl
  · exact .vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1 _ _ _ _ (by decide)
  · rfl
  · rfl

end Exec.Spec.Simd

import Itasca.Runtime.Spec.SimdFloatUnaryChoices
import Itasca.Runtime.Spec.FloatMinMax
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def floatBinaryChoices (width : Nat) (op : vbinop_Fnn_N) (a b : fN) : List fN :=
  match op with
  | .ADD => fadd_ width a b
  | .SUB => fsub_ width a b
  | .MUL => fmul_ width a b
  | .DIV => fdiv_ width a b
  | .MIN => fmin_ width a b
  | .MAX => fmax_ width a b
  | .PMIN => fpmin_ width a b
  | .PMAX => fpmax_ width a b

def floatBinarySource (ty : Fnn) (op : vbinop_Fnn_N) : vbinop_ :=
  .mk_vbinop__1 ty (128/lsize (lanetype_Fnn ty)) op

theorem float_binary_source_wf (ty : Fnn) (op : vbinop_Fnn_N) :
    wf_vbinop_ (shapeOf (lanetype_Fnn ty)) (floatBinarySource ty op) := by
  cases ty <;> cases op <;> constructor <;> constructor

theorem float_binary_choices_wf (width : Nat) (supported : width = 32 ∨ width = 64)
    (op : vbinop_Fnn_N) (a b : fN) (firstWf : wf_fN width a) (secondWf : wf_fN width b) :
    Forall (wf_fN width) (floatBinaryChoices width op a b) := by
  cases op with
  | ADD => exact add_wf width supported a b firstWf secondWf
  | SUB => exact sub_wf width supported a b firstWf secondWf
  | MUL => exact mul_wf width supported a b
  | DIV => exact div_wf width supported a b
  | MIN => exact float_min_wf width supported a b firstWf secondWf
  | MAX => exact float_max_wf width supported a b firstWf secondWf
  | PMIN =>
    intro result member
    simp only [floatBinaryChoices,fpmin_,List.mem_singleton] at member
    subst result
    split <;> assumption
  | PMAX =>
    intro result member
    simp only [floatBinaryChoices,fpmax_,List.mem_singleton] at member
    subst result
    split <;> assumption

end Itasca.Runtime.Spec.Simd

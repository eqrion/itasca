import Itasca.Runtime.Spec.SimdCompareFloatLists
import SpecExt.Builtins.Float.Wf
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def floatUnaryChoices (width : Nat) (op : vunop_Fnn_N) (a : fN) : List fN :=
  match op with
  | .ABS => fabs_ width a
  | .NEG => fneg_ width a
  | .SQRT => fsqrt_ width a
  | .CEIL => fceil_ width a
  | .FLOOR => ffloor_ width a
  | .TRUNC => ftrunc_ width a
  | .NEAREST => fnearest_ width a

def floatUnarySource (ty : Fnn) (op : vunop_Fnn_N) : vunop_ :=
  .mk_vunop__1 ty (128/lsize (lanetype_Fnn ty)) op

theorem float_unary_source_wf (ty : Fnn) (op : vunop_Fnn_N) :
    wf_vunop_ (shapeOf (lanetype_Fnn ty)) (floatUnarySource ty op) := by
  cases ty <;> cases op <;> constructor <;> constructor

theorem float_unary_choices_wf (width : Nat) (supported : width = 32 ∨ width = 64)
    (op : vunop_Fnn_N) (a : fN) (inputWf : wf_fN width a) :
    Forall (wf_fN width) (floatUnaryChoices width op a) := by
  cases op with
  | ABS =>
    intro result member
    simp only [floatUnaryChoices,fabs_,List.mem_singleton] at member
    subst result
    exact withSign_wf (magnitude_wf inputWf) false
  | NEG =>
    intro result member
    simp only [floatUnaryChoices,fneg_,List.mem_singleton] at member
    subst result
    exact withSign_wf (magnitude_wf inputWf) _
  | SQRT => exact sqrt_wf width supported a inputWf
  | CEIL => exact integral_wf width supported _ a inputWf
  | FLOOR => exact integral_wf width supported _ a inputWf
  | TRUNC => exact integral_wf width supported _ a inputWf
  | NEAREST => exact integral_wf width supported _ a inputWf

end Itasca.Runtime.Spec.Simd

import Exec.Spec.SimdShape
import Exec.Spec.SimdCompareInteger
namespace Itasca.Runtime.Spec.Simd

def integerCompareSupported (ty : Jnn) (op : vrelop_Jnn_N) : Prop :=
  match ty,op with
  | .I64,.LT .U | .I64,.GT .U | .I64,.LE .U | .I64,.GE .U => False
  | _,_ => True

def integerCompareSource (ty : Jnn) (op : vrelop_Jnn_N) : vrelop_ :=
  .mk_vrelop__0 ty (128/lsize (lanetype_Jnn ty)) op

theorem integerCompareSource_wf (ty : Jnn) (op : vrelop_Jnn_N)
    (supported : integerCompareSupported ty op) :
    wf_vrelop_ (shapeOf (lanetype_Jnn ty)) (integerCompareSource ty op) := by
  apply wf_vrelop_.vrelop__case_0 _ _ _ _ ?_ rfl
  cases op with
  | EQ => constructor
  | NE => constructor
  | LT sign | GT sign | LE sign | GE sign =>
    constructor
    cases ty <;> cases sign <;> simp_all [integerCompareSupported,lsizenn,lsize,size,psize,lanetype_Jnn,isize,valtype_numtype]

end Itasca.Runtime.Spec.Simd

import Exec.Spec.SimdCompareMasks
import SpecExt.Builtins.Float.RawCompare
namespace Exec.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def floatComparisonBool (width : Nat) (op : vrelop_Fnn_N) (a b : fN) : Bool :=
  match op with
  | .EQ => equal width a b
  | .NE => !equal width a b
  | .LT => less width a b
  | .GT => less width b a
  | .LE => less width a b || equal width a b
  | .GE => less width b a || equal width b a

def floatComparisonValue (width : Nat) (op : vrelop_Fnn_N) (a b : fN) : uN :=
  match op with
  | .EQ => feq_ width a b
  | .NE => fne_ width a b
  | .LT => flt_ width a b
  | .GT => fgt_ width a b
  | .LE => fle_ width a b
  | .GE => fge_ width a b

theorem float_comparison_value (width : Nat) (op : vrelop_Fnn_N) (a b : fN) :
    floatComparisonValue width op a b = .mk_uN (nat_of_bool (floatComparisonBool width op a b)) := by
  cases op
  · cases h : equal width a b <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
  · cases h : equal width a b <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
  · cases h : less width a b <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
  · cases h : less width b a <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
  · cases h : less width a b || equal width a b <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
  · cases h : less width b a || equal width b a <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]

def floatCompareSource (ty : Fnn) (op : vrelop_Fnn_N) : vrelop_ :=
  .mk_vrelop__1 ty (128/lsize (lanetype_Fnn ty)) op

def floatCompareInteger (ty : Fnn) : Inn := match ty with | .F32 => .I32 | .F64 => .I64

theorem floatCompareSource_wf (ty : Fnn) (op : vrelop_Fnn_N) :
    wf_vrelop_ (shapeOf (lanetype_Fnn ty)) (floatCompareSource ty op) := by
  cases ty <;> cases op <;> constructor <;> constructor <;>
    simp_all [lsizenn,lsize,size,psize,lanetype_Fnn,valtype_numtype]

end Exec.Spec.Simd

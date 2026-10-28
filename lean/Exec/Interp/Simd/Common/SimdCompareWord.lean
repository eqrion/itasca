import Exec.Interp.Simd.Integer.SimdCompareSigned
import Exec.Spec.SimdCompareInteger
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def integerCompareIndex (op : vrelop_Jnn_N) : U16 :=
  match op with
  | .EQ => 0#u16 | .NE => 1#u16
  | .LT .S => 2#u16 | .LT .U => 3#u16
  | .GT .S => 4#u16 | .GT .U => 5#u16
  | .LE .S => 6#u16 | .LE .U => 7#u16
  | .GE .S => 8#u16 | .GE .U => 9#u16

@[step] theorem integer_compare_word (op : vrelop_Jnn_N) (a b : U64) (width : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (aBound : a.val < 2^width.val) (bBound : b.val < 2^width.val) :
    runtime.interp.int.compare_int (integerCompareIndex op) a b width ⦃ result =>
      result = Spec.Simd.integerLaneCompare op (a.bv.setWidth width.val) (b.bv.setWidth width.val) ⦄ := by
  have aValue : (a.bv.setWidth width.val).toNat = a.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt aBound
  have bValue : (b.bv.setWidth width.val).toNat = b.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt bBound
  cases op with
  | EQ => simpa only [integerCompareIndex,Spec.Simd.integerLaneCompare,aValue,bValue] using
      Itasca.Runtime.Interp.compare_int_eq a b width positive widthBound
  | NE => simpa only [integerCompareIndex,Spec.Simd.integerLaneCompare,aValue,bValue] using
      Itasca.Runtime.Interp.compare_int_ne a b width positive widthBound
  | LT sign => cases sign with
    | S => exact compare_int_lts a b width positive widthBound
    | U => simpa only [integerCompareIndex,Spec.Simd.integerLaneCompare,aValue,bValue] using
        Itasca.Runtime.Interp.compare_int_ltu a b width positive widthBound
  | GT sign => cases sign with
    | S => exact compare_int_gts a b width positive widthBound
    | U => simpa only [integerCompareIndex,Spec.Simd.integerLaneCompare,aValue,bValue] using
        Itasca.Runtime.Interp.compare_int_gtu a b width positive widthBound
  | LE sign => cases sign with
    | S => exact compare_int_les a b width positive widthBound
    | U => simpa only [integerCompareIndex,Spec.Simd.integerLaneCompare,aValue,bValue] using
        Itasca.Runtime.Interp.compare_int_leu a b width positive widthBound
  | GE sign => cases sign with
    | S => exact compare_int_ges a b width positive widthBound
    | U => simpa only [integerCompareIndex,Spec.Simd.integerLaneCompare,aValue,bValue] using
        Itasca.Runtime.Interp.compare_int_geu a b width positive widthBound

end Itasca.Runtime.Interp.Simd

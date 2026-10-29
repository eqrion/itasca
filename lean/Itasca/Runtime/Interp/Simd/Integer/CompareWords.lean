import Itasca.Runtime.Interp.Simd.Integer.CompareSigned
import Itasca.Runtime.Spec.Simd.CompareInteger

/-!
Integer lane comparison word calculations and opcode dispatch, shared by lane comparison and wrapping arithmetic.
-/

/-! ## Simd Compare Word -/

section

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

end

/-! ## Simd Compare Dispatch -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def integerCompareWidth (ty : Jnn) : U32 :=
  match ty with
  | .I8 => 8#u32 | .I16 => 16#u32 | .I32 => 32#u32 | .I64 => 64#u32

def integerCompareOpcode (ty : Jnn) (op : vrelop_Jnn_N) : U32 :=
  match ty,op with
  | .I8,.EQ => 35#u32
  | .I8,.NE => 36#u32
  | .I8,.LT .S => 37#u32
  | .I8,.LT .U => 38#u32
  | .I8,.GT .S => 39#u32
  | .I8,.GT .U => 40#u32
  | .I8,.LE .S => 41#u32
  | .I8,.LE .U => 42#u32
  | .I8,.GE .S => 43#u32
  | .I8,.GE .U => 44#u32
  | .I16,.EQ => 45#u32
  | .I16,.NE => 46#u32
  | .I16,.LT .S => 47#u32
  | .I16,.LT .U => 48#u32
  | .I16,.GT .S => 49#u32
  | .I16,.GT .U => 50#u32
  | .I16,.LE .S => 51#u32
  | .I16,.LE .U => 52#u32
  | .I16,.GE .S => 53#u32
  | .I16,.GE .U => 54#u32
  | .I32,.EQ => 55#u32
  | .I32,.NE => 56#u32
  | .I32,.LT .S => 57#u32
  | .I32,.LT .U => 58#u32
  | .I32,.GT .S => 59#u32
  | .I32,.GT .U => 60#u32
  | .I32,.LE .S => 61#u32
  | .I32,.LE .U => 62#u32
  | .I32,.GE .S => 63#u32
  | .I32,.GE .U => 64#u32
  | .I64,.EQ => 214#u32
  | .I64,.NE => 215#u32
  | .I64,.LT _ => 216#u32
  | .I64,.GT _ => 217#u32
  | .I64,.LE _ => 218#u32
  | .I64,.GE _ => 219#u32

theorem integerCompareWidth_val (ty : Jnn) :
    (integerCompareWidth ty).val = lsize (lanetype_Jnn ty) := by cases ty <;> rfl

theorem integerCompareIndex_roundtrip (op : vrelop_Jnn_N) :
    UScalar.cast .U16 (UScalar.cast .U32 (integerCompareIndex op)) = integerCompareIndex op := by
  cases op <;> (try rename_i sign; cases sign) <;> rfl

theorem integer_compare_dispatch_eq (ty : Jnn) (op : vrelop_Jnn_N) (x y : U128)
    (supported : Spec.Simd.integerCompareSupported ty op) :
    runtime.interp.simd.compare_lanes (integerCompareOpcode ty op) x y =
      (runtime.interp.simd.compare_lanes_loop x y (integerCompareWidth ty)
        (UScalar.cast .U32 (integerCompareIndex op)) false 0#u128 0#u32) := by
  cases ty <;> cases op <;> (try rename_i sign; cases sign)
  all_goals simp only [Spec.Simd.integerCompareSupported] at supported
  all_goals try contradiction
  all_goals unfold runtime.interp.simd.compare_lanes integerCompareOpcode integerCompareWidth integerCompareIndex
  all_goals with_unfolding_all change (Aeneas.Std.bind (Aeneas.Std.bind (Result.ok _) _) _) = _
  all_goals simp only [bind_ok]
  all_goals rfl

end Itasca.Runtime.Interp.Simd

end

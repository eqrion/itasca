import Exec.Interp.Simd.Common.SimdCompareWord
import Exec.Spec.SimdCompareShape
namespace Exec.Interp.Simd
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

end Exec.Interp.Simd

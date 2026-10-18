import Exec.Interp.Simd.Float.SimdCompareFloatWord
import Exec.Interp.Simd.Common.SimdCompareLoop
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Exec.Spec.Simd

def floatCompareOpcode (ty : Fnn) (op : vrelop_Fnn_N) : U32 :=
  match ty,op with
  | .F32,.EQ => 65#u32
  | .F32,.NE => 66#u32
  | .F32,.LT => 67#u32
  | .F32,.GT => 68#u32
  | .F32,.LE => 69#u32
  | .F32,.GE => 70#u32
  | .F64,.EQ => 71#u32
  | .F64,.NE => 72#u32
  | .F64,.LT => 73#u32
  | .F64,.GT => 74#u32
  | .F64,.LE => 75#u32
  | .F64,.GE => 76#u32

theorem floatCompareIndex_roundtrip (op : vrelop_Fnn_N) :
    UScalar.cast .U16 (UScalar.cast .U32 (floatCompareIndex op)) = floatCompareIndex op := by
  cases op <;> rfl

def floatLanePredicate (ty : Fnn) (op : vrelop_Fnn_N) (x y : BitVec 128) (j : Nat) : Bool :=
  floatComparisonBool (lsize (lanetype_Fnn ty)) op
    (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x).toNat)
    (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j y).toNat)

theorem float_compare_loop (ty : Fnn) (op : vrelop_Fnn_N) (x y : U128) :
    runtime.interp.simd.compare_lanes_loop y x (floatCompareWidth ty)
      (UScalar.cast .U32 (floatCompareIndex op)) true 0#u128 0#u32
      ⦃ result => ∀ j, j < 128/lsize (lanetype_Fnn ty) →
        laneBits (lsize (lanetype_Fnn ty)) j result.bv =
          comparisonBits (lsize (lanetype_Fnn ty)) (floatLanePredicate ty op x.bv y.bv j) ⦄ := by
  have widthEq := floatCompareWidth_val ty
  rw [←widthEq]
  apply comparison_loop x y 0#u128 (floatCompareWidth ty) (UScalar.cast .U32 (floatCompareIndex op))
    0#u32 true (by cases ty <;> decide) (by cases ty <;> decide)
    (floatLanePredicate ty op x.bv y.bv)
  · intro j valid a b aEq bEq
    simp only [if_true,floatCompareIndex_roundtrip]
    rw [widthEq] at aEq bEq
    have aBound : a.val < 2^lsize (lanetype_Fnn ty) := by rw [aEq]; exact BitVec.isLt _
    have bBound : b.val < 2^lsize (lanetype_Fnn ty) := by rw [bEq]; exact BitVec.isLt _
    simpa only [floatLanePredicate,aEq,bEq] using float_compare_word ty op a b aBound bBound
  · simp
  · simp
  · intro j after valid
    change ((0 : BitVec 128) >>> ((floatCompareWidth ty).val*j)).setWidth _ = 0
    simp

theorem float_compare_dispatch_eq (ty : Fnn) (op : vrelop_Fnn_N) (x y : U128) :
    runtime.interp.simd.compare_lanes (floatCompareOpcode ty op) x y =
      Aeneas.Std.bind (runtime.interp.simd.compare_lanes_loop y x (floatCompareWidth ty)
        (UScalar.cast .U32 (floatCompareIndex op)) true 0#u128 0#u32)
        runtime.interp.simd.vector := by
  cases ty <;> cases op
  all_goals unfold runtime.interp.simd.compare_lanes floatCompareOpcode floatCompareWidth floatCompareIndex
  all_goals with_unfolding_all change (Aeneas.Std.bind (Aeneas.Std.bind (Result.ok _) _) _) = _
  all_goals simp only [bind_ok]
  all_goals rfl

@[step] theorem float_compare_lanes (ty : Fnn) (op : vrelop_Fnn_N) (x y : U128) :
    runtime.interp.simd.compare_lanes (floatCompareOpcode ty op) x y ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Fnn ty) → laneBits (lsize (lanetype_Fnn ty)) j result.bv =
        comparisonBits (lsize (lanetype_Fnn ty)) (floatLanePredicate ty op x.bv y.bv j) ⦄ := by
  rw [float_compare_dispatch_eq]
  step with float_compare_loop ty op x y as ⟨result,lanes⟩
  simpa [runtime.interp.simd.vector] using lanes

end Exec.Interp.Simd

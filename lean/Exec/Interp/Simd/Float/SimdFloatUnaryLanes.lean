import Exec.Interp.Simd.Float.SimdFloatUnaryWord
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Exec.Spec.Simd Platform

def floatUnaryOpcode (ty : Fnn) (op : vunop_Fnn_N) : U32 :=
  match ty,op with
  | .F32,.ABS => 224#u32 | .F32,.NEG => 225#u32 | .F32,.SQRT => 227#u32
  | .F32,.CEIL => 103#u32 | .F32,.FLOOR => 104#u32 | .F32,.TRUNC => 105#u32 | .F32,.NEAREST => 106#u32
  | .F64,.ABS => 236#u32 | .F64,.NEG => 237#u32 | .F64,.SQRT => 239#u32
  | .F64,.CEIL => 116#u32 | .F64,.FLOOR => 117#u32 | .F64,.TRUNC => 122#u32 | .F64,.NEAREST => 148#u32

theorem float_unary_loop_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vunop_Fnn_N) (x : U128) :
    runtime.interp.simd.float_unary_lanes_loop floats (floatCompareWidth ty) (floatUnaryIndex op) x 0#u128 0#u32
      ⦃ result => ∀ j, j < 128/lsize (lanetype_Fnn ty) →
        floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j result.bv).toNat ∈
          floatUnaryChoices (lsize (lanetype_Fnn ty)) op
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat) ⦄ := by
  have widthEq := floatCompareWidth_val ty
  rw [←widthEq]
  apply float_unary_loop floats x 0#u128 (floatCompareWidth ty) (floatUnaryIndex op) 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => floatOfBits (floatCompareWidth ty).val bits.toNat ∈
      floatUnaryChoices (floatCompareWidth ty).val op
        (floatOfBits (floatCompareWidth ty).val (laneBits (floatCompareWidth ty).val j x.bv).toNat))
  · intro j valid a aEq
    rw [widthEq] at aEq ⊢
    have bound : a.val < 2^lsize (lanetype_Fnn ty) := by rw [aEq]; exact BitVec.isLt _
    simpa only [aEq] using float_unary_word floats laws ty op a bound
  · simp
  · simp

theorem float_unary_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (op : vunop_Fnn_N) (x : U128) :
    runtime.interp.simd.float_unary_lanes floats (floatUnaryOpcode ty op) x =
      Aeneas.Std.bind (runtime.interp.simd.float_unary_lanes_loop floats (floatCompareWidth ty)
        (floatUnaryIndex op) x 0#u128 0#u32) runtime.interp.simd.vector := by
  cases ty <;> cases op
  all_goals unfold runtime.interp.simd.float_unary_lanes floatUnaryOpcode floatCompareWidth floatUnaryIndex
  all_goals with_unfolding_all first
    | change (Aeneas.Std.bind (Result.ok _) _) = _
    | change (Aeneas.Std.bind (Aeneas.Std.bind (Result.ok _) _) _) = _
  all_goals simp only [bind_ok]
  all_goals rfl

@[step] theorem float_unary_lanes {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vunop_Fnn_N) (x : U128) :
    runtime.interp.simd.float_unary_lanes floats (floatUnaryOpcode ty op) x ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Fnn ty) →
        floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j result.bv).toNat ∈
          floatUnaryChoices (lsize (lanetype_Fnn ty)) op
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat) ⦄ := by
  rw [float_unary_dispatch_eq]
  step with float_unary_loop_sound floats laws ty op x as ⟨result,allowed⟩
  simpa [runtime.interp.simd.vector] using allowed

end Exec.Interp.Simd

import Exec.Interp.Simd.Float.SimdFloatBinaryPseudo
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Exec.Spec.Simd Platform

def floatBinaryOpcode (ty : Fnn) (op : vbinop_Fnn_N) : U32 :=
  match ty,op with
  | .F32,.ADD => 228#u32
  | .F32,.SUB => 229#u32
  | .F32,.MUL => 230#u32
  | .F32,.DIV => 231#u32
  | .F32,.MIN => 232#u32
  | .F32,.MAX => 233#u32
  | .F32,.PMIN => 234#u32
  | .F32,.PMAX => 235#u32
  | .F64,.ADD => 240#u32
  | .F64,.SUB => 241#u32
  | .F64,.MUL => 242#u32
  | .F64,.DIV => 243#u32
  | .F64,.MIN => 244#u32
  | .F64,.MAX => 245#u32
  | .F64,.PMIN => 246#u32
  | .F64,.PMAX => 247#u32

theorem float_binary_loop_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vbinop_Fnn_N) (x y : U128) :
    runtime.interp.simd.float_binary_lanes_loop floats (floatCompareWidth ty) (floatBinaryIndex op) y x 0#u128 0#u32
      ⦃ result => ∀ j, j < 128/lsize (lanetype_Fnn ty) →
        floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j result.bv).toNat ∈
          floatBinaryChoices (lsize (lanetype_Fnn ty)) op
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat)
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j y.bv).toNat) ⦄ := by
  have widthEq := floatCompareWidth_val ty
  rw [←widthEq]
  apply float_binary_loop floats x y 0#u128 (floatCompareWidth ty) (floatBinaryIndex op) 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => floatOfBits (floatCompareWidth ty).val bits.toNat ∈
      floatBinaryChoices (floatCompareWidth ty).val op
        (floatOfBits (floatCompareWidth ty).val (laneBits (floatCompareWidth ty).val j x.bv).toNat)
        (floatOfBits (floatCompareWidth ty).val (laneBits (floatCompareWidth ty).val j y.bv).toNat))
  · intro j valid a b aEq bEq
    rw [widthEq] at aEq bEq ⊢
    have bound : a.val < 2^lsize (lanetype_Fnn ty) := by rw [aEq]; exact BitVec.isLt _
    have secondBound : b.val < 2^lsize (lanetype_Fnn ty) := by rw [bEq]; exact BitVec.isLt _
    simpa only [aEq,bEq] using float_binary_word floats laws ty op a b bound secondBound
  · simp
  · simp

theorem float_binary_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (op : vbinop_Fnn_N) (x y : U128) :
    runtime.interp.simd.float_binary_lanes floats (floatBinaryOpcode ty op) x y =
      Aeneas.Std.bind (runtime.interp.simd.float_binary_lanes_loop floats (floatCompareWidth ty)
        (floatBinaryIndex op) y x 0#u128 0#u32) runtime.interp.simd.vector := by
  cases ty <;> cases op
  all_goals unfold runtime.interp.simd.float_binary_lanes floatBinaryOpcode floatCompareWidth floatBinaryIndex
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals rfl

@[step] theorem float_binary_lanes {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vbinop_Fnn_N) (x y : U128) :
    runtime.interp.simd.float_binary_lanes floats (floatBinaryOpcode ty op) x y ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Fnn ty) →
        floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j result.bv).toNat ∈
          floatBinaryChoices (lsize (lanetype_Fnn ty)) op
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat)
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j y.bv).toNat) ⦄ := by
  rw [float_binary_dispatch_eq]
  step with float_binary_loop_sound floats laws ty op x y as ⟨result,allowed⟩
  simpa [runtime.interp.simd.vector] using allowed

end Exec.Interp.Simd

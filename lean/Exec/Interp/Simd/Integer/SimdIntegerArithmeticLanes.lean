import Exec.Interp.Simd.Integer.SimdIntegerArithmeticWord
import Exec.Interp.Simd.Common.SimdCompareDispatch
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def integerArithmeticOpcode (ty : Jnn) (kind : IntegerArithmetic) : U32 :=
  match ty,kind with
  | .I8,.add => 110#u32 | .I8,.sub => 113#u32 | .I8,.mul => 117#u32
  | .I16,.add => 142#u32 | .I16,.sub => 145#u32 | .I16,.mul => 149#u32
  | .I32,.add => 174#u32 | .I32,.sub => 177#u32 | .I32,.mul => 181#u32
  | .I64,.add => 206#u32 | .I64,.sub => 209#u32 | .I64,.mul => 213#u32

theorem integerArithmeticOpcode_index (ty : Jnn) (kind : IntegerArithmetic) :
    (integerArithmeticOpcode ty kind).val%32 = (integerArithmeticIndex kind).val := by
  cases ty <;> cases kind <;> decide

theorem lane_word_cast (width j : Nat) (x : BitVec 128) (a : U64)
    (value : a.val = (laneBits width j x).toNat) : a.bv.setWidth width = laneBits width j x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth]
  change a.val%2^width = _
  rw [value,Nat.mod_eq_of_lt (BitVec.isLt _)]

theorem integer_arithmetic_loop (ty : Jnn) (kind : IntegerArithmetic) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes_loop (integerArithmeticOpcode ty kind) x
      y (integerCompareWidth ty) 0#u128 0#u32 ⦃ result => ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerArithmeticBits kind
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  have widthEq := integerCompareWidth_val ty
  rw [←widthEq]
  apply integer_binary_loop x y 0#u128 (integerCompareWidth ty) (integerArithmeticOpcode ty kind) 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = integerArithmeticBits kind (laneBits (integerCompareWidth ty).val j x.bv)
      (laneBits (integerCompareWidth ty).val j y.bv))
  · intro j valid a b sa sb remainder aEq bEq saEq sbEq remainderEq
    have exactIndex : remainder = integerArithmeticIndex kind := by
      apply UScalar.eq_of_val_eq
      exact remainderEq.trans (integerArithmeticOpcode_index ty kind)
    subst remainder
    have aBits := lane_word_cast _ j x.bv a aEq
    have bBits := lane_word_cast _ j y.bv b bEq
    simpa only [aBits,bBits] using integer_arithmetic_word kind (integerCompareWidth ty) a b sa sb (by cases ty <;> decide)
  · simp
  · simp

theorem integer_arithmetic_dispatch_eq (ty : Jnn) (kind : IntegerArithmetic) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes (integerArithmeticOpcode ty kind) x y =
      (runtime.interp.simd.integer_binary_lanes_loop (integerArithmeticOpcode ty kind)
        x y (integerCompareWidth ty) 0#u128 0#u32) := by
  cases ty <;> cases kind
  all_goals unfold runtime.interp.simd.integer_binary_lanes integerArithmeticOpcode integerCompareWidth
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals rfl

@[step] theorem integer_arithmetic_lanes (ty : Jnn) (kind : IntegerArithmetic) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes (integerArithmeticOpcode ty kind) x y ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerArithmeticBits kind
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  rw [integer_arithmetic_dispatch_eq]
  apply WP.spec_mono (integer_arithmetic_loop ty kind x y)
  intro result lanes
  simpa using lanes

end Itasca.Runtime.Interp.Simd

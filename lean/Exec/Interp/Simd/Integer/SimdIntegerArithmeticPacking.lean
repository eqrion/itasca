import Exec.Interp.Simd.Integer.SimdIntegerArithmeticLanes
import Exec.Spec.SimdIntegerArithmeticStep
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd SpecExt.Builtins

theorem integer_arithmetic_packed (ty : Jnn) (kind : IntegerArithmetic) (x y result : U128)
    (lanes : ∀ j, j < 128/lsize (lanetype_Jnn ty) →
      laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerArithmeticBits kind
        (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv)) :
    uN.mk_uN result.val = integerArithmeticResult ty kind x.bv y.bv := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty) (128/lsize (lanetype_Jnn ty)) result.bv.toNat
    (fun j => (integerArithmeticBits kind (laneBits (lsize (lanetype_Jnn ty)) j x.bv)
      (laneBits (lsize (lanetype_Jnn ty)) j y.bv)).toNat)
    (by intro j valid; rw [←laneBits_toNat,lanes j valid])
  rw [shapeOf_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  unfold integerArithmeticResult arithmeticWords Map
  rw [List.map_map]
  have same (bits : Nat) : laneOfBits (lanetype_Jnn ty) bits = .mk_lane__0 ty (.mk_uN bits) := by cases ty <;> rfl
  simp only [same] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

end Exec.Interp.Simd

import Exec.Interp.Simd.Common.SimdCompareMaskBits
import Exec.Spec.SimdCompareRelation
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Itasca.Runtime.Spec.Simd

theorem comparison_masks_lanes (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) :
    Map (lane_.mk_lane__0 ty) (comparisonMasks ty op x y) =
      (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
        laneOfBits (lanetype_Jnn ty) (comparisonBits (lsize (lanetype_Jnn ty))
          (integerLaneCompare op (laneBits (lsize (lanetype_Jnn ty)) j x)
            (laneBits (lsize (lanetype_Jnn ty)) j y))).toNat) := by
  simp only [comparisonMasks,comparisonAnswers,Map,List.map_map]
  apply List.map_congr_left
  intro j member
  simp only [Function.comp_apply,proj_uN_0,boolean_extend]
  rw [comparisonBits_signExtend _ (by cases ty <;> decide)]
  cases ty <;> rfl

theorem integer_compare_packed (ty : Jnn) (op : vrelop_Jnn_N) (x y result : U128)
    (lanes : ∀ j, j < 128/lsize (lanetype_Jnn ty) →
      laneBits (lsize (lanetype_Jnn ty)) j result.bv =
        comparisonBits (lsize (lanetype_Jnn ty)) (integerLaneCompare op
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv))) :
    uN.mk_uN result.val = integerComparisonResult ty op x.bv y.bv := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty) (128/lsize (lanetype_Jnn ty)) result.bv.toNat
    (fun j => (comparisonBits (lsize (lanetype_Jnn ty)) (integerLaneCompare op
      (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv))).toNat)
    (by intro j valid; rw [←laneBits_toNat,lanes j valid])
  have covers : lsize (lanetype_Jnn ty)*(128/lsize (lanetype_Jnn ty)) = 128 := by cases ty <;> decide
  rw [covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  rw [integerComparisonResult,comparison_masks_lanes]
  exact congrArg uN.mk_uN packed.symm

end Itasca.Runtime.Interp.Simd

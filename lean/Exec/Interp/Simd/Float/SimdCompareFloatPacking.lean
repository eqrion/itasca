import Exec.Interp.Simd.Float.SimdCompareFloatLanes
import Exec.Interp.Simd.Common.SimdCompareMaskBits
import Exec.Spec.SimdCompareFloatRelation
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Itasca.Runtime.Spec.Simd

theorem float_comparison_masks_lanes (ty : Fnn) (op : vrelop_Fnn_N) (x y : BitVec 128) :
    Map (fun mask => lane_.mk_lane__0 (Jnn_Inn (floatCompareInteger ty)) (.mk_uN (proj_uN_0 mask)))
        (floatComparisonMasks ty op x y) =
      (List.range (128/lsize (lanetype_Fnn ty))).map (fun j =>
        laneOfBits (lanetype_Inn (floatCompareInteger ty))
          (comparisonBits (lsize (lanetype_Fnn ty)) (floatLanePredicate ty op x y j)).toNat) := by
  unfold floatComparisonMasks
  rw [lanes_map_words,lanes_map_words,map2_map]
  simp only [Map,List.map_map]
  apply List.map_congr_left
  intro j member
  simp only [Function.comp_apply,float_comparison_value,proj_uN_0,boolean_extend]
  rw [comparisonBits_signExtend _ (by cases ty <;> decide)]
  cases ty <;> rfl

theorem float_compare_packed (ty : Fnn) (op : vrelop_Fnn_N) (x y result : U128)
    (lanes : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      laneBits (lsize (lanetype_Fnn ty)) j result.bv =
        comparisonBits (lsize (lanetype_Fnn ty)) (floatLanePredicate ty op x.bv y.bv j)) :
    uN.mk_uN result.val = floatComparisonResult ty op x.bv y.bv := by
  have sizeEq : lsize (lanetype_Inn (floatCompareInteger ty)) = lsize (lanetype_Fnn ty) := by
    cases ty <;> rfl
  have packed := pack_map_of_lanes (lanetype_Inn (floatCompareInteger ty))
    (128/lsize (lanetype_Fnn ty)) result.bv.toNat
    (fun j => (comparisonBits (lsize (lanetype_Fnn ty)) (floatLanePredicate ty op x.bv y.bv j)).toNat)
    (by intro j valid; rw [sizeEq,←laneBits_toNat,lanes j valid])
  rw [sizeEq,shapeOf_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  rw [floatComparisonResult,float_comparison_masks_lanes]
  exact congrArg uN.mk_uN packed.symm

end Itasca.Runtime.Interp.Simd

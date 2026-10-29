import Itasca.Runtime.Interp.Simd.Integer.CompareMaskBits
import Itasca.Runtime.Spec.Simd.CompareInteger

/-!
Integer comparison masks packed into the source result. Shared mask, lane and word facts remain below integer and floating-point comparison.
-/

/-! ## Simd Compare Packing -/

section

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

end

/-! ## Simd Compare Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem integer_compare_lanes_sound (ty : Jnn) (op : vrelop_Jnn_N) (x y : U128)
    (supported : Spec.Simd.integerCompareSupported ty op) :
    runtime.interp.simd.compare_lanes (integerCompareOpcode ty op) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VRELOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.integerCompareSource ty op)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (integer_compare_lanes ty op x y supported)
  intro result lanes
  rw [integerCompareWidth_val] at lanes
  exact Spec.Simd.integer_comparison_step ty op x.bv y.bv result.bv supported
    (integer_compare_packed ty op x y result lanes)

theorem integer_compare_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (op : vrelop_Jnn_N) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (integerCompareOpcode ty op) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.compare_lanes (integerCompareOpcode ty op) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases op <;> (try rename_i sign; cases sign)
  all_goals unfold runtime.interp.simd.simd integerCompareOpcode
  all_goals with_unfolding_all rfl

@[step] theorem integer_compare_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (op : vrelop_Jnn_N) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) (supported : Spec.Simd.integerCompareSupported ty op) :
    runtime.interp.simd.simd floats (integerCompareOpcode ty op) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VRELOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.integerCompareSource ty op)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [integer_compare_simd_eq]
  step with integer_compare_lanes_sound ty op x y supported as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end

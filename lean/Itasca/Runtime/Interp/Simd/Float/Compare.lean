import Itasca.Runtime.Interp.Simd.Float.CompareLanes
import Itasca.Runtime.Interp.Simd.Integer.CompareMaskBits
import Itasca.Runtime.Spec.Simd.CompareFloat

/-!
Floating-point comparison masks and packed source dispatch. Scalar comparison and shared lane iteration remain independently available to arithmetic and conversion proofs.
-/

/-! ## Simd Compare Float Packing -/

section

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
  rw [comparison_bits_sign_extend _ (by cases ty <;> decide)]
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
    (by intro j valid; rw [sizeEq,←lane_bits_to_nat,lanes j valid])
  rw [sizeEq,shape_of_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  rw [floatComparisonResult,float_comparison_masks_lanes]
  exact congrArg uN.mk_uN packed.symm

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Compare Float Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem float_compare_lanes_sound (ty : Fnn) (op : vrelop_Fnn_N) (x y : U128)
    :
    runtime.interp.simd.compare_lanes (floatCompareOpcode ty op) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VRELOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatCompareSource ty op)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (float_compare_lanes ty op x y)
  intro result lanes
  exact Spec.Simd.float_comparison_step ty op x.bv y.bv result.bv
    (float_compare_packed ty op x y result lanes)

theorem float_compare_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (op : vrelop_Fnn_N) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatCompareOpcode ty op) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.compare_lanes (floatCompareOpcode ty op) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases op
  all_goals unfold runtime.interp.simd.simd floatCompareOpcode
  all_goals with_unfolding_all rfl

@[step] theorem float_compare_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (op : vrelop_Fnn_N) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatCompareOpcode ty op) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VRELOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatCompareSource ty op)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [float_compare_simd_eq]
  step with float_compare_lanes_sound ty op x y as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end

import Exec.Spec.Choices.SimdConversionChosen
import Exec.Interp.Simd.Integer.SimdConvertIntegerSound
import Exec.Interp.Simd.Common.SimdTruncSatSound
import Exec.Interp.Simd.Integer.SimdWidenSound
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Platform

theorem convert_integer_lanes_chosen {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (occurrence : Nat) (ty : Fnn) (signed : Bool) (x : U128) :
    runtime.interp.simd.convert_lanes floats (convertIntegerOpcode ty signed) x ⦃ out =>
      ∃ value, out = .Ok value ∧ Spec.ChosenVector Spec.firstVectorChoice occurrence
        (.convert (Spec.Simd.shapeOf .I32) (Spec.Simd.shapeOf (lanetype_Fnn ty))
          (Spec.Simd.convertIntegerSource ty (if signed then .S else .U)) (.mk_uN x.val))
        (some (.mk_uN value.val)) ⦄ := by
  apply WP.spec_mono (convert_integer_lanes floats laws ty signed x)
  rintro out ⟨value,rfl,allowed⟩
  exact ⟨value,rfl,Spec.Simd.convert_integer_chosen occurrence ty (if signed then .S else .U)
    x.bv value.bv (Spec.Simd.convert_integer_packed _ _ _ _ allowed)⟩

theorem trunc_sat_lanes_chosen {F : Type} (floats : runtime.platform.FloatOps F)
    (occurrence : Nat) (ty : Fnn) (signed : Bool) (x : U128) :
    runtime.interp.simd.convert_lanes floats (truncSatOpcode ty signed) x ⦃ out =>
      ∃ value, out = .Ok value ∧ Spec.ChosenVector Spec.firstVectorChoice occurrence
        (.convert (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.shapeOf .I32)
          (Spec.Simd.truncSatSource ty (if signed then .S else .U)) (.mk_uN x.val))
        (some (.mk_uN value.val)) ⦄ := by
  apply WP.spec_mono (trunc_sat_lanes floats ty signed x)
  rintro out ⟨value,rfl,allowed,zeroed⟩
  exact ⟨value,rfl,Spec.Simd.trunc_sat_chosen occurrence ty (if signed then .S else .U)
    x.bv value.bv (Spec.Simd.trunc_sat_packed _ _ _ _ allowed zeroed)⟩

theorem extend_lanes_chosen (occurrence : Nat) (ty : Spec.Simd.WidenWidth) (high signed : Bool) (x y : U128) :
    runtime.interp.simd.widen_lanes (widenOpcode ty false high signed) x y ⦃ value =>
      Spec.ChosenVector Spec.firstVectorChoice occurrence
        (.convert (Spec.Simd.shapeOf (lanetype_Jnn ty.input)) (Spec.Simd.shapeOf (lanetype_Jnn ty.output))
          (Spec.Simd.extendOperation ty high signed) (.mk_uN x.val)) (some (.mk_uN value.val)) ⦄ := by
  apply WP.spec_mono (widen_lanes ty false high signed x y)
  intro value lanes
  apply Spec.Simd.extend_chosen_vector occurrence ty high signed x.bv value.bv
  change uN.mk_uN value.val = Spec.Simd.widenResult ty false high signed x.bv x.bv
  have packed := widen_packed ty false high signed x y value lanes
  with_unfolding_all simpa only [Spec.Simd.widenResult,Spec.Simd.widenWords,Spec.Simd.widenBits,Bool.false_eq_true,ite_false] using packed

theorem convert_integer_simd_chosen {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (occurrence : Nat) (ty : Fnn) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (convertIntegerOpcode ty signed) offset laneIndex bits x y z memory ⦃ out =>
      ∃ value, out = (.Ok value,memory) ∧ Spec.ChosenVector Spec.firstVectorChoice occurrence
        (.convert (Spec.Simd.shapeOf .I32) (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.convertIntegerSource ty (if signed then .S else .U)) (.mk_uN x.val)) (some (.mk_uN value.val)) ⦄ := by
  rw [convert_integer_simd_eq]
  step with convert_integer_lanes_chosen floats laws occurrence ty signed x as ⟨result,value,same,chosen⟩
  subst result
  exact ⟨value,rfl,chosen⟩

theorem trunc_sat_simd_chosen {F : Type} (floats : runtime.platform.FloatOps F)
    (occurrence : Nat) (ty : Fnn) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (truncSatOpcode ty signed) offset laneIndex bits x y z memory ⦃ out =>
      ∃ value, out = (.Ok value,memory) ∧ Spec.ChosenVector Spec.firstVectorChoice occurrence
        (.convert (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.shapeOf .I32) (Spec.Simd.truncSatSource ty (if signed then .S else .U)) (.mk_uN x.val)) (some (.mk_uN value.val)) ⦄ := by
  rw [trunc_sat_simd_eq]
  step with trunc_sat_lanes_chosen floats occurrence ty signed x as ⟨result,value,same,chosen⟩
  subst result
  exact ⟨value,rfl,chosen⟩

theorem extend_simd_chosen {F : Type} (floats : runtime.platform.FloatOps F)
    (occurrence : Nat) (ty : Spec.Simd.WidenWidth) (high signed : Bool) (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (widenOpcode ty false high signed) offset laneIndex bits x y z memory ⦃ out =>
      ∃ value, out = (.Ok value,memory) ∧ Spec.ChosenVector Spec.firstVectorChoice occurrence
        (.convert (Spec.Simd.shapeOf (lanetype_Jnn ty.input)) (Spec.Simd.shapeOf (lanetype_Jnn ty.output)) (Spec.Simd.extendOperation ty high signed) (.mk_uN x.val)) (some (.mk_uN value.val)) ⦄ := by
  rw [widen_simd_eq]
  step with extend_lanes_chosen occurrence ty high signed x y as ⟨value,chosen⟩
  exact ⟨value,rfl,chosen⟩
end Exec.Interp.Simd

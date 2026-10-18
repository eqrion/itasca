import Exec.Interp.Simd.Integer.SimdWidenLanes
import Exec.Spec.SimdWidenMultiply
import Exec.Spec.SimdExtendSource
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd SpecExt.Builtins

theorem widen_packed (ty : WidenWidth) (multiply high signed : Bool) (x y result : U128)
    (lanes : ∀ j, j < ty.count → laneBits (ty.width*2) j result.bv = widenBits multiply signed
      (laneBits ty.width (j+if high then ty.count else 0) x.bv)
      (laneBits ty.width (j+if high then ty.count else 0) y.bv)) :
    uN.mk_uN result.val = widenResult ty multiply high signed x.bv y.bv := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty.output) ty.count result.bv.toNat
    (fun j => (widenBits multiply signed (laneBits ty.width (j+if high then ty.count else 0) x.bv)
      (laneBits ty.width (j+if high then ty.count else 0) y.bv)).toNat)
    (by intro j valid;rw [←laneBits_toNat];cases ty <;> exact congrArg BitVec.toNat (lanes j valid))
  have covers : lsize (lanetype_Jnn ty.output)*ty.count = 128 := by cases ty <;> decide
  rw [covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  unfold widenResult widenWords Map
  rw [List.map_map]
  have same (bits : Nat) : laneOfBits (lanetype_Jnn ty.output) bits = .mk_lane__0 ty.output (.mk_uN bits) := by cases ty <;> rfl
  simp only [same] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

@[step] theorem widen_lanes_sound (ty : WidenWidth) (multiply high signed : Bool) (x y : U128) :
    runtime.interp.simd.widen_lanes (widenOpcode ty multiply high signed) x y ⦃ result =>
      Step_pure ((if multiply then [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val)]
        else [.VCONST .V128 (.mk_uN x.val)]) ++ [widenSource ty multiply high signed])
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (widen_lanes ty multiply high signed x y)
  intro result lanes
  have packed := widen_packed ty multiply high signed x y result lanes
  cases multiply
  · exact extend_step ty high signed x.bv result.bv packed
  · exact widen_multiply_step ty high signed x.bv y.bv result.bv packed

theorem widen_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : WidenWidth) (multiply high signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (widenOpcode ty multiply high signed) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.widen_lanes (widenOpcode ty multiply high signed) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases multiply <;> cases high <;> cases signed
  all_goals unfold runtime.interp.simd.simd widenOpcode
  all_goals with_unfolding_all rfl

@[step] theorem widen_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : WidenWidth) (multiply high signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (widenOpcode ty multiply high signed) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure ((if multiply then [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val)]
          else [.VCONST .V128 (.mk_uN x.val)]) ++ [widenSource ty multiply high signed])
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [widen_simd_eq]
  step with widen_lanes_sound ty multiply high signed x y as ⟨value,source⟩
  exact ⟨value,rfl,source⟩
end Exec.Interp.Simd

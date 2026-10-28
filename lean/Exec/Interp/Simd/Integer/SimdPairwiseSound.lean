import Exec.Interp.Simd.Integer.SimdPairwiseLanes
import Exec.Spec.SimdPairwiseSource
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem pairwise_packed (ty : PairwiseWidth) (signed : Bool) (x result : U128)
    (lanes : ∀ j, j < ty.widen.count → laneBits (ty.widen.width*2) j result.bv =
      pairwiseBits signed (laneBits ty.widen.width (2*j) x.bv) (laneBits ty.widen.width (2*j+1) x.bv)) :
    uN.mk_uN result.val = pairwiseResult ty signed x.bv := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty.widen.output) ty.widen.count result.bv.toNat
    (fun j => (pairwiseBits signed (laneBits ty.widen.width (2*j) x.bv) (laneBits ty.widen.width (2*j+1) x.bv)).toNat)
    (by intro j valid;rw [←laneBits_toNat];cases ty <;> exact congrArg BitVec.toNat (lanes j valid))
  have covers : lsize (lanetype_Jnn ty.widen.output)*ty.widen.count = 128 := by cases ty <;> decide
  rw [covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  unfold pairwiseResult pairwiseWords Map
  rw [List.map_map]
  have same (bits : Nat) : laneOfBits (lanetype_Jnn ty.widen.output) bits = .mk_lane__0 ty.widen.output (.mk_uN bits) := by cases ty <;> rfl
  simp only [same] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

@[step] theorem pairwise_lanes_sound (ty : PairwiseWidth) (signed : Bool) (x : U128) :
    runtime.interp.simd.pairwise_add_lanes (pairwiseOpcode ty signed) x ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),pairwiseSource ty signed]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (pairwise_lanes ty signed x)
  intro result lanes
  exact pairwise_step ty signed x.bv result.bv (pairwise_packed ty signed x result lanes)

theorem pairwise_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : PairwiseWidth) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (pairwiseOpcode ty signed) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.pairwise_add_lanes (pairwiseOpcode ty signed) x)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.simd pairwiseOpcode
  all_goals with_unfolding_all rfl

@[step] theorem pairwise_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : PairwiseWidth) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (pairwiseOpcode ty signed) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),pairwiseSource ty signed]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [pairwise_simd_eq]
  step with pairwise_lanes_sound ty signed x as ⟨value,source⟩
  exact ⟨value,rfl,source⟩
end Itasca.Runtime.Interp.Simd

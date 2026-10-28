import Itasca.Runtime.Interp.Simd.Common.SimdUnary
import Itasca.Runtime.Interp.Simd.Common.SimdUnaryBits
import Itasca.Runtime.Spec.SimdPopcount
import SpecExt.Builtins.LaneMap
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem popcount_packed (x result : U128)
    (lanes : ∀ j, j < 128/lsize .I8 →
      laneBits (lsize .I8) j result.bv =
        unaryLane (unaryAction .population) (lsize .I8)
          (laneBits (lsize .I8) j x.bv)) :
    uN.mk_uN result.val = inv_lanes_ (shapeOf .I8)
      ((popcountWords x.bv).map (lane_.mk_lane__0 .I8)) := by
  have laneValue (j : Nat) (valid : j < 128/lsize .I8) :
      result.bv.toNat / 2^(lsize .I8*j) % 2^lsize .I8 =
        (BitVec.ofNat 8 (population (integerBits 8 (vectorLane .I8 x.bv j).toNat))).toNat := by
    rw [←laneBits_toNat,lanes j valid]
    apply congrArg BitVec.toNat
    exact unaryLane_population _
  have packed := pack_map_of_lanes .I8 (128/lsize .I8) result.bv.toNat
    (fun j => (BitVec.ofNat 8 (population (integerBits 8 (vectorLane .I8 x.bv j).toNat))).toNat) laneValue
  rw [shapeOf_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  change uN.mk_uN result.val = uN.mk_uN _
  apply congrArg uN.mk_uN
  refine packed.symm.trans ?_
  apply congrArg (packLanes .I8)
  simp only [popcountWords,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro j member
  have bound := population_bits_le 8 (vectorLane .I8 x.bv j).toNat
  simp [laneOfBits,BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show population (integerBits 8 (vectorLane .I8 x.bv j).toNat) < 256 by omega)]

@[step] theorem popcount_lanes_sound (x : U128) :
    runtime.interp.simd.integer_unary_lanes (unaryOpcode .I8 .population) x
      ⦃ result => Step_pure [.VCONST .V128 (.mk_uN x.val),popcountSource]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (integer_unary_lanes .I8 .population x)
  intro result outcome
  apply popcount_step x.bv result.bv
  apply popcount_packed x result
  exact outcome

theorem popcount_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (unaryOpcode .I8 .population) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.integer_unary_lanes (unaryOpcode .I8 .population) x)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  unfold runtime.interp.simd.simd unaryOpcode
  with_unfolding_all rfl

@[step] theorem popcount_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (unaryOpcode .I8 .population) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),popcountSource]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [popcount_dispatch_eq]
  step with popcount_lanes_sound x as ⟨value,source⟩
  exact ⟨value,rfl,source⟩
end Itasca.Runtime.Interp.Simd

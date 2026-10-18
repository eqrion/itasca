import Exec.Interp.Simd.Integer.SimdNarrowLanes
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd SpecExt.Builtins

theorem narrow_packed (ty : NarrowWidth) (signed : Bool) (x y result : U128)
    (lanes : ∀ j, j < 128/ty.width → laneBits ty.width j result.bv = narrowLane ty.width signed x.bv y.bv j) :
    uN.mk_uN result.val = narrowResult ty signed x.bv y.bv := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty.output) (128/ty.width) result.bv.toNat
    (fun j => (narrowLane ty.width signed x.bv y.bv j).toNat)
    (by
      intro j valid
      rw [←laneBits_toNat]
      change (laneBits ty.width j result.bv).toNat = _
      rw [lanes j valid])
  change packLanes (lanetype_Jnn ty.output) (List.map (fun j => laneOfBits (lanetype_Jnn ty.output)
    (narrowLane ty.width signed x.bv y.bv j).toNat) (List.range (128/ty.width))) = _ at packed
  have words : List.map (fun j => laneOfBits (lanetype_Jnn ty.output)
      (narrowLane ty.width signed x.bv y.bv j).toNat) (List.range (128/ty.width)) =
      Map (lane_.mk_lane__0 ty.output) (narrowWords ty signed x.bv) ++
      Map (lane_.mk_lane__0 ty.output) (narrowWords ty signed y.bv) := by
    cases ty <;> with_unfolding_all rfl
  have covers : lsize (lanetype_Jnn ty.output)*(128/ty.width) = 128 := by cases ty <;> decide
  rw [covers,Nat.mod_eq_of_lt result.bv.isLt,words] at packed
  unfold narrowResult
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

end Exec.Interp.Simd

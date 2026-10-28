import Exec.Interp.Simd.Integer.SimdDotLoop
import Exec.Spec.SimdDotSource
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem dot_packed (x y result : U128)
    (lanes : ∀ j, j < 4 → laneBits 32 j result.bv = dotBits x.bv y.bv j) :
    uN.mk_uN result.val = dotResult x.bv y.bv := by
  have packed := pack_map_of_lanes .I32 (128/lsize .I32) result.bv.toNat
    (fun j => (dotBits x.bv y.bv j).toNat)
    (by intro j valid; rw [←laneBits_toNat]; change (laneBits 32 j result.bv).toNat = _; rw [lanes j valid])
  rw [shapeOf_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  unfold dotResult dotWords Map
  rw [List.map_map]
  have same (bits : Nat) : laneOfBits .I32 bits = .mk_lane__0 .I32 (.mk_uN bits) := by rfl
  simp only [same] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

end Itasca.Runtime.Interp.Simd

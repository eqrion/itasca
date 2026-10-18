import Exec.Interp.Simd.Integer.SimdQ15Loop
import Exec.Spec.SimdQ15Source
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd SpecExt.Builtins

theorem q15_packed (x y result : U128)
    (lanes : ∀ j, j < 128/lsize .I16 →
      laneBits (lsize .I16) j result.bv = q15Bits
        (laneBits (lsize .I16) j x.bv) (laneBits (lsize .I16) j y.bv)) :
    uN.mk_uN result.val = q15Result x.bv y.bv := by
  have packed := pack_map_of_lanes .I16 (128/lsize .I16) result.bv.toNat
    (fun j => (q15Bits (laneBits (lsize .I16) j x.bv)
      (laneBits (lsize .I16) j y.bv)).toNat)
    (by intro j valid; rw [←laneBits_toNat,lanes j valid]; rfl)
  rw [shapeOf_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  unfold q15Result q15Words Map
  rw [List.map_map]
  have same (bits : Nat) : laneOfBits .I16 bits = .mk_lane__0 .I16 (.mk_uN bits) := by rfl
  simp only [same] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

end Exec.Interp.Simd

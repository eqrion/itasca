import Itasca.Runtime.Interp.Simd.Common.SimdPacking
import Itasca.Runtime.Spec.SimdShape
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem unpackLanes_write (ty : lanetype) (index : Nat) (v : BitVec 128) (x : BitVec 64)
    (valid : index < 128/lsize ty) :
    SpecExt.Builtins.unpackLanes ty (128/lsize ty) (writeLaneBits (lsize ty) index v x).toNat =
      (SpecExt.Builtins.unpackLanes ty (128/lsize ty) v.toNat).set index
        (SpecExt.Builtins.laneOfBits ty (x.setWidth (lsize ty)).toNat) := by
  apply List.ext_getElem?
  intro j
  rw [SpecExt.Builtins.unpackLanes_getElem?]
  by_cases inside : j < 128/lsize ty
  · have bound : j < (SpecExt.Builtins.unpackLanes ty (128/lsize ty) v.toNat).length := by
      simpa only [SpecExt.Builtins.unpackLanes_length] using inside
    by_cases same : j = index
    · subst j
      simp only [inside, if_true]
      rw [List.getElem?_set_self (by simpa [SpecExt.Builtins.unpackLanes_length] using valid)]
      rw [←laneBits_toNat, laneBits_write_same _ _ _ _ (lane_range _ _ valid)]
    · rw [List.getElem?_set_ne (Ne.symm same), SpecExt.Builtins.unpackLanes_getElem?]
      simp only [inside, if_true]
      rw [←laneBits_toNat, laneBits_write_other _ _ _ _ _ (lane_range _ _ inside) same, laneBits_toNat]
  · have outside : (SpecExt.Builtins.unpackLanes ty (128/lsize ty) v.toNat).length ≤ j := by
      simpa only [SpecExt.Builtins.unpackLanes_length] using Nat.le_of_not_gt inside
    simp only [inside, if_false]
    exact (List.getElem?_eq_none (by simpa only [List.length_set] using outside)).symm

theorem packLanes_write (ty : lanetype) (index : Nat) (v : BitVec 128) (x : BitVec 64)
    (valid : index < 128/lsize ty) :
    uN.mk_uN (writeLaneBits (lsize ty) index v x).toNat =
      inv_lanes_ (Spec.Simd.shapeOf ty)
        ((lanes_ (Spec.Simd.shapeOf ty) (.mk_uN v.toNat)).set index
          (SpecExt.Builtins.laneOfBits ty (x.setWidth (lsize ty)).toNat)) := by
  change uN.mk_uN _ = uN.mk_uN (SpecExt.Builtins.packLanes ty _)
  dsimp only [lanes_, Spec.Simd.shapeOf, proj_uN_0]
  rw [←unpackLanes_write ty index v x valid, SpecExt.Builtins.pack_unpackLanes,
    Spec.Simd.shapeOf_covers,
    Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (by rfl))]

end Itasca.Runtime.Interp.Simd

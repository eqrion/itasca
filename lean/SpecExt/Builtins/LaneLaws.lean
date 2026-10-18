import SpecExt.Builtins.Lanes
import SpecExt.Builtins.Float.Decoding
import Mathlib.Data.Nat.Basic
namespace SpecExt.Builtins
open Float

theorem laneBits_laneOfBits (ty : lanetype) (bits : Nat) (bound : bits < 2^lsize ty) :
    laneBits ty (laneOfBits ty bits) = bits := by
  cases ty with
  | F32 => exact float_bits_roundtrip_32 bits bound
  | F64 => exact float_bits_roundtrip_64 bits bound
  | _ => rfl

theorem unpackLanes_getElem? (ty : lanetype) (count bits index : Nat) :
    (unpackLanes ty count bits)[index]? =
      if index < count then some (laneOfBits ty (bits / 2^(lsize ty*index) % 2^lsize ty)) else none := by
  induction count generalizing bits index with
  | zero => simp [unpackLanes]
  | succ count ih =>
    cases index with
    | zero => simp [unpackLanes]
    | succ index =>
      simp only [unpackLanes, List.getElem?_cons_succ, ih, Nat.succ_lt_succ_iff,
        Nat.mul_succ, Nat.pow_add, Nat.div_div_eq_div_mul]
      rw [Nat.mul_comm (2^lsize ty) (2^(lsize ty*index))]


theorem pack_unpackLanes (ty : lanetype) (count bits : Nat) :
    packLanes ty (unpackLanes ty count bits) = bits % 2^(lsize ty*count) := by
  induction count generalizing bits with
  | zero => simp only [unpackLanes,packLanes,Nat.mul_zero,pow_zero,Nat.mod_one]
  | succ count ih =>
    simp only [unpackLanes,packLanes,laneBits_laneOfBits _ _ (Nat.mod_lt _ (by positivity)),ih]
    rw [Nat.mul_succ,Nat.pow_add,Nat.mul_comm (2^(lsize ty*count)) (2^lsize ty),Nat.mod_mul]
end SpecExt.Builtins

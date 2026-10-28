import Itasca.Runtime.Code.Local.Initializer.Initializer
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Packing a vector constant retains the full low and high words. -/
theorem initializerBits_val (lo hi : U64) :
    (initializerBits lo hi).val = lo.val + hi.val * 2^64 := by
  have hlo : lo.val < 2^64 := by scalar_tac
  have hloWide : lo.val < 2^128 := by scalar_tac
  have hhiWide : hi.val < 2^128 := by scalar_tac
  have hshift : hi.val * 2^64 < 2^128 := by scalar_tac
  change (lo.bv.setWidth 128 ||| (hi.bv.setWidth 128 <<< 64)).toNat = lo.val + hi.val * 2^64
  simp only [BitVec.toNat_or,BitVec.toNat_shiftLeft,BitVec.toNat_setWidth,UScalar.bv_toNat]
  rw [Nat.mod_eq_of_lt hloWide,Nat.mod_eq_of_lt hhiWide,Nat.shiftLeft_eq,Nat.mod_eq_of_lt hshift]
  rw [Nat.or_comm,←Nat.shiftLeft_eq,←Nat.shiftLeft_add_eq_or_of_lt hlo,Nat.shiftLeft_eq]
  omega
end Itasca.Runtime.Code

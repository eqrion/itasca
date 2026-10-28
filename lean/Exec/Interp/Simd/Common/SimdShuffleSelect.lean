import Exec.Interp.Simd.Common.SimdPacking
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def selectedByte (shuffle : Bool) (x y : BitVec 128) (n : Nat) : BitVec 8 :=
  if n < 16 then laneBits 8 n x
  else if shuffle && decide (n < 32) then laneBits 8 (n-16) y else 0

@[step] theorem shuffle_select (op n : U32) (x y : U128) :
    (if n < 16#u32 then runtime.interp.simd.lane x 8#u32 n
      else if op = 13#u32 then
        if n < 32#u32 then do
          let index ← n - 16#u32
          runtime.interp.simd.lane y 8#u32 index
        else Result.ok 0#u64
      else Result.ok 0#u64)
      ⦃ value => value.bv.setWidth 8 = selectedByte (decide (op = 13#u32)) x.bv y.bv n.val ⦄ := by
  split
  · rename_i first
    have small : n.val < 16 := by scalar_tac
    step with lane as ⟨value,bits⟩
    simp only [selectedByte,if_pos small]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth]
    change value.val % 2^8 = _
    rw [bits,laneBits_toNat]
    simp
  · rename_i rest
    have large : ¬n.val < 16 := by scalar_tac
    split
    · rename_i shuffle
      split
      · rename_i second
        have small : n.val < 32 := by scalar_tac
        step as ⟨index,indexEq⟩
        step with lane as ⟨value,bits⟩
        simp only [selectedByte,if_neg large,shuffle,decide_true,Bool.true_and,decide_eq_true_eq,if_pos small]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth]
        change value.val % 2^8 = _
        rw [bits,laneBits_toNat]
        simp [indexEq]
      · rename_i outside
        have large32 : ¬n.val < 32 := by scalar_tac
        simp [selectedByte,large,shuffle,large32]
    · rename_i swizzle
      simp [selectedByte,large,swizzle]

end Itasca.Runtime.Interp.Simd

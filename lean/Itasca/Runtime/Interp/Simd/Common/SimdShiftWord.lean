import Itasca.Runtime.Interp.Simd.Common.SimdShiftBits
import Itasca.Runtime.Spec.SimdShift
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
open Itasca.Runtime.Spec.Simd

def shiftCode (kind : ShiftKind) : Nat :=
  match kind with | .left => 11 | .signedRight => 12 | .unsignedRight => 13

theorem shift_word (kind : ShiftKind) (op width amount : U32) (value : U64)
    (bits : BitVec width.val) (input : value.bv = bits.setWidth 64)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64) (amountBound : amount.val < width.val)
    (operation : op.val=shiftCode kind) :
    (match op with
      | 11#uscalar => value <<< amount
      | 12#uscalar => do
          let signedValue ← runtime.interp.simd.signed value width
          let shifted ← signedValue >>> amount
          Result.ok (IScalar.hcast .U64 shifted)
      | _ => value >>> amount) ⦃ result =>
        result.bv.setWidth width.val = shiftBits kind bits amount.val ⦄ := by
  have truncated : value.bv.setWidth width.val = bits := by rw [input,BitVec.setWidth_setWidth_of_le _ widthBound,BitVec.setWidth_eq]
  cases kind with
  | left =>
    have eq : op=11#u32 := UScalar.eq_of_val_eq operation
    subst op
    with_unfolding_all change (value <<< amount) ⦃ _ ⦄
    step as ⟨result,valueEq,bitsEq⟩
    simp only [shiftBits,bitsEq,BitVec.setWidth_shiftLeft_of_le widthBound,truncated]
  | signedRight =>
    have eq : op=12#u32 := UScalar.eq_of_val_eq operation
    subst op
    with_unfolding_all change (do
      let s ← runtime.interp.simd.signed value width
      let shifted ← s >>> amount
      Result.ok (IScalar.hcast .U64 shifted)) ⦃ _ ⦄
    step with signed_bits value width positive widthBound as ⟨signedValue,signedEq⟩
    step as ⟨shifted,shiftedEq,shiftedBits⟩
    simp only [shiftBits]
    simp only [IScalar.hcast_bv_eq, UScalarTy.U64_numBits_eq, IScalarTy.I64_numBits_eq, BitVec.signExtend_eq]
    rw [shiftedBits,signedEq,truncated,shiftRight_signed_widen _ _ _ positive widthBound]
  | unsignedRight =>
    have eq : op=13#u32 := UScalar.eq_of_val_eq operation
    subst op
    with_unfolding_all change (value >>> amount) ⦃ _ ⦄
    step as ⟨result,valueEq,bitsEq⟩
    simp only [shiftBits]
    rw [bitsEq,input,shiftRight_widen _ _ _ widthBound]
end Itasca.Runtime.Interp.Simd

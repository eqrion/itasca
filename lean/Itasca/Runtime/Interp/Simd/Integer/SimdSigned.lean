import Itasca.Runtime.Interp.Simd.Common.SimdLanes
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem shifted_signed (bits : BitVec 64) (width : Nat)
    (positive : 0 < width) (bound : width ≤ 64) :
    (bits <<< (64-width)).sshiftRight (64-width) = (bits.setWidth width).signExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.msb_eq_getLsbD_last]
  by_cases valid : i < 64
  · have shiftValid : 64-width < 64 := by omega
    have last : 63-(64-width) = width-1 := by omega
    by_cases small : i < width
    · have fits : i+(64-width) < 64 := by omega
      simp [valid, small, Nat.add_comm, fits, Nat.not_le.mpr valid]
    · have outside : ¬i+(64-width) < 64 := by omega
      simp [valid, small, Nat.add_comm, outside, last, positive, Nat.not_le.mpr valid, Nat.not_lt.mpr (show 64-width ≤ 63 by omega)]
  · simp [valid]

@[step] theorem signed (v : U64) (width : U32)
    (positive : 0 < width.val) (bound : width.val ≤ 64) :
    runtime.interp.simd.signed v width ⦃ result =>
      result.val = (v.bv.setWidth width.val).toInt ⦄ := by
  unfold runtime.interp.simd.signed
  step as ⟨shift, shiftEq⟩
  step as ⟨shifted, shiftedEq, shiftedBits⟩
  rw [lift, bind_ok]
  step as ⟨answer, answerEq, answerBits⟩
  change answer.bv.toInt = _
  have answerBits' : answer.bv = shifted.bv.sshiftRight shift.val := answerBits
  calc
    answer.bv.toInt = (shifted.bv.sshiftRight shift.val).toInt :=
      congrArg BitVec.toInt answerBits'
    _ = ((v.bv <<< shift.val).sshiftRight shift.val).toInt :=
      congrArg (fun (x : BitVec 64) => (x.sshiftRight shift.val).toInt) shiftedBits
    _ = (v.bv.setWidth width.val).toInt := by
      rw [shiftEq, shifted_signed v.bv width.val positive bound,
        BitVec.toInt_signExtend_of_le bound]
end Itasca.Runtime.Interp.Simd

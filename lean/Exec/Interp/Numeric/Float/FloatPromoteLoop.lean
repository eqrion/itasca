import Exec.Interp.Numeric.Float.Float
namespace Exec.Interp
open Aeneas Aeneas.Std

@[step] theorem promote_loop_effect (fraction : U32)
    (positive : 0 < fraction.val) (small : fraction.val < 8388608) :
    runtime.interp.float.promote_loop fraction 897#u64 ⦃ result =>
      ∃ shifts : Nat, shifts ≤ 24 ∧ result.1.val = fraction.val * 2^shifts ∧
        result.2.val = 897 - shifts ∧ 8388608 ≤ result.1.val ∧ result.1.val < 16777216 ⦄ := by
  unfold runtime.interp.float.promote_loop
  apply loop.spec_decr_nat (fun p => 8388608 - p.1.val)
    (fun p => ∃ shifts : Nat, shifts ≤ 24 ∧ p.1.val = fraction.val * 2^shifts ∧
      p.2.val = 897 - shifts ∧ 0 < p.1.val ∧ p.1.val < 16777216)
  · rintro ⟨current, exponent⟩ ⟨shifts, count, fractionEq, exponentEq, currentPositive, currentBound⟩
    dsimp only at *
    unfold runtime.interp.float.promote_loop.body
    split
    · have nextBound : current.val < 8388608 := by scalar_tac
      have room : shifts < 24 := by
        by_contra h
        have equal : shifts = 24 := by omega
        rw [equal] at fractionEq
        norm_num at fractionEq
        omega
      step as ⟨doubled, doubleEq, doubleBits⟩
      have double : doubled.val = current.val * 2 := by
        rw [doubleEq]
        simp only [Nat.shiftLeft_eq, Int.reduceToNat, Nat.reducePow]
        norm_num only [U32.size, U32.numBits, UScalarTy.U32_numBits_eq, Nat.reducePow]
        omega
      step as ⟨next, nextEq⟩
      refine ⟨⟨shifts+1, by omega, ?_, ?_, by omega, by omega⟩, by omega⟩
      · rw [double, fractionEq, pow_succ]
        ring
      · omega
    · have finished : 8388608 ≤ current.val := by scalar_tac
      exact ⟨shifts, count, fractionEq, exponentEq, finished, currentBound⟩
  · dsimp only
    exact ⟨0, by omega, by simp, rfl, positive, by omega⟩

end Exec.Interp

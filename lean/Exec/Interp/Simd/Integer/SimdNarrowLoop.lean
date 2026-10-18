import Exec.Interp.Simd.Integer.SimdSaturation
import Exec.Interp.Simd.Integer.SimdIntegerArithmeticLanes
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd

def narrowLane (width : Nat) (signed : Bool) (x y : BitVec 128) (j : Nat) : BitVec width :=
  BitVec.ofInt width (clampLane width signed
    (laneBits (width*2) (j%(64/width)) (if j < 64/width then x else y)).toInt)

theorem narrow_loop (x y initial : U128) (width i : U32) (signedFlag : Bool)
    (supported : width.val ∈ [8,16]) (position : i.val ≤ 128/width.val)
    (initializedPrefix : ∀ j, j < i.val → laneBits width.val j initial.bv = narrowLane width.val signedFlag x.bv y.bv j) :
    runtime.interp.simd.narrow_lanes_loop width signedFlag y x initial i ⦃ result =>
      ∀ j, j < 128/width.val → laneBits width.val j result.bv = narrowLane width.val signedFlag x.bv y.bv j ⦄ := by
  have positive : 0 < width.val := by simp_all; omega
  have widthBound : width.val ≤ 64 := by simp_all; omega
  have halfPositive : 0 < 64/width.val := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
    rcases supported with h | h <;> rw [h] <;> decide
  have wideBound : width.val*2 ≤ 64 := by simp_all; omega
  unfold runtime.interp.simd.narrow_lanes_loop
  apply loop.spec_decr_nat (fun p => 128/width.val-p.2.val)
    (fun p => p.2.val ≤ 128/width.val ∧ ∀ j, j < p.2.val →
      laneBits width.val j p.1.bv = narrowLane width.val signedFlag x.bv y.bv j)
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.narrow_lanes_loop.body
    dsimp only
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 128/width.val := by scalar_tac
      step as ⟨half,halfEq⟩
      have selectEq : (if index < half then Result.ok x else Result.ok y) = Result.ok (if index < half then x else y) := by split <;> rfl
      rw [selectEq,bind_ok]
      step as ⟨wide,wideEq⟩
      step as ⟨laneIndex,laneIndexEq⟩
      have laneBound : wide.val*laneIndex.val < 128 := by
        rw [wideEq,laneIndexEq,halfEq]
        have modBound := Nat.mod_lt index.val halfPositive
        simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
        rcases supported with h | h <;> rw [h] at * <;> omega
      step with lane (if index < half then x else y) wide laneIndex (by scalar_tac) (by scalar_tac) laneBound as ⟨a,aEq⟩
      have aBits := lane_word_cast wide.val laneIndex.val (if index < half then x else y).bv a (by rw [laneBits_toNat]; exact aEq)
      step with signed a wide (by scalar_tac) (by scalar_tac) as ⟨sa,saEq⟩
      step as ⟨widened,widenedEq⟩
      step with saturate widened width signedFlag (by simp only [List.mem_cons,List.not_mem_nil,or_false] at supported ⊢; rcases supported with h | h; exact Or.inl h; exact Or.inr (Or.inl h)) as ⟨value,valueEq⟩
      have widenedVal : widened.val = sa.val := by simp [widenedEq]
      have correct : value.bv.setWidth width.val = narrowLane width.val signedFlag x.bv y.bv index.val := by
        rw [valueEq,widenedVal,saEq,aBits]
        with_unfolding_all rw [wideEq]
        simp only [laneIndexEq,UScalar.lt_equiv,halfEq,narrowLane]
        split <;> rfl
      step with put_lanes current width index value positive widthBound (lane_range _ _ less) as ⟨updated,same,other⟩
      have countBound : 128/width.val ≤ 128 := Nat.div_le_self _ _
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; rw [same]; exact correct
        · rw [other j (lane_range _ _ (by omega)) eq]; exact initialized j (by omega)
      · omega
    · have finished : index.val = 128/width.val := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩

end Exec.Interp.Simd

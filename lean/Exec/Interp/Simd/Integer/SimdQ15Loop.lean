import Exec.Interp.Simd.Integer.SimdQ15Word
import Exec.Interp.Simd.Integer.SimdIntegerArithmeticLanes
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd

theorem q15_loop (x y initial : U128) (i : U32)
    (position : i.val ≤ 8)
    (initializedPrefix : ∀ j, j < i.val → laneBits 16 j initial.bv =
      q15Bits (laneBits 16 j x.bv) (laneBits 16 j y.bv)) :
    runtime.interp.simd.multiply_lanes_loop 130#u32 y x initial i ⦃ result =>
      ∀ j, j < 8 → laneBits 16 j result.bv = q15Bits (laneBits 16 j x.bv) (laneBits 16 j y.bv) ⦄ := by
  unfold runtime.interp.simd.multiply_lanes_loop
  apply loop.spec_decr_nat (fun p => 8-p.2.val)
    (fun p => p.2.val ≤ 8 ∧ ∀ j, j < p.2.val → laneBits 16 j p.1.bv =
      q15Bits (laneBits 16 j x.bv) (laneBits 16 j y.bv))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.multiply_lanes_loop.body
    simp only [↓reduceIte]
    split
    · rename_i more
      have less : index.val < 8 := by scalar_tac
      step with lane x 16#u32 index (by decide) (by decide) (by scalar_tac) as ⟨a,aEq⟩
      have aBits : a.bv.setWidth 16 = laneBits 16 index.val x.bv :=
        lane_word_cast 16 _ _ a (by rw [laneBits_toNat]; exact aEq)
      step with signed a 16#u32 (by decide) (by decide) as ⟨sa,saEq⟩
      step with lane y 16#u32 index (by decide) (by decide) (by scalar_tac) as ⟨b,bEq⟩
      have bBits : b.bv.setWidth 16 = laneBits 16 index.val y.bv :=
        lane_word_cast 16 _ _ b (by rw [laneBits_toNat]; exact bEq)
      step with signed b 16#u32 (by decide) (by decide) as ⟨sb,sbEq⟩
      have aBound : -32768 ≤ sa.val ∧ sa.val < 32768 := by
        rw [saEq]; exact ⟨BitVec.le_toInt _,BitVec.toInt_lt⟩
      have bBound : -32768 ≤ sb.val ∧ sb.val < 32768 := by
        rw [sbEq]; exact ⟨BitVec.le_toInt _,BitVec.toInt_lt⟩
      rw [←Std.bind_assoc,←Std.bind_assoc,←Std.bind_assoc,←Std.bind_assoc]
      with_unfolding_all change (Aeneas.Std.bind (q15Word sa sb) _) ⦃ _ ⦄
      step with q15_word sa sb aBound bBound as ⟨value,valueEq⟩
      change sa.val = (a.bv.setWidth 16).toInt at saEq
      change sb.val = (b.bv.setWidth 16).toInt at sbEq
      rw [aBits] at saEq
      rw [bBits] at sbEq
      have correct : value.bv.setWidth 16 = q15Bits (laneBits 16 index.val x.bv) (laneBits 16 index.val y.bv) := by
        with_unfolding_all simpa only [q15Bits,saEq,sbEq] using valueEq
      step with put_lanes current 16#u32 index value (by decide) (by decide) (by scalar_tac) as ⟨updated,same,other⟩
      change laneBits 16 index.val updated.bv = value.bv.setWidth 16 at same
      change ∀ j, 16*j+16 ≤ 128 → j ≠ index.val → laneBits 16 j updated.bv = laneBits 16 j current.bv at other
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; rw [same]; exact correct
        · rw [other j (by omega) eq]; exact initialized j (by omega)
      · omega
    · have finished : index.val = 8 := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩

@[step] theorem q15_lanes (x y : U128) :
    runtime.interp.simd.multiply_lanes 130#u32 x y ⦃ result =>
      ∀ j, j < 8 → laneBits 16 j result.bv = q15Bits (laneBits 16 j x.bv) (laneBits 16 j y.bv) ⦄ := by
  unfold runtime.interp.simd.multiply_lanes
  step with q15_loop x y 0#u128 0#u32 (by decide) (by simp) as ⟨result,lanes⟩
  simpa [runtime.interp.simd.vector] using lanes

end Exec.Interp.Simd

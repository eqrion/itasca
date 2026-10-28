import Exec.Spec.SimdDot
import Exec.Interp.Simd.Integer.SimdDotWord
import Exec.Interp.Simd.Integer.SimdIntegerArithmeticLanes
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

theorem dot_loop (x y initial : U128) (i : U32)
    (position : i.val ≤ 4)
    (initializedPrefix : ∀ j, j < i.val → laneBits 32 j initial.bv = dotBits x.bv y.bv j) :
    runtime.interp.simd.multiply_lanes_loop 186#u32 x y initial i ⦃ result =>
      ∀ j, j < 4 → laneBits 32 j result.bv = dotBits x.bv y.bv j ⦄ := by
  unfold runtime.interp.simd.multiply_lanes_loop
  apply loop.spec_decr_nat (fun p => 4-p.2.val)
    (fun p => p.2.val ≤ 4 ∧ ∀ j, j < p.2.val → laneBits 32 j p.1.bv = dotBits x.bv y.bv j)
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.multiply_lanes_loop.body
    simp only [show (186#u32 ≠ 130#u32) by decide, ↓reduceIte]
    split
    · rename_i more
      have less : index.val < 4 := by scalar_tac
      step as ⟨even,evenEq⟩
      step with lane x 16#u32 even (by decide) (by decide) (by scalar_tac) as ⟨a0,a0Eq⟩
      have a0Bits : a0.bv.setWidth 16 = laneBits 16 even.val x.bv :=
        lane_word_cast 16 _ _ a0 (by rw [laneBits_toNat]; exact a0Eq)
      step with signed a0 16#u32 (by decide) (by decide) as ⟨sa0,sa0Eq⟩
      have a0Bound : -32768 ≤ sa0.val ∧ sa0.val < 32768 := by
        rw [sa0Eq]; exact ⟨BitVec.le_toInt _,BitVec.toInt_lt⟩
      change sa0.val = (a0.bv.setWidth 16).toInt at sa0Eq
      rw [a0Bits] at sa0Eq
      step with lane y 16#u32 even (by decide) (by decide) (by scalar_tac) as ⟨b0,b0Eq⟩
      have b0Bits : b0.bv.setWidth 16 = laneBits 16 even.val y.bv :=
        lane_word_cast 16 _ _ b0 (by rw [laneBits_toNat]; exact b0Eq)
      step with signed b0 16#u32 (by decide) (by decide) as ⟨sb0,sb0Eq⟩
      have b0Bound : -32768 ≤ sb0.val ∧ sb0.val < 32768 := by
        rw [sb0Eq]; exact ⟨BitVec.le_toInt _,BitVec.toInt_lt⟩
      change sb0.val = (b0.bv.setWidth 16).toInt at sb0Eq
      rw [b0Bits] at sb0Eq
      step with dot_mul sa0 sb0 a0Bound b0Bound as ⟨p0,p0Eq,p0Lo,p0Hi⟩
      step as ⟨odd,oddEq⟩
      step with lane x 16#u32 odd (by decide) (by decide) (by scalar_tac) as ⟨a1,a1Eq⟩
      have a1Bits : a1.bv.setWidth 16 = laneBits 16 odd.val x.bv :=
        lane_word_cast 16 _ _ a1 (by rw [laneBits_toNat]; exact a1Eq)
      step with signed a1 16#u32 (by decide) (by decide) as ⟨sa1,sa1Eq⟩
      have a1Bound : -32768 ≤ sa1.val ∧ sa1.val < 32768 := by
        rw [sa1Eq]; exact ⟨BitVec.le_toInt _,BitVec.toInt_lt⟩
      change sa1.val = (a1.bv.setWidth 16).toInt at sa1Eq
      rw [a1Bits] at sa1Eq
      step as ⟨oddY,oddYEq⟩
      step with lane y 16#u32 oddY (by decide) (by decide) (by scalar_tac) as ⟨b1,b1Eq⟩
      have b1Bits : b1.bv.setWidth 16 = laneBits 16 oddY.val y.bv :=
        lane_word_cast 16 _ _ b1 (by rw [laneBits_toNat]; exact b1Eq)
      step with signed b1 16#u32 (by decide) (by decide) as ⟨sb1,sb1Eq⟩
      have b1Bound : -32768 ≤ sb1.val ∧ sb1.val < 32768 := by
        rw [sb1Eq]; exact ⟨BitVec.le_toInt _,BitVec.toInt_lt⟩
      change sb1.val = (b1.bv.setWidth 16).toInt at sb1Eq
      rw [b1Bits] at sb1Eq
      step with dot_mul sa1 sb1 a1Bound b1Bound as ⟨p1,p1Eq,p1Lo,p1Hi⟩
      step as ⟨total,totalEq⟩
      step as ⟨value,valueEq⟩
      have correct : value.bv.setWidth 32 = dotBits x.bv y.bv index.val := by
        rw [valueEq,dot_cast,dot_bits_int,totalEq,p0Eq,p1Eq,sa0Eq,sb0Eq,sa1Eq,sb1Eq]
        with_unfolding_all simp only [evenEq,oddEq,oddYEq]
        rfl
      step with put_lanes current 32#u32 index value (by decide) (by decide) (by scalar_tac) as ⟨updated,same,other⟩
      change laneBits 32 index.val updated.bv = value.bv.setWidth 32 at same
      change ∀ j, 32*j+32 ≤ 128 → j ≠ index.val → laneBits 32 j updated.bv = laneBits 32 j current.bv at other
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; rw [same]; exact correct
        · rw [other j (by omega) eq]; exact initialized j (by omega)
      · omega
    · have finished : index.val = 4 := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩

@[step] theorem dot_lanes (x y : U128) :
    runtime.interp.simd.multiply_lanes 186#u32 x y ⦃ result =>
      ∀ j, j < 4 → laneBits 32 j result.bv = dotBits x.bv y.bv j ⦄ := by
  unfold runtime.interp.simd.multiply_lanes
  apply WP.spec_mono (dot_loop x y 0#u128 0#u32 (by decide) (by simp))
  intro result lanes
  simpa using lanes

end Itasca.Runtime.Interp.Simd

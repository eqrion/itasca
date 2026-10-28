import Itasca.Runtime.Interp.Simd.Integer.SimdIntegerBinaryLoop
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def pairwiseWord (width : U32) (signed : Bool) (a b : U64) : Result U64 := do
  if signed then
    let sa ← runtime.interp.simd.signed a width
    let sb ← runtime.interp.simd.signed b width
    let sum ← sa + sb
    Result.ok (IScalar.hcast .U64 sum)
  else a + b

theorem pairwise_loop (width i : U32) (signed : Bool) (x initial : U128)
    (positive : 0 < width.val) (widthBound : width.val ≤ 32)
    (R : Nat → BitVec (width.val*2) → Prop)
    (wordLaw : ∀ j, j < 64/width.val → ∀ a b : U64,
      a.val = (laneBits width.val (2*j) x.bv).toNat →
      b.val = (laneBits width.val (2*j+1) x.bv).toNat →
      pairwiseWord width signed a b ⦃ value => R j (value.bv.setWidth (width.val*2)) ⦄)
    (position : i.val ≤ 64/width.val)
    (initializedPrefix : ∀ j, j < i.val → R j (laneBits (width.val*2) j initial.bv)) :
    runtime.interp.simd.pairwise_add_lanes_loop x width signed initial i ⦃ result =>
      ∀ j, j < 64/width.val → R j (laneBits (width.val*2) j result.bv) ⦄ := by
  unfold runtime.interp.simd.pairwise_add_lanes_loop
  apply loop.spec_decr_nat (fun p => 64/width.val-p.2.val)
    (fun p => p.2.val ≤ 64/width.val ∧ ∀ j, j < p.2.val → R j (laneBits (width.val*2) j p.1.bv))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.pairwise_add_lanes_loop.body
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 64/width.val := by scalar_tac
      have countBound : 64/width.val ≤ 64 := Nat.div_le_self _ _
      have productBound : width.val*(64/width.val) ≤ 64 := Nat.mul_div_le _ _
      have indexProduct : width.val*(index.val+1) ≤ 64 :=
        (Nat.mul_le_mul_left _ less).trans productBound
      have range : width.val*2*index.val+width.val*2 ≤ 128 := by nlinarith
      step as ⟨first,firstEq⟩
      step with lane x width first positive (by omega) (by rw [firstEq]; nlinarith) as ⟨a,aEq⟩
      step as ⟨second,secondEq⟩
      step with lane x width second positive (by omega) (by rw [secondEq,firstEq];nlinarith) as ⟨b,bEq⟩
      have aBits : a.val = (laneBits width.val (2*index.val) x.bv).toNat := by
        rw [laneBits_toNat,←firstEq]; exact aEq
      have bBits : b.val = (laneBits width.val (2*index.val+1) x.bv).toNat := by
        rw [laneBits_toNat,←firstEq,←secondEq]; exact bEq
      with_unfolding_all change Aeneas.Std.bind (pairwiseWord width signed a b) _ ⦃ _ ⦄
      step with wordLaw index.val less a b aBits bBits as ⟨value,allowed⟩
      step as ⟨wide,wideEq⟩
      step with put_lanes current wide index value (by omega) (by omega) (by rw [wideEq];exact range) as ⟨updated,same,other⟩
      step as ⟨next,nextEq⟩
      refine ⟨by omega,?_,by omega⟩
      intro j bound
      by_cases eq : j=index.val
      · subst j; rw [wideEq] at same; rw [same]; exact allowed
      · have otherRange : wide.val*j+wide.val ≤ 128 := by
          have le : j ≤ index.val := by omega
          have := Nat.mul_le_mul_left (width.val*2) le
          rw [wideEq]; omega
        rw [wideEq] at other
        rw [other j (by simpa only [wideEq] using otherRange) eq]
        exact initialized j (by omega)
    · have finished : index.val=64/width.val := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩
end Itasca.Runtime.Interp.Simd

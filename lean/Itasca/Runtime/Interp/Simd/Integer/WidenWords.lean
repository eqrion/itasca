import Itasca.Runtime.Interp.Simd.Integer.BinaryLoop
import Itasca.Runtime.Interp.Simd.Integer.ShiftBits
import Itasca.Runtime.Spec.Simd.Widen

/-!
Widening integer lane calculations and their loop. Memory extension and pairwise addition consume these word facts without importing the final widening source correspondence.
-/

/-! ## Simd Widen Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def widenWord (width : U32) (extmul signed : Bool) (a b : U64) : Result U64 := do
  let a1 ← if signed then do
    let value ← runtime.interp.simd.signed a width
    Result.ok (IScalar.hcast .U64 value)
    else Result.ok a
  let b1 ← if signed then do
    let value ← runtime.interp.simd.signed b width
    Result.ok (IScalar.hcast .U64 value)
    else Result.ok b
  if extmul then Result.ok (core.num.U64.wrapping_mul a1 b1) else Result.ok a1

theorem widenWord_bind {α : Type} (width : U32) (extmul signed : Bool) (a b : U64) (k : U64 → Result α) :
    Aeneas.Std.bind (widenWord width extmul signed a b) k = (do
      let a1 ← if signed then do
        let value ← runtime.interp.simd.signed a width
        Result.ok (IScalar.hcast .U64 value)
        else Result.ok a
      let b1 ← if signed then do
        let value ← runtime.interp.simd.signed b width
        Result.ok (IScalar.hcast .U64 value)
        else Result.ok b
      let product ← if extmul then Result.ok (core.num.U64.wrapping_mul a1 b1) else Result.ok a1
      k product) := by
  simp only [widenWord,Std.bind_assoc]

theorem widen_loop (width i : U32) (extmul high signed : Bool) (x y initial : U128)
    (positive : 0 < width.val) (widthBound : width.val ≤ 32)
    (R : Nat → BitVec (width.val*2) → Prop)
    (wordLaw : ∀ j, j < 64/width.val → ∀ a b : U64,
      a.val = (laneBits width.val (j + if high then 64/width.val else 0) x.bv).toNat →
      b.val = (laneBits width.val (j + if high then 64/width.val else 0) y.bv).toNat →
      widenWord width extmul signed a b ⦃ value => R j (value.bv.setWidth (width.val*2)) ⦄)
    (position : i.val ≤ 64/width.val)
    (initializedPrefix : ∀ j, j < i.val → R j (laneBits (width.val*2) j initial.bv)) :
    runtime.interp.simd.widen_lanes_loop x width extmul high signed y initial i ⦃ result =>
      ∀ j, j < 64/width.val → R j (laneBits (width.val*2) j result.bv) ⦄ := by
  unfold runtime.interp.simd.widen_lanes_loop
  apply loop.spec_decr_nat (fun p => 64/width.val-p.2.val)
    (fun p => p.2.val ≤ 64/width.val ∧ ∀ j, j < p.2.val → R j (laneBits (width.val*2) j p.1.bv))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.widen_lanes_loop.body
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 64/width.val := by scalar_tac
      have countBound : 64/width.val ≤ 64 := Nat.div_le_self _ _
      have productBound : width.val*(64/width.val) ≤ 64 := Nat.mul_div_le _ _
      have indexProduct : width.val*(index.val+1) ≤ 64 :=
        (Nat.mul_le_mul_left _ less).trans productBound
      have range : width.val*2*index.val+width.val*2 ≤ 128 := by nlinarith
      have selectionBound : ∀ offset : U32, offset.val = (if high then 64/width.val else 0) →
          width.val*(index.val+offset.val) < 128 := by
        intro offset eq
        cases high <;> simp_all <;> nlinarith
      have offsetCall : (if high then Result.ok count else Result.ok 0#u32) ⦃ offset =>
          offset.val = (if high then 64/width.val else 0) ⦄ := by
        cases high <;> simp_all [WP.spec_ok]
      step with offsetCall as ⟨offset,offsetEq⟩
      have offsetBound : offset.val ≤ 64 := by cases high <;> simp_all
      step as ⟨selected,selectedEq⟩
      have selectedRange : width.val*selected.val < 128 := by rw [selectedEq]; exact selectionBound offset offsetEq
      step with lane x width selected positive (by omega) selectedRange as ⟨a,aEq⟩
      step with lane y width selected positive (by omega) selectedRange as ⟨b,bEq⟩
      have aBits : a.val = (laneBits width.val (index.val + if high then 64/width.val else 0) x.bv).toNat := by
        rw [laneBits_toNat,←offsetEq,←selectedEq]; exact aEq
      have bBits : b.val = (laneBits width.val (index.val + if high then 64/width.val else 0) y.bv).toNat := by
        rw [laneBits_toNat,←offsetEq,←selectedEq]; exact bEq
      with_unfolding_all rw [←widenWord_bind width extmul signed a b]
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

end

/-! ## Simd Widen Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

theorem signExtend_restrict {width : Nat} (bits : BitVec width) (output : Nat) (le : output ≤ 64) :
    (bits.signExtend 64).setWidth output = bits.signExtend output := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_signExtend]
  by_cases inside : i < output
  · simp [inside,show i < 64 by omega]
  · simp [inside]

@[step] theorem widen_input (width : U32) (signed : Bool) (a : U64) (bits : BitVec width.val)
    (positive : 0 < width.val) (bound : width.val ≤ 32)
    (input : a.val = bits.toNat) :
    (if signed then do
      let value ← runtime.interp.simd.signed a width
      Result.ok (IScalar.hcast .U64 value)
      else Result.ok a) ⦃ result => result.bv.setWidth (width.val*2) = extendBits signed (width.val*2) bits ⦄ := by
  have aBits : a.bv = bits.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth_of_le (by omega)]
    exact input
  cases signed
  · simp only [Bool.false_eq_true,↓reduceIte,WP.spec_ok,extendBits]
    exact (congrArg (BitVec.setWidth (width.val*2)) aBits).trans
      (BitVec.setWidth_setWidth_of_le _ (by omega))
  · simp only [Bool.true_eq,↓reduceIte]
    step with signed_bits a width positive (by omega) as ⟨value,valueEq⟩
    simp only [IScalar.hcast_bv_eq,UScalarTy.U64_numBits_eq,IScalarTy.I64_numBits_eq,BitVec.signExtend_eq]
    have narrow : a.bv.setWidth width.val = bits := by
      rw [aBits,BitVec.setWidth_setWidth_of_le _ (by omega),BitVec.setWidth_eq]
    have exactValue : value.bv = bits.signExtend 64 := by rw [valueEq,narrow]
    exact (congrArg (BitVec.setWidth (width.val*2)) exactValue).trans
      (signExtend_restrict bits _ (by omega))

@[step] theorem widen_word (width : U32) (multiply signed : Bool) (a b : U64)
    (x y : BitVec width.val) (positive : 0 < width.val) (bound : width.val ≤ 32)
    (aBits : a.val = x.toNat) (bBits : b.val = y.toNat) :
    widenWord width multiply signed a b ⦃ result =>
      result.bv.setWidth (width.val*2) = widenBits multiply signed x y ⦄ := by
  unfold widenWord
  step with widen_input width signed a x positive bound aBits as ⟨first,firstEq⟩
  step with widen_input width signed b y positive bound bBits as ⟨second,secondEq⟩
  cases multiply
  · exact WP.spec.ret firstEq
  · apply WP.spec.ret
    with_unfolding_all change (first.bv*second.bv).setWidth (width.val*2) = _
    rw [BitVec.setWidth_mul _ _ (by omega),firstEq,secondEq]
    rfl
end Itasca.Runtime.Interp.Simd

end

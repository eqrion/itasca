import Itasca.Runtime.Interp.Simd.Lanes.Packing

/-!
Packed comparison masks for integer lanes.

Main declarations: `comparisonBits`. A direct consumer is `Interp.Simd.Float.CompareLanes`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

def comparisonBits (width : Nat) (answer : Bool) : BitVec width :=
  if answer then (core.num.U64.MAX).bv.setWidth width else 0

@[step] theorem comparison_loop (x y initial : U128) (width cmp i : U32) (float : Bool)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (predicate : Nat → Bool)
    (compareLaw : ∀ j, j < 128/width.val → ∀ (a b : U64),
      a.val = (laneBits width.val j x.bv).toNat →
      b.val = (laneBits width.val j y.bv).toNat →
      (if float then runtime.interp.float.compare_float (UScalar.cast .U16 cmp) a b width
        else runtime.interp.int.compare_int (UScalar.cast .U16 cmp) a b width)
        ⦃ answer => answer = predicate j ⦄)
    (position : i.val ≤ 128/width.val)
    (initializedPrefix : ∀ j, j < i.val →
      laneBits width.val j initial.bv = comparisonBits width.val (predicate j))
    (zeroSuffix : ∀ j, i.val ≤ j → j < 128/width.val → laneBits width.val j initial.bv = 0) :
    runtime.interp.simd.compare_lanes_loop x y width cmp float initial i ⦃ result =>
      ∀ j, j < 128/width.val → laneBits width.val j result.bv = comparisonBits width.val (predicate j) ⦄ := by
  unfold runtime.interp.simd.compare_lanes_loop
  apply loop.spec_decr_nat (fun p => 128/width.val-p.2.val)
    (fun p => p.2.val ≤ 128/width.val ∧
      (∀ j, j < p.2.val → laneBits width.val j p.1.bv = comparisonBits width.val (predicate j)) ∧
      (∀ j, p.2.val ≤ j → j < 128/width.val → laneBits width.val j p.1.bv = 0))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized,zeros⟩
    dsimp only at indexBound initialized zeros
    unfold runtime.interp.simd.compare_lanes_loop.body
    dsimp only
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 128/width.val := by scalar_tac
      have range := lane_range width.val index.val less
      step with lane as ⟨a,aEq⟩
      step with lane as ⟨b,bEq⟩
      have aBits : a.val = (laneBits width.val index.val x.bv).toNat := by rw [laneBits_toNat]; exact aEq
      have bBits : b.val = (laneBits width.val index.val y.bv).toNat := by rw [laneBits_toNat]; exact bEq
      have compareCall :
          (if float then do
            let op ← lift (UScalar.cast .U16 cmp)
            runtime.interp.float.compare_float op a b width
           else do
            let op ← lift (UScalar.cast .U16 cmp)
            runtime.interp.int.compare_int op a b width)
          ⦃ answer => answer = predicate index.val ⦄ := by
        simpa only [lift,bind_ok] using compareLaw index.val less a b aBits bBits
      step with compareCall as ⟨answer,answerEq⟩
      have update : (if answer then runtime.interp.simd.put current width index core.num.U64.MAX
          else Result.ok current) ⦃ updated =>
        laneBits width.val index.val updated.bv = comparisonBits width.val answer ∧
        ∀ j, width.val*j+width.val ≤ 128 → j ≠ index.val →
          laneBits width.val j updated.bv = laneBits width.val j current.bv ⦄ := by
        cases answer
        · simp only [Bool.false_eq_true,if_false,WP.spec_ok,comparisonBits]
          exact ⟨zeros index.val (by omega) less,by simp⟩
        · simp only [if_true,comparisonBits]
          exact put_lanes current width index core.num.U64.MAX positive widthBound range
      step with update as ⟨updated,same,other⟩
      have countBound : 128/width.val ≤ 128 := Nat.div_le_self _ _
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; simpa only [answerEq] using same
        · exact (other j (lane_range _ _ (by omega)) eq).trans (initialized j (by omega))
      · intro j after valid
        exact (other j (lane_range _ _ valid) (by omega)).trans (zeros j (by omega) valid)
      · omega
    · have finished : index.val = 128/width.val := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix,zeroSuffix⟩

end Itasca.Runtime.Interp.Simd

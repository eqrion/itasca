import Exec.Interp.Simd.Common.SimdSplat
import Exec.Interp.Simd.Common.SimdPacking
import Exec.Interp.Simd.Integer.SimdSigned
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std

def integerBinaryWord (op width : U32) (a b : U64) (sa sb : I64) : Result U64 :=
  match op with
  | 14#uscalar => Result.ok (core.num.U64.wrapping_add a b)
  | 15#uscalar =>
    do
    let i3 ← lift (IScalar.cast .I128 sa)
    let i4 ← lift (IScalar.cast .I128 sb)
    let i5 ← i3 + i4
    runtime.interp.simd.sat i5 width true
  | 16#uscalar =>
    do
    let i3 ← lift (UScalar.hcast .I128 a)
    let i4 ← lift (UScalar.hcast .I128 b)
    let i5 ← i3 + i4
    runtime.interp.simd.sat i5 width false
  | 17#uscalar => Result.ok (core.num.U64.wrapping_sub a b)
  | 18#uscalar =>
    do
    let i3 ← lift (IScalar.cast .I128 sa)
    let i4 ← lift (IScalar.cast .I128 sb)
    let i5 ← i3 - i4
    runtime.interp.simd.sat i5 width true
  | 19#uscalar =>
    do
    let i3 ← lift (UScalar.hcast .I128 a)
    let i4 ← lift (UScalar.hcast .I128 b)
    let i5 ← i3 - i4
    runtime.interp.simd.sat i5 width false
  | 21#uscalar => Result.ok (core.num.U64.wrapping_mul a b)
  | 22#uscalar => if sa < sb
                  then Result.ok a
                  else Result.ok b
  | 23#uscalar => if a < b
                  then Result.ok a
                  else Result.ok b
  | 24#uscalar => if sa > sb
                  then Result.ok a
                  else Result.ok b
  | 25#uscalar => if a > b
                  then Result.ok a
                  else Result.ok b
  | _ => do
         let i3 ← a + b
         let i4 ← i3 + 1#u64
         i4 / 2#u64
theorem integer_binary_loop
    (x y initial : U128) (width op i : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (R : Nat → BitVec width.val → Prop)
    (wordLaw : ∀ j, j < 128/width.val → ∀ (a b : U64) (sa sb : I64) (remainder : U32),
      a.val = (laneBits width.val j x.bv).toNat →
      b.val = (laneBits width.val j y.bv).toNat →
      sa.val = (a.bv.setWidth width.val).toInt →
      sb.val = (b.bv.setWidth width.val).toInt →
      remainder.val = op.val%32 →
      integerBinaryWord remainder width a b sa sb ⦃ value => R j (value.bv.setWidth width.val) ⦄)
    (position : i.val ≤ 128/width.val)
    (initializedPrefix : ∀ j, j < i.val → R j (laneBits width.val j initial.bv)) :
    runtime.interp.simd.integer_binary_lanes_loop op x y width initial i ⦃ result =>
      ∀ j, j < 128/width.val → R j (laneBits width.val j result.bv) ⦄ := by
  unfold runtime.interp.simd.integer_binary_lanes_loop
  apply loop.spec_decr_nat (fun p => 128/width.val-p.2.val)
    (fun p => p.2.val ≤ 128/width.val ∧ ∀ j, j < p.2.val → R j (laneBits width.val j p.1.bv))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.integer_binary_lanes_loop.body
    dsimp only
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 128/width.val := by scalar_tac
      have range := lane_range width.val index.val less
      step with lane x width index positive widthBound (by omega) as ⟨a,aEq⟩
      have aBits : a.val = (laneBits width.val index.val x.bv).toNat := by
        rw [laneBits_toNat]
        exact aEq
      step with lane y width index positive widthBound (by omega) as ⟨b,bEq⟩
      have bBits : b.val = (laneBits width.val index.val y.bv).toNat := by
        rw [laneBits_toNat]
        exact bEq
      step with signed a width positive widthBound as ⟨sa,saEq⟩
      step with signed b width positive widthBound as ⟨sb,sbEq⟩
      step as ⟨remainder,remainderEq⟩
      with_unfolding_all change (Aeneas.Std.bind (integerBinaryWord remainder width a b sa sb) _) ⦃ _ ⦄
      step with wordLaw index.val less a b sa sb remainder aBits bBits saEq sbEq remainderEq as ⟨value,allowed⟩
      step with put_lanes current width index value positive widthBound range as ⟨updated,same,other⟩
      have countBound : 128/width.val ≤ 128 := Nat.div_le_self _ _
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; rw [same]; exact allowed
        · rw [other j (lane_range _ _ (by omega)) eq]
          exact initialized j (by omega)
      · omega
    · have finished : index.val = 128/width.val := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩

end Exec.Interp.Simd

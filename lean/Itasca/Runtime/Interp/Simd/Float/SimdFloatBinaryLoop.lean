import Itasca.Runtime.Interp.Simd.Common.SimdSplat
import Itasca.Runtime.Interp.Simd.Common.SimdPacking
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def floatBinaryWord {F : Type} (floats : runtime.platform.FloatOps F) (width bin : U32) (a b : U64) :
    Result U64 :=
  if bin >= 6#u32 then do
    let choose ← if bin = 6#u32 then runtime.interp.float.compare_float 2#u16 b a width
      else runtime.interp.float.compare_float 2#u16 a b width
    if choose then Result.ok b else Result.ok a
  else if width = 32#u32 then do
    let index ← lift (UScalar.cast .U16 bin)
    let first ← lift (UScalar.cast .U32 a)
    let second ← lift (UScalar.cast .U32 b)
    let result ← runtime.interp.float.binary32 floats index first second
    Result.ok (UScalar.cast .U64 result)
  else do
    let index ← lift (UScalar.cast .U16 bin)
    runtime.interp.float.binary64 floats index a b

theorem float_binary_loop {F : Type} (floats : runtime.platform.FloatOps F)
    (x y initial : U128) (width bin i : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (R : Nat → BitVec width.val → Prop)
    (wordLaw : ∀ j, j < 128/width.val → ∀ a b : U64,
      a.val = (laneBits width.val j x.bv).toNat →
      b.val = (laneBits width.val j y.bv).toNat →
      floatBinaryWord floats width bin a b ⦃ value => R j (value.bv.setWidth width.val) ⦄)
    (position : i.val ≤ 128/width.val)
    (initializedPrefix : ∀ j, j < i.val → R j (laneBits width.val j initial.bv)) :
    runtime.interp.simd.float_binary_lanes_loop floats x y width bin initial i ⦃ result =>
      ∀ j, j < 128/width.val → R j (laneBits width.val j result.bv) ⦄ := by
  unfold runtime.interp.simd.float_binary_lanes_loop
  apply loop.spec_decr_nat (fun p => 128/width.val-p.2.val)
    (fun p => p.2.val ≤ 128/width.val ∧ ∀ j, j < p.2.val → R j (laneBits width.val j p.1.bv))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.float_binary_lanes_loop.body
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
      with_unfolding_all change (Aeneas.Std.bind (floatBinaryWord floats width bin a b) _) ⦃ _ ⦄
      step with wordLaw index.val less a b aBits bBits as ⟨value,allowed⟩
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

end Itasca.Runtime.Interp.Simd

import Itasca.Runtime.Interp.Simd.Lanes.LaneBits

/-!
Lane bounds and runtime scalar splatting.

Main declarations: `lane_range` and `splat`. A direct consumer is `Interp.Simd.Float.Binary`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem lane_range (width index : Nat) (bound : index < 128/width) :
    width*index+width ≤ 128 := by
  have order := Nat.mul_le_mul_left width bound
  have limit := Nat.mul_div_le 128 width
  rw [Nat.mul_succ] at order
  omega

@[step] theorem splat_loop (x : U64) (width : U32) (initial : U128) (i : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (position : i.val ≤ 128/width.val)
    (initializedPrefix : ∀ j, j < i.val → laneBits width.val j initial.bv = x.bv.setWidth width.val) :
    runtime.interp.simd.splat_loop x width initial i ⦃ result =>
      ∀ j, j < 128/width.val → laneBits width.val j result.bv = x.bv.setWidth width.val ⦄ := by
  unfold runtime.interp.simd.splat_loop
  apply loop.spec_decr_nat (fun p => 128/width.val-p.2.val)
    (fun p => p.2.val ≤ 128/width.val ∧
      ∀ j, j < p.2.val → laneBits width.val j p.1.bv = x.bv.setWidth width.val)
  · rintro ⟨current, index⟩ ⟨indexBound, initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.splat_loop.body
    dsimp only
    step as ⟨count, countEq⟩
    split
    · rename_i more
      have less : index.val < 128/width.val := by scalar_tac
      have range := lane_range width.val index.val less
      step with put_lanes current width index x positive widthBound range as ⟨updated, same, other⟩
      have countBound : 128/width.val ≤ 128 := Nat.div_le_self _ _
      step as ⟨next, nextEq⟩
      refine ⟨?_, ?_, ?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; exact same
        · rw [other j (lane_range _ _ (by omega)) eq]
          exact initialized j (by omega)
      · omega
    · have finished : index.val = 128/width.val := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position, initializedPrefix⟩

@[step] theorem splat (x : U64) (width : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64) :
    runtime.interp.simd.splat x width ⦃ result =>
      ∀ j, j < 128/width.val → laneBits width.val j result.bv = x.bv.setWidth width.val ⦄ := by
  exact splat_loop x width 0#u128 0#u32 positive widthBound (by simp) (by simp)

end Itasca.Runtime.Interp.Simd

import Exec.Interp.Simd.Float.SimdFloatResizeFirstWord
import Exec.Interp.Simd.Float.SimdFloatResizeLanes
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd SpecExt.Builtins SpecExt.Builtins.Float Platform

@[step] theorem float_resize_lanes_first {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (kind : FloatResize) (x : U128) :
    runtime.interp.simd.convert_lanes floats (floatResizeOpcode kind) x
      ⦃ result => ∃ value, result = .Ok value ∧
        (∀ j, j < 2 →
          (floatResizeChoices kind (floatOfBits (lsize (lanetype_Fnn kind.input))
              (laneBits (lsize (lanetype_Fnn kind.input)) j x.bv).toNat)).head? =
            some (floatOfBits (lsize (lanetype_Fnn kind.output)) (laneBits (lsize (lanetype_Fnn kind.output)) j value.bv).toNat)) ∧
        (∀ j, 2 ≤ j → j < 128/lsize (lanetype_Fnn kind.output) → laneBits (lsize (lanetype_Fnn kind.output)) j value.bv = 0) ⦄ := by
  rw [float_resize_dispatch_eq]
  have inputEq := floatCompareWidth_val kind.input
  have outputEq := floatCompareWidth_val kind.output
  have spec := float_resize_loop floats kind x 0#u128 0#u32
    (fun j bits => (floatResizeChoices kind (floatOfBits (lsize (lanetype_Fnn kind.input))
        (laneBits (lsize (lanetype_Fnn kind.input)) j x.bv).toNat)).head? =
      some (floatOfBits (floatCompareWidth kind.output).val bits.toNat))
    (by
      intro j valid a aEq
      have aBits : a.val = (laneBits (lsize (lanetype_Fnn kind.input)) j x.bv).toNat := by
        cases kind <;> with_unfolding_all exact aEq
      apply WP.spec_mono (float_resize_word_first floats laws kind a (by rw [aBits]; exact BitVec.isLt _))
      rintro value ⟨chosen,bound⟩
      rw [outputEq]
      have valueNat : (value.bv.setWidth (lsize (lanetype_Fnn kind.output))).toNat = value.val := by
        rw [BitVec.toNat_setWidth]
        exact Nat.mod_eq_of_lt bound
      rw [valueNat]
      simpa only [aBits] using chosen)
    (by simp) (by simp) (by intro j above bound; simp [laneBits])
  cases kind <;> with_unfolding_all exact spec

end Exec.Interp.Simd

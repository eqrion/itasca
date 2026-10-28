import Itasca.Runtime.Interp.Simd.Float.SimdFloatResizeWord
import Itasca.Runtime.Interp.Simd.Integer.SimdIntegerArithmeticLanes
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def floatResizeOpcode : FloatResize → U32 | .demote => 94#u32 | .promote => 95#u32

theorem float_resize_body_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (kind : FloatResize) (x current : U128) (index : U32) :
    runtime.interp.simd.convert_lanes_loop.body floats (floatResizeOpcode kind) x 2#u32 current index =
      (if index < 2#u32 then do
        let a ← runtime.interp.simd.lane x (floatCompareWidth kind.input) index
        let value ← floatResizeWord floats kind a
        let updated ← runtime.interp.simd.put current (floatCompareWidth kind.output) index value
        let next ← index + 1#u32
        Result.ok (ControlFlow.cont (updated,next))
      else do
        Result.ok (ControlFlow.done (core.result.Result.Ok current))) := by
  cases kind
  all_goals unfold runtime.interp.simd.convert_lanes_loop.body floatResizeOpcode
  all_goals with_unfolding_all simp only [floatResizeWord,floatCompareWidth,lift,bind_ok,Std.bind_assoc]
  all_goals with_unfolding_all rfl

theorem float_resize_loop {F : Type} (floats : runtime.platform.FloatOps F)
    (kind : FloatResize) (x initial : U128) (i : U32)
    (R : Nat → BitVec (floatCompareWidth kind.output).val → Prop)
    (wordLaw : ∀ j, j < 2 → ∀ a : U64,
      a.val = (laneBits (floatCompareWidth kind.input).val j x.bv).toNat →
      floatResizeWord floats kind a ⦃ value => R j (value.bv.setWidth (floatCompareWidth kind.output).val) ⦄)
    (position : i.val ≤ 2)
    (initializedPrefix : ∀ j, j < i.val → R j (laneBits (floatCompareWidth kind.output).val j initial.bv))
    (initializedSuffix : ∀ j, 2 ≤ j → j < 128/(floatCompareWidth kind.output).val →
      laneBits (floatCompareWidth kind.output).val j initial.bv = 0) :
    runtime.interp.simd.convert_lanes_loop floats (floatResizeOpcode kind) x initial i 2#u32
      ⦃ result => ∃ value, result = .Ok value ∧
        (∀ j, j < 2 → R j (laneBits (floatCompareWidth kind.output).val j value.bv)) ∧
        (∀ j, 2 ≤ j → j < 128/(floatCompareWidth kind.output).val →
          laneBits (floatCompareWidth kind.output).val j value.bv = 0) ⦄ := by
  have inputPositive : 0 < (floatCompareWidth kind.input).val := by cases kind <;> decide
  have inputBound : (floatCompareWidth kind.input).val ≤ 64 := by cases kind <;> decide
  have outputPositive : 0 < (floatCompareWidth kind.output).val := by cases kind <;> decide
  have outputBound : (floatCompareWidth kind.output).val ≤ 64 := by cases kind <;> decide
  have outputCount : 2 ≤ 128/(floatCompareWidth kind.output).val := by cases kind <;> decide
  unfold runtime.interp.simd.convert_lanes_loop
  apply loop.spec_decr_nat (fun p => 2-p.2.val)
    (fun p => p.2.val ≤ 2 ∧
      (∀ j, j < p.2.val → R j (laneBits (floatCompareWidth kind.output).val j p.1.bv)) ∧
      (∀ j, 2 ≤ j → j < 128/(floatCompareWidth kind.output).val → laneBits (floatCompareWidth kind.output).val j p.1.bv = 0))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized,zeroed⟩
    dsimp only at indexBound initialized zeroed
    dsimp only
    simp only [float_resize_body_eq]
    split
    · rename_i more
      have less : index.val < 2 := by scalar_tac
      have readRange : (floatCompareWidth kind.input).val*index.val < 128 := by
        cases kind <;> simp only [FloatResize.input,floatCompareWidth] <;> scalar_tac
      step with lane x (floatCompareWidth kind.input) index inputPositive inputBound readRange as ⟨a,aEq⟩
      have aBits : a.val = (laneBits (floatCompareWidth kind.input).val index.val x.bv).toNat := by
        rw [laneBits_toNat]; exact aEq
      step with wordLaw index.val less a aBits as ⟨value,allowed⟩
      step with put_lanes current (floatCompareWidth kind.output) index value outputPositive outputBound
        (lane_range _ _ (by omega)) as ⟨updated,same,other⟩
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; rw [same]; exact allowed
        · rw [other j (lane_range _ _ (by omega)) eq]; exact initialized j (by omega)
      · intro j above bound
        rw [other j (lane_range _ _ bound) (by omega)]
        exact zeroed j above bound
      · omega
    · have finished : index.val = 2 := by scalar_tac
      exact ⟨current,rfl,by simpa [finished] using initialized,zeroed⟩
  · exact ⟨position,initializedPrefix,initializedSuffix⟩

end Itasca.Runtime.Interp.Simd

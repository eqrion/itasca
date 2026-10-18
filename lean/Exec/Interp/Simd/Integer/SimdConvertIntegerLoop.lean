import Exec.Interp.Simd.Integer.SimdConvertIntegerWord
import Exec.Interp.Simd.Integer.SimdIntegerArithmeticLanes
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd

def convertIntegerOpcode (ty : Fnn) (signed : Bool) : U32 :=
  match ty,signed with
  | .F32,true => 250#u32 | .F32,false => 251#u32
  | .F64,true => 254#u32 | .F64,false => 255#u32

theorem convert_integer_body_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool) (x current : U128) (index count : U32) :
    runtime.interp.simd.convert_lanes_loop.body floats (convertIntegerOpcode ty signed) x count current index =
      (if index < count then do
        let a ← runtime.interp.simd.lane x 32#u32 index
        let value ← convertIntegerWord floats ty signed a
        let updated ← runtime.interp.simd.put current (floatCompareWidth ty) index value
        let next ← index + 1#u32
        Result.ok (ControlFlow.cont (updated,next))
      else do
        let result ← runtime.interp.simd.vector current
        Result.ok (ControlFlow.done (core.result.Result.Ok result))) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.convert_lanes_loop.body convertIntegerOpcode
  all_goals with_unfolding_all simp only [convertIntegerWord,floatCompareWidth,lift,bind_ok,Std.bind_assoc]
  all_goals with_unfolding_all rfl

theorem convert_integer_loop {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool) (x initial : U128) (i count : U32)
    (countEq : count.val = 128/(floatCompareWidth ty).val)
    (R : Nat → BitVec (floatCompareWidth ty).val → Prop)
    (wordLaw : ∀ j, j < count.val → ∀ a : U64,
      a.val = (laneBits 32 j x.bv).toNat →
      convertIntegerWord floats ty signed a ⦃ value => R j (value.bv.setWidth (floatCompareWidth ty).val) ⦄)
    (position : i.val ≤ count.val)
    (initializedPrefix : ∀ j, j < i.val → R j (laneBits (floatCompareWidth ty).val j initial.bv)) :
    runtime.interp.simd.convert_lanes_loop floats (convertIntegerOpcode ty signed) x initial i count
      ⦃ result => ∃ value, result = .Ok value ∧
        ∀ j, j < count.val → R j (laneBits (floatCompareWidth ty).val j value.bv) ⦄ := by
  have positive : 0 < (floatCompareWidth ty).val := by cases ty <;> decide
  have widthBound : (floatCompareWidth ty).val ≤ 64 := by cases ty <;> decide
  have countBound : count.val ≤ 4 := by cases ty <;> simp only [floatCompareWidth] at countEq <;> scalar_tac
  unfold runtime.interp.simd.convert_lanes_loop
  apply loop.spec_decr_nat (fun p => count.val-p.2.val)
    (fun p => p.2.val ≤ count.val ∧ ∀ j, j < p.2.val → R j (laneBits (floatCompareWidth ty).val j p.1.bv))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    dsimp only
    simp only [convert_integer_body_eq]
    split
    · rename_i more
      have less : index.val < count.val := by scalar_tac
      step with lane x 32#u32 index (by decide) (by decide) (by scalar_tac) as ⟨a,aEq⟩
      have aBits : a.val = (laneBits 32 index.val x.bv).toNat := by
        rw [laneBits_toNat]; exact aEq
      step with wordLaw index.val less a aBits as ⟨value,allowed⟩
      have range := lane_range (floatCompareWidth ty).val index.val (by omega : index.val < 128/(floatCompareWidth ty).val)
      step with put_lanes current (floatCompareWidth ty) index value positive widthBound range as ⟨updated,same,other⟩
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; rw [same]; exact allowed
        · rw [other j (lane_range _ _ (by omega)) eq]; exact initialized j (by omega)
      · omega
    · have finished : index.val = count.val := by scalar_tac
      unfold runtime.interp.simd.vector
      simp only [bind_ok]
      exact ⟨current,rfl,by simpa [finished] using initialized⟩
  · exact ⟨position,initializedPrefix⟩

end Exec.Interp.Simd

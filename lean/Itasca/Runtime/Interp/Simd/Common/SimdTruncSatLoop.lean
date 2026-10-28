import Itasca.Runtime.Interp.Simd.Common.SimdTruncSatWord
import Itasca.Runtime.Interp.Simd.Integer.SimdIntegerArithmeticLanes
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def truncSatOpcode (ty : Fnn) (signed : Bool) : U32 :=
  match ty,signed with
  | .F32,true => 248#u32 | .F32,false => 249#u32
  | .F64,true => 252#u32 | .F64,false => 253#u32

theorem trunc_sat_body_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool) (x current : U128) (index count : U32) :
    runtime.interp.simd.convert_lanes_loop.body floats (truncSatOpcode ty signed) x count current index =
      (if index < count then do
        let a ← runtime.interp.simd.lane x (floatCompareWidth ty) index
        let outcome ← runtime.interp.float.trunc_int a (ty == .F32) 32#u32 signed true
        let cf ← core.result.Result.Insts.CoreOpsTry.branch outcome
        match cf with
        | core.ops.control_flow.ControlFlow.Continue value =>
          let updated ← runtime.interp.simd.put current 32#u32 index value
          let next ← index + 1#u32
          Result.ok (ControlFlow.cont (updated,next))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual U128
            (core.convert.FromSame runtime.ExecError) residual
          Result.ok (ControlFlow.done r)
      else do
        Result.ok (ControlFlow.done (core.result.Result.Ok current))) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.convert_lanes_loop.body truncSatOpcode
  all_goals with_unfolding_all rfl

theorem trunc_sat_loop {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool) (x initial : U128) (i count : U32)
    (countEq : count.val = 128/(floatCompareWidth ty).val)
    (R : Nat → BitVec 32 → Prop)
    (wordLaw : ∀ j, j < count.val → ∀ a : U64,
      a.val = (laneBits (floatCompareWidth ty).val j x.bv).toNat →
      runtime.interp.float.trunc_int a (ty == .F32) 32#u32 signed true
        ⦃ result => ∃ value, result = .Ok value ∧ R j (value.bv.setWidth 32) ⦄)
    (position : i.val ≤ count.val)
    (initializedPrefix : ∀ j, j < i.val → R j (laneBits 32 j initial.bv))
    (initializedSuffix : ∀ j, count.val ≤ j → j < 4 → laneBits 32 j initial.bv = 0) :
    runtime.interp.simd.convert_lanes_loop floats (truncSatOpcode ty signed) x initial i count
      ⦃ result => ∃ value, result = .Ok value ∧
        (∀ j, j < count.val → R j (laneBits 32 j value.bv)) ∧
        (∀ j, count.val ≤ j → j < 4 → laneBits 32 j value.bv = 0) ⦄ := by
  have positive : 0 < (floatCompareWidth ty).val := by cases ty <;> decide
  have widthBound : (floatCompareWidth ty).val ≤ 64 := by cases ty <;> decide
  have countBound : count.val ≤ 4 := by cases ty <;> simp only [floatCompareWidth] at countEq <;> scalar_tac
  unfold runtime.interp.simd.convert_lanes_loop
  apply loop.spec_decr_nat (fun p => count.val-p.2.val)
    (fun p => p.2.val ≤ count.val ∧
      (∀ j, j < p.2.val → R j (laneBits 32 j p.1.bv)) ∧
      (∀ j, count.val ≤ j → j < 4 → laneBits 32 j p.1.bv = 0))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized,zeroed⟩
    dsimp only at indexBound initialized zeroed
    dsimp only
    simp only [trunc_sat_body_eq]
    split
    · rename_i more
      have less : index.val < count.val := by scalar_tac
      have range := lane_range (floatCompareWidth ty).val index.val (by omega : index.val < 128/(floatCompareWidth ty).val)
      step with lane x (floatCompareWidth ty) index positive widthBound (by omega) as ⟨a,aEq⟩
      have aBits : a.val = (laneBits (floatCompareWidth ty).val index.val x.bv).toNat := by
        rw [laneBits_toNat]; exact aEq
      step with wordLaw index.val less a aBits as ⟨outcome,value,eq,allowed⟩
      subst outcome
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      step with put_lanes current 32#u32 index value (by decide) (by decide) (by scalar_tac) as ⟨updated,same,other⟩
      change laneBits 32 index.val updated.bv = value.bv.setWidth 32 at same
      change ∀ j, 32*j+32 ≤ 128 → j ≠ index.val → laneBits 32 j updated.bv = laneBits 32 j current.bv at other
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; rw [same]; exact allowed
        · rw [other j (by omega) eq]; exact initialized j (by omega)
      · intro j above bound
        rw [other j (by omega) (by omega)]
        exact zeroed j above bound
      · omega
    · have finished : index.val = count.val := by scalar_tac
      exact ⟨current,rfl,by simpa [finished] using initialized,zeroed⟩
  · exact ⟨position,initializedPrefix,initializedSuffix⟩

end Itasca.Runtime.Interp.Simd

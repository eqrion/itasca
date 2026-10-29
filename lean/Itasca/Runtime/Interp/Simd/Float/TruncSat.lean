import Itasca.Runtime.Spec.Simd.TruncSat
import Itasca.Runtime.Interp.Numeric.Float.FloatTrunc32
import Itasca.Runtime.Interp.Numeric.Float.FloatTrunc64
import Itasca.Runtime.Interp.Simd.Float.CompareLanes
import Itasca.Runtime.Interp.Simd.Integer.ArithmeticLanes

/-!
Saturating lane truncation: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Trunc Sat Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins SpecExt.Builtins.Float

theorem trunc_outcome_some (word : uN) (result : core.result.Result U64 runtime.ExecError)
    (effect : TruncOutcome (some word) result) :
    ∃ value, result = .Ok value ∧ .mk_uN value.val = word := by
  cases result with
  | Ok value => exact ⟨value,rfl,(Option.some.inj effect).symm⟩
  | Err error => cases error <;> simp [TruncOutcome] at effect

@[step] theorem trunc_sat_word (ty : Fnn) (signed : Bool) (a : U64)
    (bound : a.val < 2^(lsize (lanetype_Fnn ty))) :
    runtime.interp.float.trunc_int a (ty == .F32) 32#u32 signed true ⦃ result =>
      ∃ value, result = .Ok value ∧
        uN.mk_uN value.val = truncSatWord (lsize (lanetype_Fnn ty)) (if signed then .S else .U)
          (floatOfBits (lsize (lanetype_Fnn ty)) a.val) ∧ value.val < 2^32 ⦄ := by
  have relation : runtime.interp.float.trunc_int a (ty == .F32) 32#u32 signed true ⦃ result =>
      TruncOutcome (trunc_sat__ (lsize (lanetype_Fnn ty)) 32 (if signed then .S else .U)
        (floatOfBits (lsize (lanetype_Fnn ty)) a.val)) result ⦄ := by
    cases ty
    · have castEq : (UScalar.cast .U32 a).val = a.val := by
        with_unfolding_all change a.val % 2^32 = a.val
        exact Nat.mod_eq_of_lt bound
      have h := trunc_int32_sound a 32#u32 signed true (Or.inl rfl)
      simp only [castEq,↓reduceIte] at h
      with_unfolding_all exact h
    · exact trunc_int64_sound a 32#u32 signed true (Or.inl rfl)
  apply WP.spec_mono relation
  intro result effect
  rw [trunc_sat_word_some] at effect
  obtain ⟨value,rfl,word⟩ := trunc_outcome_some _ result effect
  refine ⟨value,rfl,word,?_⟩
  have bound := trunc_sat_word_bound (lsize (lanetype_Fnn ty)) (if signed then .S else .U) (floatOfBits (lsize (lanetype_Fnn ty)) a.val)
  rw [←word] at bound
  exact bound

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Trunc Sat Loop -/

section

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

end

/-! ## Simd Trunc Sat Lanes -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins SpecExt.Builtins.Float

def truncSatCountU32 : Fnn → U32 | .F32 => 4#u32 | .F64 => 2#u32

theorem trunc_sat_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool) (x : U128) :
    runtime.interp.simd.convert_lanes floats (truncSatOpcode ty signed) x =
      runtime.interp.simd.convert_lanes_loop floats (truncSatOpcode ty signed) x 0#u128 0#u32 (truncSatCountU32 ty) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.convert_lanes truncSatOpcode truncSatCountU32
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals simp only [bind_ok]

@[step] theorem trunc_sat_lanes {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool) (x : U128) :
    runtime.interp.simd.convert_lanes floats (truncSatOpcode ty signed) x
      ⦃ result => ∃ value, result = .Ok value ∧
        (∀ j, j < truncSatCount ty →
          uN.mk_uN (laneBits 32 j value.bv).toNat = truncSatWord (lsize (lanetype_Fnn ty))
            (if signed then .S else .U)
            (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat)) ∧
        (∀ j, truncSatCount ty ≤ j → j < 4 → laneBits 32 j value.bv = 0) ⦄ := by
  rw [trunc_sat_dispatch_eq]
  have widthEq := floatCompareWidth_val ty
  have countEq : (truncSatCountU32 ty).val = 128/(floatCompareWidth ty).val := by cases ty <;> decide
  have spec := trunc_sat_loop floats ty signed x 0#u128 0#u32 (truncSatCountU32 ty) countEq
    (fun j bits => uN.mk_uN bits.toNat = truncSatWord (lsize (lanetype_Fnn ty)) (if signed then .S else .U)
      (floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat))
    (by
      intro j valid a aEq
      have aBits : a.val = (laneBits (lsize (lanetype_Fnn ty)) j x.bv).toNat := by
        cases ty <;> with_unfolding_all exact aEq
      apply WP.spec_mono (trunc_sat_word ty signed a (by rw [aBits]; exact BitVec.isLt _))
      rintro out ⟨value,rfl,chosen,bound⟩
      refine ⟨value,rfl,?_⟩
      have valueNat : (value.bv.setWidth 32).toNat = value.val := by
        rw [BitVec.toNat_setWidth]
        exact Nat.mod_eq_of_lt bound
      rw [valueNat,chosen,aBits])
    (by simp) (by simp) (by intro j above bound; simp [laneBits])
  cases ty <;> with_unfolding_all exact spec

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Trunc Sat Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Platform

@[step] theorem trunc_sat_lanes_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool) (x : U128) :
    runtime.interp.simd.convert_lanes floats (truncSatOpcode ty signed) x ⦃ out =>
      ∃ result, out = .Ok result ∧
      Step_pure [.VCONST .V128 (.mk_uN x.val),
        .VCVTOP (Spec.Simd.shapeOf .I32) (Spec.Simd.shapeOf (lanetype_Fnn ty))
          (Spec.Simd.truncSatSource ty (if signed then .S else .U))]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (trunc_sat_lanes floats ty signed x)
  rintro out ⟨result,rfl,allowed,zeroed⟩
  exact ⟨result,rfl,Spec.Simd.trunc_sat_step ty (if signed then .S else .U) x.bv result.bv allowed zeroed⟩

theorem trunc_sat_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (truncSatOpcode ty signed) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.convert_lanes floats (truncSatOpcode ty signed) x)
        (fun result => Result.ok (result,memory)) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.simd truncSatOpcode
  all_goals with_unfolding_all rfl

@[step] theorem trunc_sat_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (truncSatOpcode ty signed) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),
          .VCVTOP (Spec.Simd.shapeOf .I32) (Spec.Simd.shapeOf (lanetype_Fnn ty))
            (Spec.Simd.truncSatSource ty (if signed then .S else .U))]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [trunc_sat_simd_eq]
  step with trunc_sat_lanes_sound floats ty signed x as ⟨out,value,eq,source⟩
  subst out
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end

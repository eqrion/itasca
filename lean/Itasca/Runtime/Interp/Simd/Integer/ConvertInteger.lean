import Itasca.Runtime.Interp.Numeric.Float
import Itasca.Runtime.Interp.Simd.Float.CompareLanes
import Itasca.Runtime.Interp.Simd.Integer.ArithmeticLanes
import Itasca.Runtime.Spec.Simd.ConvertInteger

/-!
Integer-to-floating-point lane conversion: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Convert Integer Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins SpecExt.Builtins.Float Platform

def convertIntegerWord {F : Type} (floats : runtime.platform.FloatOps F) (ty : Fnn) (signed : Bool) (a : U64) : Result U64 := do
  match ty,signed with
  | .F32,true =>
    let raw ← floats.f32_convert_i32_s (UScalar.hcast .I32 a)
    let value ← runtime.interp.float.quiet32 raw
    Result.ok (UScalar.cast .U64 value)
  | .F32,false =>
    let raw ← floats.f32_convert_i32_u (UScalar.cast .U32 a)
    let value ← runtime.interp.float.quiet32 raw
    Result.ok (UScalar.cast .U64 value)
  | .F64,true =>
    let raw ← floats.f64_convert_i32_s (UScalar.hcast .I32 a)
    runtime.interp.float.quiet64 raw
  | .F64,false =>
    let raw ← floats.f64_convert_i32_u (UScalar.cast .U32 a)
    runtime.interp.float.quiet64 raw

@[step] theorem convert_integer_word {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (signed : Bool) (a : U64) (bound : a.val < 2^32) :
    convertIntegerWord floats ty signed a ⦃ result =>
      floatOfBits (lsize (lanetype_Fnn ty)) result.val =
        convert__ 32 (lsize (lanetype_Fnn ty)) (if signed then .S else .U) (.mk_uN a.val) ∧
      result.val < 2^(lsize (lanetype_Fnn ty)) ⦄ := by
  have unsigned : (UScalar.cast .U32 a).val = a.val := by
    with_unfolding_all change a.val % 2^32 = a.val
    exact Nat.mod_eq_of_lt bound
  have signedRound : (IScalar.hcast .U32 (UScalar.hcast .I32 a)).val = a.val := by
    with_unfolding_all change ((a.bv.setWidth 32).signExtend 32).toNat = a.val
    rw [BitVec.signExtend_eq]
    exact unsigned
  cases ty <;> cases signed <;> unfold convertIntegerWord
  all_goals simp only [lanetype_Fnn,lsize,size,valtype_numtype,Option.get!_some]
  · step with laws.f32_convert_i32_u (UScalar.cast .U32 a) as ⟨raw,allowed⟩
    step with quiet32_sound raw _ allowed (canonicalClosed_convert 32 32 (by omega) _ _) as ⟨value,chosen⟩
    exact ⟨by simpa [U32.cast_U64_val_eq,unsigned] using chosen,by with_unfolding_all exact value.bv.isLt⟩
  · step with laws.f32_convert_i32_s (UScalar.hcast .I32 a) as ⟨raw,allowed⟩
    step with quiet32_sound raw _ allowed (canonicalClosed_convert 32 32 (by omega) _ _) as ⟨value,chosen⟩
    exact ⟨by simpa [U32.cast_U64_val_eq,signedRound] using chosen,by with_unfolding_all exact value.bv.isLt⟩
  · step with laws.f64_convert_i32_u (UScalar.cast .U32 a) as ⟨raw,allowed⟩
    step with quiet64_sound raw _ allowed (canonicalClosed_convert 32 64 (by omega) _ _) as ⟨value,chosen⟩
    exact ⟨by simpa [unsigned] using chosen,by with_unfolding_all exact value.bv.isLt⟩
  · step with laws.f64_convert_i32_s (UScalar.hcast .I32 a) as ⟨raw,allowed⟩
    step with quiet64_sound raw _ allowed (canonicalClosed_convert 32 64 (by omega) _ _) as ⟨value,chosen⟩
    exact ⟨by simpa [signedRound] using chosen,by with_unfolding_all exact value.bv.isLt⟩

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Convert Integer Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

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
        Result.ok (ControlFlow.done (core.result.Result.Ok current))) := by
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
        rw [lane_bits_to_nat]; exact aEq
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
      exact ⟨current,rfl,by simpa [finished] using initialized⟩
  · exact ⟨position,initializedPrefix⟩

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Convert Integer Lanes -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins SpecExt.Builtins.Float Platform

def convertIntegerCountU32 : Fnn → U32 | .F32 => 4#u32 | .F64 => 2#u32

theorem convert_integer_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool) (x : U128) :
    runtime.interp.simd.convert_lanes floats (convertIntegerOpcode ty signed) x =
      runtime.interp.simd.convert_lanes_loop floats (convertIntegerOpcode ty signed) x 0#u128 0#u32 (convertIntegerCountU32 ty) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.convert_lanes convertIntegerOpcode convertIntegerCountU32
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals simp only [bind_ok]

@[step] theorem convert_integer_lanes {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (signed : Bool) (x : U128) :
    runtime.interp.simd.convert_lanes floats (convertIntegerOpcode ty signed) x
      ⦃ result => ∃ value, result = .Ok value ∧
        ∀ j, j < 128/lsize (lanetype_Fnn ty) →
          floatOfBits (lsize (lanetype_Fnn ty)) (laneBits (lsize (lanetype_Fnn ty)) j value.bv).toNat =
            convert__ 32 (lsize (lanetype_Fnn ty)) (if signed then .S else .U)
              (.mk_uN (laneBits 32 j x.bv).toNat) ⦄ := by
  rw [convert_integer_dispatch_eq]
  have widthEq := float_compare_width_val ty
  have countEq : (convertIntegerCountU32 ty).val = 128/(floatCompareWidth ty).val := by cases ty <;> decide
  have spec := convert_integer_loop floats ty signed x 0#u128 0#u32 (convertIntegerCountU32 ty) countEq
    (fun j bits => floatOfBits (floatCompareWidth ty).val bits.toNat =
      convert__ 32 (floatCompareWidth ty).val (if signed then .S else .U) (.mk_uN (laneBits 32 j x.bv).toNat))
    (by
      intro j valid a aEq
      apply WP.spec_mono (convert_integer_word floats laws ty signed a (by rw [aEq]; exact BitVec.isLt _))
      rintro value ⟨chosen,bound⟩
      rw [widthEq]
      have valueNat : (value.bv.setWidth (lsize (lanetype_Fnn ty))).toNat = value.val := by
        rw [BitVec.toNat_setWidth]
        exact Nat.mod_eq_of_lt bound
      rw [valueNat,chosen,aEq])
    (by simp) (by simp)
  cases ty <;> with_unfolding_all exact spec

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Convert Integer Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Platform

@[step] theorem convert_integer_lanes_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (signed : Bool) (x : U128) :
    runtime.interp.simd.convert_lanes floats (convertIntegerOpcode ty signed) x ⦃ out =>
      ∃ result, out = .Ok result ∧
      Step_pure [.VCONST .V128 (.mk_uN x.val),
        .VCVTOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.shapeOf .I32)
          (Spec.Simd.convertIntegerSource ty (if signed then .S else .U))]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (convert_integer_lanes floats laws ty signed x)
  rintro out ⟨result,rfl,allowed⟩
  exact ⟨result,rfl,Spec.Simd.convert_integer_step ty (if signed then .S else .U) x.bv result.bv allowed⟩

theorem convert_integer_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (convertIntegerOpcode ty signed) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.convert_lanes floats (convertIntegerOpcode ty signed) x)
        (fun result => Result.ok (result,memory)) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.simd convertIntegerOpcode
  all_goals with_unfolding_all rfl

@[step] theorem convert_integer_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (signed : Bool)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (convertIntegerOpcode ty signed) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),
          .VCVTOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.shapeOf .I32)
            (Spec.Simd.convertIntegerSource ty (if signed then .S else .U))]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [convert_integer_simd_eq]
  step with convert_integer_lanes_sound floats laws ty signed x as ⟨out,value,eq,source⟩
  subst out
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end

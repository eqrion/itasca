import Itasca.Runtime.Interp.Numeric.Float
import Itasca.Runtime.Interp.Simd.Float.TruncSat
import Itasca.Runtime.Interp.Simd.Integer.UnaryWords
import Itasca.Runtime.Spec.Simd.Pairwise
import Itasca.Runtime.Interp.Simd.Integer.CompareSigned

/-!
Sections, each formerly its own module: ConvertInteger, Saturation, Q15Word, Dot, Narrow, Pairwise, UnaryAll.
-/

/-! ## ConvertInteger -/

section

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

end

/-! ## Saturation -/

section

/-!
Runtime lane casts and saturation bounds.

Main declarations: `hcast_lane` and `saturate`. A direct consumer is `Interp.Simd.Integer.Narrow`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

theorem hcast_lane (x : I128) (width : Nat) (bound : width ≤ 64) :
    (IScalar.hcast .U64 x).bv.setWidth width = BitVec.ofInt width x.val := by
  rw [IScalar.hcast_bv_eq,BitVec.signExtend_eq_setWidth_of_le _ (by decide),UScalarTy.U64_numBits_eq,
    BitVec.setWidth_setWidth_of_le _ bound,
    ←BitVec.signExtend_eq_setWidth_of_le _ (by omega : width ≤ 128)]
  rfl

@[step] theorem saturate (x : I128) (width : U32) (signed : Bool)
    (supported : width.val ∈ [8,16,32]) :
    runtime.interp.simd.sat x width signed ⦃ result =>
      result.bv.setWidth width.val = BitVec.ofInt width.val (clampLane width.val signed x.val) ⦄ := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
  rcases supported with supported | supported | supported
  all_goals first
    | have eq : width = 8#u32 := UScalar.eq_of_val_eq supported
    | have eq : width = 16#u32 := UScalar.eq_of_val_eq supported
    | have eq : width = 32#u32 := UScalar.eq_of_val_eq supported
  all_goals subst width
  all_goals cases signed
  all_goals unfold runtime.interp.simd.sat
  all_goals simp only [Bool.false_eq_true,Bool.true_eq,↓reduceIte,bind_ok]
  all_goals step*
  all_goals try rw [hcast_lane _ _ (by decide)]
  all_goals simp_all [I128.size,I128.numBits,I128.min,I128.max,Int.bmod,Int.shiftLeft_eq,clampLane,IScalar.min,IScalar.lt_equiv]
  all_goals try omega
  all_goals split_ifs <;> (try simp_all) <;> omega

end Itasca.Runtime.Interp.Simd

end

/-! ## Q15Word -/

section

/-!
Word-level rounded saturating Q15 multiplication.

Main declarations: `q15Word`. A direct consumer is `Interp.Simd.Integer.Dot`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def q15Word (a b : I64) : Result U64 :=
  Aeneas.Std.bind (Aeneas.Std.bind (Aeneas.Std.bind (Aeneas.Std.bind (a * b)
    (fun product => product + 16384#i64))
    (fun rounded => rounded >>> 15#i32))
    (fun shifted => lift (IScalar.cast .I128 shifted)))
    (fun widened => runtime.interp.simd.sat widened 16#u32 true)

@[step] theorem q15_word (a b : I64)
    (aBound : -32768 ≤ a.val ∧ a.val < 32768)
    (bBound : -32768 ≤ b.val ∧ b.val < 32768) :
    q15Word a b ⦃ result => result.bv.setWidth 16 =
      BitVec.ofInt 16 (clampLane 16 true ((a.val*b.val+16384)/32768)) ⦄ := by
  have p1 := mul_nonneg (by omega : 0 ≤ a.val+32768) (by omega : 0 ≤ b.val+32768)
  have p2 := mul_nonneg (by omega : 0 ≤ 32768-a.val) (by omega : 0 ≤ 32768-b.val)
  have p3 := mul_nonneg (by omega : 0 ≤ a.val+32768) (by omega : 0 ≤ 32768-b.val)
  have p4 := mul_nonneg (by omega : 0 ≤ 32768-a.val) (by omega : 0 ≤ b.val+32768)
  have productBound : -1073741824 ≤ a.val*b.val ∧ a.val*b.val ≤ 1073741824 := by constructor <;> nlinarith
  unfold q15Word
  simp only [Std.bind_assoc]
  step* <;> simp_all [Int.shiftRight_eq_div_pow] <;> first | (with_unfolding_all assumption) | scalar_tac

end Itasca.Runtime.Interp.Simd

end

/-! ## Dot -/

section

/-!
Integer dot products: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Dot Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

@[step] theorem dot_mul (a b : I64)
    (aBound : -32768 ≤ a.val ∧ a.val < 32768)
    (bBound : -32768 ≤ b.val ∧ b.val < 32768) :
    a * b ⦃ result => result.val = a.val*b.val ∧
      -1073741824 ≤ result.val ∧ result.val ≤ 1073741824 ⦄ := by
  have p1 := mul_nonneg (by omega : 0 ≤ a.val+32768) (by omega : 0 ≤ b.val+32768)
  have p2 := mul_nonneg (by omega : 0 ≤ 32768-a.val) (by omega : 0 ≤ 32768-b.val)
  have p3 := mul_nonneg (by omega : 0 ≤ a.val+32768) (by omega : 0 ≤ 32768-b.val)
  have p4 := mul_nonneg (by omega : 0 ≤ 32768-a.val) (by omega : 0 ≤ b.val+32768)
  have productBound : -1073741824 ≤ a.val*b.val ∧ a.val*b.val ≤ 1073741824 := by constructor <;> nlinarith
  step* <;> scalar_tac

theorem dot_cast (x : I64) :
    (IScalar.hcast .U64 x).bv.setWidth 32 = BitVec.ofInt 32 x.val := by
  rw [IScalar.hcast_bv_eq]
  change (x.bv.signExtend 64).setWidth 32 = BitVec.ofInt 32 x.val
  rw [BitVec.signExtend_eq_setWidth_of_le _ (by decide : 64 ≤ 64)]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
  rw [← BitVec.signExtend_eq_setWidth_of_le _ (by decide : 32 ≤ 64)]
  rfl

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Dot Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

theorem dot_loop (x y initial : U128) (i : U32)
    (position : i.val ≤ 4)
    (initializedPrefix : ∀ j, j < i.val → laneBits 32 j initial.bv = dotBits x.bv y.bv j) :
    runtime.interp.simd.multiply_lanes_loop 186#u32 x y initial i ⦃ result =>
      ∀ j, j < 4 → laneBits 32 j result.bv = dotBits x.bv y.bv j ⦄ := by
  unfold runtime.interp.simd.multiply_lanes_loop
  apply loop.spec_decr_nat (fun p => 4-p.2.val)
    (fun p => p.2.val ≤ 4 ∧ ∀ j, j < p.2.val → laneBits 32 j p.1.bv = dotBits x.bv y.bv j)
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.multiply_lanes_loop.body
    simp only [show (186#u32 ≠ 130#u32) by decide, ↓reduceIte]
    split
    · rename_i more
      have less : index.val < 4 := by scalar_tac
      step as ⟨even,evenEq⟩
      step with lane x 16#u32 even (by decide) (by decide) (by scalar_tac) as ⟨a0,a0Eq⟩
      have a0Bits : a0.bv.setWidth 16 = laneBits 16 even.val x.bv :=
        lane_word_cast 16 _ _ a0 (by rw [lane_bits_to_nat]; exact a0Eq)
      step with signed a0 16#u32 (by decide) (by decide) as ⟨sa0,sa0Eq⟩
      have a0Bound : -32768 ≤ sa0.val ∧ sa0.val < 32768 := by
        rw [sa0Eq]; exact ⟨BitVec.le_toInt _,BitVec.toInt_lt⟩
      change sa0.val = (a0.bv.setWidth 16).toInt at sa0Eq
      rw [a0Bits] at sa0Eq
      step with lane y 16#u32 even (by decide) (by decide) (by scalar_tac) as ⟨b0,b0Eq⟩
      have b0Bits : b0.bv.setWidth 16 = laneBits 16 even.val y.bv :=
        lane_word_cast 16 _ _ b0 (by rw [lane_bits_to_nat]; exact b0Eq)
      step with signed b0 16#u32 (by decide) (by decide) as ⟨sb0,sb0Eq⟩
      have b0Bound : -32768 ≤ sb0.val ∧ sb0.val < 32768 := by
        rw [sb0Eq]; exact ⟨BitVec.le_toInt _,BitVec.toInt_lt⟩
      change sb0.val = (b0.bv.setWidth 16).toInt at sb0Eq
      rw [b0Bits] at sb0Eq
      step with dot_mul sa0 sb0 a0Bound b0Bound as ⟨p0,p0Eq,p0Lo,p0Hi⟩
      step as ⟨odd,oddEq⟩
      step with lane x 16#u32 odd (by decide) (by decide) (by scalar_tac) as ⟨a1,a1Eq⟩
      have a1Bits : a1.bv.setWidth 16 = laneBits 16 odd.val x.bv :=
        lane_word_cast 16 _ _ a1 (by rw [lane_bits_to_nat]; exact a1Eq)
      step with signed a1 16#u32 (by decide) (by decide) as ⟨sa1,sa1Eq⟩
      have a1Bound : -32768 ≤ sa1.val ∧ sa1.val < 32768 := by
        rw [sa1Eq]; exact ⟨BitVec.le_toInt _,BitVec.toInt_lt⟩
      change sa1.val = (a1.bv.setWidth 16).toInt at sa1Eq
      rw [a1Bits] at sa1Eq
      step as ⟨oddY,oddYEq⟩
      step with lane y 16#u32 oddY (by decide) (by decide) (by scalar_tac) as ⟨b1,b1Eq⟩
      have b1Bits : b1.bv.setWidth 16 = laneBits 16 oddY.val y.bv :=
        lane_word_cast 16 _ _ b1 (by rw [lane_bits_to_nat]; exact b1Eq)
      step with signed b1 16#u32 (by decide) (by decide) as ⟨sb1,sb1Eq⟩
      have b1Bound : -32768 ≤ sb1.val ∧ sb1.val < 32768 := by
        rw [sb1Eq]; exact ⟨BitVec.le_toInt _,BitVec.toInt_lt⟩
      change sb1.val = (b1.bv.setWidth 16).toInt at sb1Eq
      rw [b1Bits] at sb1Eq
      step with dot_mul sa1 sb1 a1Bound b1Bound as ⟨p1,p1Eq,p1Lo,p1Hi⟩
      step as ⟨total,totalEq⟩
      step as ⟨value,valueEq⟩
      have correct : value.bv.setWidth 32 = dotBits x.bv y.bv index.val := by
        rw [valueEq,dot_cast,dot_bits_int,totalEq,p0Eq,p1Eq,sa0Eq,sb0Eq,sa1Eq,sb1Eq]
        with_unfolding_all simp only [evenEq,oddEq,oddYEq]
        rfl
      step with put_lanes current 32#u32 index value (by decide) (by decide) (by scalar_tac) as ⟨updated,same,other⟩
      change laneBits 32 index.val updated.bv = value.bv.setWidth 32 at same
      change ∀ j, 32*j+32 ≤ 128 → j ≠ index.val → laneBits 32 j updated.bv = laneBits 32 j current.bv at other
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; rw [same]; exact correct
        · rw [other j (by omega) eq]; exact initialized j (by omega)
      · omega
    · have finished : index.val = 4 := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩

@[step] theorem dot_lanes (x y : U128) :
    runtime.interp.simd.multiply_lanes 186#u32 x y ⦃ result =>
      ∀ j, j < 4 → laneBits 32 j result.bv = dotBits x.bv y.bv j ⦄ := by
  unfold runtime.interp.simd.multiply_lanes
  apply WP.spec_mono (dot_loop x y 0#u128 0#u32 (by decide) (by simp))
  intro result lanes
  simpa using lanes

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Dot Packing -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem dot_packed (x y result : U128)
    (lanes : ∀ j, j < 4 → laneBits 32 j result.bv = dotBits x.bv y.bv j) :
    uN.mk_uN result.val = dotResult x.bv y.bv := by
  have packed := pack_map_of_lanes .I32 (128/lsize .I32) result.bv.toNat
    (fun j => (dotBits x.bv y.bv j).toNat)
    (by intro j valid; rw [←lane_bits_to_nat]; change (laneBits 32 j result.bv).toNat = _; rw [lanes j valid])
  rw [shape_of_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  unfold dotResult dotWords Map
  rw [List.map_map]
  have same (bits : Nat) : laneOfBits .I32 bits = .mk_lane__0 .I32 (.mk_uN bits) := by rfl
  simp only [same] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Dot Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem dot_lanes_sound (x y : U128)
    :
    runtime.interp.simd.multiply_lanes ((186#u32)) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        Spec.Simd.dotSource]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (dot_lanes x y)
  intro result lanes
  exact Spec.Simd.dot_step x.bv y.bv result.bv
    (dot_packed x y result lanes)

theorem dot_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats ((186#u32)) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.multiply_lanes ((186#u32)) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  unfold runtime.interp.simd.simd
  with_unfolding_all rfl

@[step] theorem dot_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats ((186#u32)) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          Spec.Simd.dotSource]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [dot_simd_eq floats offset laneIndex bits x y z memory]
  step with dot_lanes_sound x y as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end

end

/-! ## Narrow -/

section

/-!
Narrowing lane arithmetic: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Narrow Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def narrowLane (width : Nat) (signed : Bool) (x y : BitVec 128) (j : Nat) : BitVec width :=
  BitVec.ofInt width (clampLane width signed
    (laneBits (width*2) (j%(64/width)) (if j < 64/width then x else y)).toInt)

theorem narrow_loop (x y initial : U128) (width i : U32) (signedFlag : Bool)
    (supported : width.val ∈ [8,16]) (position : i.val ≤ 128/width.val)
    (initializedPrefix : ∀ j, j < i.val → laneBits width.val j initial.bv = narrowLane width.val signedFlag x.bv y.bv j) :
    runtime.interp.simd.narrow_lanes_loop x y width signedFlag initial i ⦃ result =>
      ∀ j, j < 128/width.val → laneBits width.val j result.bv = narrowLane width.val signedFlag x.bv y.bv j ⦄ := by
  have positive : 0 < width.val := by simp_all; omega
  have widthBound : width.val ≤ 64 := by simp_all; omega
  have halfPositive : 0 < 64/width.val := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
    rcases supported with h | h <;> rw [h] <;> decide
  have wideBound : width.val*2 ≤ 64 := by simp_all; omega
  unfold runtime.interp.simd.narrow_lanes_loop
  apply loop.spec_decr_nat (fun p => 128/width.val-p.2.val)
    (fun p => p.2.val ≤ 128/width.val ∧ ∀ j, j < p.2.val →
      laneBits width.val j p.1.bv = narrowLane width.val signedFlag x.bv y.bv j)
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.narrow_lanes_loop.body
    dsimp only
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 128/width.val := by scalar_tac
      step as ⟨half,halfEq⟩
      have selectEq : (if index < half then Result.ok x else Result.ok y) = Result.ok (if index < half then x else y) := by split <;> rfl
      rw [selectEq,bind_ok]
      step as ⟨wide,wideEq⟩
      step as ⟨laneIndex,laneIndexEq⟩
      have laneBound : wide.val*laneIndex.val < 128 := by
        rw [wideEq,laneIndexEq,halfEq]
        have modBound := Nat.mod_lt index.val halfPositive
        simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
        rcases supported with h | h <;> rw [h] at * <;> omega
      step with lane (if index < half then x else y) wide laneIndex (by scalar_tac) (by scalar_tac) laneBound as ⟨a,aEq⟩
      have aBits := lane_word_cast wide.val laneIndex.val (if index < half then x else y).bv a (by rw [lane_bits_to_nat]; exact aEq)
      step with signed a wide (by scalar_tac) (by scalar_tac) as ⟨sa,saEq⟩
      step as ⟨widened,widenedEq⟩
      step with saturate widened width signedFlag (by simp only [List.mem_cons,List.not_mem_nil,or_false] at supported ⊢; rcases supported with h | h; exact Or.inl h; exact Or.inr (Or.inl h)) as ⟨value,valueEq⟩
      have widenedVal : widened.val = sa.val := by simp [widenedEq]
      have correct : value.bv.setWidth width.val = narrowLane width.val signedFlag x.bv y.bv index.val := by
        rw [valueEq,widenedVal,saEq,aBits]
        with_unfolding_all rw [wideEq]
        simp only [laneIndexEq,UScalar.lt_equiv,halfEq,narrowLane]
        split <;> rfl
      step with put_lanes current width index value positive widthBound (lane_range _ _ less) as ⟨updated,same,other⟩
      have countBound : 128/width.val ≤ 128 := Nat.div_le_self _ _
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; rw [same]; exact correct
        · rw [other j (lane_range _ _ (by omega)) eq]; exact initialized j (by omega)
      · omega
    · have finished : index.val = 128/width.val := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Narrow Lanes -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def narrowWidth : NarrowWidth → U32 | .i8 => 8#u32 | .i16 => 16#u32

def narrowOpcode (ty : NarrowWidth) (signed : Bool) : U32 :=
  match ty,signed with
  | .i8,true => 101#u32 | .i8,false => 102#u32
  | .i16,true => 133#u32 | .i16,false => 134#u32

theorem narrow_dispatch_eq (ty : NarrowWidth) (signed : Bool) (x y : U128) :
    runtime.interp.simd.narrow_lanes (narrowOpcode ty signed) x y =
      (runtime.interp.simd.narrow_lanes_loop x y (narrowWidth ty) signed 0#u128 0#u32) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.narrow_lanes narrowOpcode narrowWidth
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals rfl

@[step] theorem narrow_lanes (ty : NarrowWidth) (signed : Bool) (x y : U128) :
    runtime.interp.simd.narrow_lanes (narrowOpcode ty signed) x y ⦃ result =>
      ∀ j, j < 128/ty.width → laneBits ty.width j result.bv = narrowLane ty.width signed x.bv y.bv j ⦄ := by
  rw [narrow_dispatch_eq]
  apply WP.spec_mono (narrow_loop x y 0#u128 (narrowWidth ty) 0#u32 signed (by cases ty <;> decide) (by simp) (by simp))
  intro result lanes
  cases ty <;> with_unfolding_all exact lanes

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Narrow Packing -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem narrow_packed (ty : NarrowWidth) (signed : Bool) (x y result : U128)
    (lanes : ∀ j, j < 128/ty.width → laneBits ty.width j result.bv = narrowLane ty.width signed x.bv y.bv j) :
    uN.mk_uN result.val = narrowResult ty signed x.bv y.bv := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty.output) (128/ty.width) result.bv.toNat
    (fun j => (narrowLane ty.width signed x.bv y.bv j).toNat)
    (by
      intro j valid
      rw [←lane_bits_to_nat]
      change (laneBits ty.width j result.bv).toNat = _
      rw [lanes j valid])
  change packLanes (lanetype_Jnn ty.output) (List.map (fun j => laneOfBits (lanetype_Jnn ty.output)
    (narrowLane ty.width signed x.bv y.bv j).toNat) (List.range (128/ty.width))) = _ at packed
  have words : List.map (fun j => laneOfBits (lanetype_Jnn ty.output)
      (narrowLane ty.width signed x.bv y.bv j).toNat) (List.range (128/ty.width)) =
      Map (lane_.mk_lane__0 ty.output) (narrowWords ty signed x.bv) ++
      Map (lane_.mk_lane__0 ty.output) (narrowWords ty signed y.bv) := by
    cases ty <;> with_unfolding_all rfl
  have covers : lsize (lanetype_Jnn ty.output)*(128/ty.width) = 128 := by cases ty <;> decide
  rw [covers,Nat.mod_eq_of_lt result.bv.isLt,words] at packed
  unfold narrowResult
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Narrow Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem narrow_lanes_sound (ty : Spec.Simd.NarrowWidth) (signed : Bool) (x y : U128)
    :
    runtime.interp.simd.narrow_lanes (narrowOpcode ty signed) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        (Spec.Simd.narrowSource ty signed)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (narrow_lanes ty signed x y)
  intro result lanes
  exact Spec.Simd.narrow_step ty signed x.bv y.bv result.bv
    (narrow_packed ty signed x y result lanes)

theorem narrow_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Spec.Simd.NarrowWidth) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (narrowOpcode ty signed) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.narrow_lanes (narrowOpcode ty signed) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.simd narrowOpcode
  all_goals with_unfolding_all rfl

@[step] theorem narrow_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Spec.Simd.NarrowWidth) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (narrowOpcode ty signed) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          (Spec.Simd.narrowSource ty signed)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [narrow_simd_eq floats ty signed offset laneIndex bits x y z memory]
  step with narrow_lanes_sound ty signed x y as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end

end

/-! ## Pairwise -/

section

/-!
Pairwise extended addition: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Pairwise Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def pairwiseWord (width : U32) (signed : Bool) (a b : U64) : Result U64 := do
  if signed then
    let sa ← runtime.interp.simd.signed a width
    let sb ← runtime.interp.simd.signed b width
    let sum ← sa + sb
    Result.ok (IScalar.hcast .U64 sum)
  else a + b

theorem pairwise_loop (width i : U32) (signed : Bool) (x initial : U128)
    (positive : 0 < width.val) (widthBound : width.val ≤ 32)
    (R : Nat → BitVec (width.val*2) → Prop)
    (wordLaw : ∀ j, j < 64/width.val → ∀ a b : U64,
      a.val = (laneBits width.val (2*j) x.bv).toNat →
      b.val = (laneBits width.val (2*j+1) x.bv).toNat →
      pairwiseWord width signed a b ⦃ value => R j (value.bv.setWidth (width.val*2)) ⦄)
    (position : i.val ≤ 64/width.val)
    (initializedPrefix : ∀ j, j < i.val → R j (laneBits (width.val*2) j initial.bv)) :
    runtime.interp.simd.pairwise_add_lanes_loop x width signed initial i ⦃ result =>
      ∀ j, j < 64/width.val → R j (laneBits (width.val*2) j result.bv) ⦄ := by
  unfold runtime.interp.simd.pairwise_add_lanes_loop
  apply loop.spec_decr_nat (fun p => 64/width.val-p.2.val)
    (fun p => p.2.val ≤ 64/width.val ∧ ∀ j, j < p.2.val → R j (laneBits (width.val*2) j p.1.bv))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.pairwise_add_lanes_loop.body
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 64/width.val := by scalar_tac
      have countBound : 64/width.val ≤ 64 := Nat.div_le_self _ _
      have productBound : width.val*(64/width.val) ≤ 64 := Nat.mul_div_le _ _
      have indexProduct : width.val*(index.val+1) ≤ 64 :=
        (Nat.mul_le_mul_left _ less).trans productBound
      have range : width.val*2*index.val+width.val*2 ≤ 128 := by nlinarith
      step as ⟨first,firstEq⟩
      step with lane x width first positive (by omega) (by rw [firstEq]; nlinarith) as ⟨a,aEq⟩
      step as ⟨second,secondEq⟩
      step with lane x width second positive (by omega) (by rw [secondEq,firstEq];nlinarith) as ⟨b,bEq⟩
      have aBits : a.val = (laneBits width.val (2*index.val) x.bv).toNat := by
        rw [lane_bits_to_nat,←firstEq]; exact aEq
      have bBits : b.val = (laneBits width.val (2*index.val+1) x.bv).toNat := by
        rw [lane_bits_to_nat,←firstEq,←secondEq]; exact bEq
      with_unfolding_all change Aeneas.Std.bind (pairwiseWord width signed a b) _ ⦃ _ ⦄
      step with wordLaw index.val less a b aBits bBits as ⟨value,allowed⟩
      step as ⟨wide,wideEq⟩
      step with put_lanes current wide index value (by omega) (by omega) (by rw [wideEq];exact range) as ⟨updated,same,other⟩
      step as ⟨next,nextEq⟩
      refine ⟨by omega,?_,by omega⟩
      intro j bound
      by_cases eq : j=index.val
      · subst j; rw [wideEq] at same; rw [same]; exact allowed
      · have otherRange : wide.val*j+wide.val ≤ 128 := by
          have le : j ≤ index.val := by omega
          have := Nat.mul_le_mul_left (width.val*2) le
          rw [wideEq]; omega
        rw [wideEq] at other
        rw [other j (by simpa only [wideEq] using otherRange) eq]
        exact initialized j (by omega)
    · have finished : index.val=64/width.val := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩
end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Pairwise Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

@[step] theorem pairwise_word (width : U32) (signed : Bool) (a b : U64)
    (x y : BitVec width.val) (supported : width.val ∈ [8,16])
    (aBits : a.val = x.toNat) (bBits : b.val = y.toNat) :
    pairwiseWord width signed a b ⦃ result =>
      result.bv.setWidth (width.val*2) = pairwiseBits signed x y ⦄ := by
  have positive : 0 < width.val := by simp only [List.mem_cons,List.not_mem_nil,or_false] at supported;omega
  have bound : width.val ≤ 16 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at supported;omega
  have aNat : a.val < 65536 := by
    rw [aBits]
    exact lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) bound)
  have bNat : b.val < 65536 := by
    rw [bBits]
    exact lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by decide) bound)
  have aExact : a.bv = x.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq;rw [BitVec.toNat_setWidth_of_le (by omega)];exact aBits
  have bExact : b.bv = y.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq;rw [BitVec.toNat_setWidth_of_le (by omega)];exact bBits
  unfold pairwiseWord
  cases signed
  · simp only [Bool.false_eq_true,↓reduceIte]
    step as ⟨value,valueEq⟩
    have valueBits : value.bv = a.bv+b.bv := by
      apply BitVec.eq_of_toNat_eq
      change value.val = (a.val+b.val)%2^64
      rw [←valueEq]
      exact (Nat.mod_eq_of_lt (by scalar_tac)).symm
    refine (congrArg (BitVec.setWidth (width.val*2)) valueBits).trans ?_
    rw [BitVec.setWidth_add _ _ (by omega),aExact,bExact,
      BitVec.setWidth_setWidth_of_le _ (by omega),BitVec.setWidth_setWidth_of_le _ (by omega)]
    rfl
  · simp only [↓reduceIte]
    step with signed_bits a width positive (by omega) as ⟨sa,saBits⟩
    step with signed_bits b width positive (by omega) as ⟨sb,sbBits⟩
    have saExact : sa.bv = x.signExtend 64 := by
      rw [saBits,aExact,BitVec.setWidth_setWidth_of_le _ (by omega),BitVec.setWidth_eq]
    have sbExact : sb.bv = y.signExtend 64 := by
      rw [sbBits,bExact,BitVec.setWidth_setWidth_of_le _ (by omega),BitVec.setWidth_eq]
    have signedBounds (bits : BitVec width.val) : -32768 ≤ bits.toInt ∧ bits.toInt < 32768 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
      rcases supported with h | h
      all_goals have lo := BitVec.le_toInt bits
      all_goals have hi := BitVec.toInt_lt (x:=bits)
      all_goals simp only [h] at lo hi
      all_goals omega
    have saBound : -32768 ≤ sa.val ∧ sa.val < 32768 := by
      change -32768 ≤ sa.bv.toInt ∧ sa.bv.toInt < 32768
      rw [saExact,BitVec.toInt_signExtend_of_le (by omega)]
      exact signedBounds x
    have sbBound : -32768 ≤ sb.val ∧ sb.val < 32768 := by
      change -32768 ≤ sb.bv.toInt ∧ sb.bv.toInt < 32768
      rw [sbExact,BitVec.toInt_signExtend_of_le (by omega)]
      exact signedBounds y
    step as ⟨value,valueEq⟩
    have valueBits : value.bv = sa.bv+sb.bv := by
      rw [←BitVec.ofInt_toInt (x:=value.bv)]
      change BitVec.ofInt 64 value.val = _
      rw [valueEq,BitVec.ofInt_add]
      simp
    simp only [IScalar.hcast_bv_eq,UScalarTy.U64_numBits_eq,IScalarTy.I64_numBits_eq,BitVec.signExtend_eq]
    refine (congrArg (BitVec.setWidth (width.val*2)) valueBits).trans ?_
    rw [BitVec.setWidth_add _ _ (by omega),saExact,sbExact,
      sign_extend_restrict _ _ (by omega),sign_extend_restrict _ _ (by omega)]
    rfl
end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Pairwise Lanes -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def pairwiseOpcode (ty : PairwiseWidth) (signed : Bool) : U32 :=
  match ty,signed with | .i8,true => 124#u32 | .i8,false => 125#u32 | .i16,true => 126#u32 | .i16,false => 127#u32

theorem pairwise_dispatch_eq (ty : PairwiseWidth) (signed : Bool) (x : U128) :
    runtime.interp.simd.pairwise_add_lanes (pairwiseOpcode ty signed) x =
      (runtime.interp.simd.pairwise_add_lanes_loop x (widenWidth ty.widen) signed 0#u128 0#u32) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.pairwise_add_lanes pairwiseOpcode widenWidth PairwiseWidth.widen
  all_goals repeat (with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _;rw [bind_ok])
  all_goals with_unfolding_all rfl

@[step] theorem pairwise_lanes (ty : PairwiseWidth) (signed : Bool) (x : U128) :
    runtime.interp.simd.pairwise_add_lanes (pairwiseOpcode ty signed) x ⦃ result =>
      ∀ j, j < ty.widen.count → laneBits (ty.widen.width*2) j result.bv =
        pairwiseBits signed (laneBits ty.widen.width (2*j) x.bv) (laneBits ty.widen.width (2*j+1) x.bv) ⦄ := by
  rw [pairwise_dispatch_eq]
  have widthEq := widen_width_val ty.widen
  have loopLaw := pairwise_loop (widenWidth ty.widen) 0#u32 signed x 0#u128
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = pairwiseBits signed
      (laneBits (widenWidth ty.widen).val (2*j) x.bv) (laneBits (widenWidth ty.widen).val (2*j+1) x.bv))
    (by intro j valid a b aEq bEq; exact pairwise_word _ _ _ _ _ _ (by cases ty <;> decide) aEq bEq)
    (by simp) (by simp)
  apply WP.spec_mono loopLaw
  intro out lanes
  cases ty <;> with_unfolding_all exact lanes
end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Pairwise Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem pairwise_packed (ty : PairwiseWidth) (signed : Bool) (x result : U128)
    (lanes : ∀ j, j < ty.widen.count → laneBits (ty.widen.width*2) j result.bv =
      pairwiseBits signed (laneBits ty.widen.width (2*j) x.bv) (laneBits ty.widen.width (2*j+1) x.bv)) :
    uN.mk_uN result.val = pairwiseResult ty signed x.bv := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty.widen.output) ty.widen.count result.bv.toNat
    (fun j => (pairwiseBits signed (laneBits ty.widen.width (2*j) x.bv) (laneBits ty.widen.width (2*j+1) x.bv)).toNat)
    (by intro j valid;rw [←lane_bits_to_nat];cases ty <;> exact congrArg BitVec.toNat (lanes j valid))
  have covers : lsize (lanetype_Jnn ty.widen.output)*ty.widen.count = 128 := by cases ty <;> decide
  rw [covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  unfold pairwiseResult pairwiseWords Map
  rw [List.map_map]
  have same (bits : Nat) : laneOfBits (lanetype_Jnn ty.widen.output) bits = .mk_lane__0 ty.widen.output (.mk_uN bits) := by cases ty <;> rfl
  simp only [same] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

@[step] theorem pairwise_lanes_sound (ty : PairwiseWidth) (signed : Bool) (x : U128) :
    runtime.interp.simd.pairwise_add_lanes (pairwiseOpcode ty signed) x ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),pairwiseSource ty signed]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (pairwise_lanes ty signed x)
  intro result lanes
  exact pairwise_step ty signed x.bv result.bv (pairwise_packed ty signed x result lanes)

theorem pairwise_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : PairwiseWidth) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (pairwiseOpcode ty signed) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.pairwise_add_lanes (pairwiseOpcode ty signed) x)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.simd pairwiseOpcode
  all_goals with_unfolding_all rfl

@[step] theorem pairwise_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : PairwiseWidth) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (pairwiseOpcode ty signed) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),pairwiseSource ty signed]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [pairwise_simd_eq]
  step with pairwise_lanes_sound ty signed x as ⟨value,source⟩
  exact ⟨value,rfl,source⟩
end Itasca.Runtime.Interp.Simd

end

end

/-! ## UnaryAll -/

section

/-!
Nonzero lanes and the all-true reduction.

Main declarations: `lane_nonzero` and `unary_all_iff`. A direct consumer is `Interp.Simd.Integer.AllTrueSound`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem lane_nonzero (width : Nat) (bits : BitVec width) (bound : width ≤ 64) :
    ((⟨bits.setWidth 64⟩ : U64) != 0#u64) = true ↔ bits.toNat ≠ 0 := by
  have value : (bits.setWidth 64).toNat = bits.toNat := by
    rw [BitVec.toNat_setWidth,Nat.mod_eq_of_lt]
    exact lt_of_lt_of_le bits.isLt (Nat.pow_le_pow_right (by decide) bound)
  simp only [bne_iff_ne]
  constructor
  · intro nonzero zero
    apply nonzero
    apply UScalar.eq_of_val_eq
    exact value.trans zero
  · intro nonzero zero
    apply nonzero
    exact value.symm.trans (congrArg UScalar.val zero)

theorem unary_all_iff (width : Nat) (x : BitVec 128) (count : Nat) (bound : width ≤ 64) :
    unaryAll width x count = true ↔ ∀ j, j < count → (laneBits width j x).toNat ≠ 0 := by
  induction count with
  | zero => simp [unaryAll]
  | succ count ih =>
    simp only [unaryAll,Bool.and_eq_true,ih,lane_nonzero width _ bound]
    constructor
    · rintro ⟨earlier,last⟩ j valid
      by_cases eq : j=count
      · simpa only [eq] using last
      · exact earlier j (by omega)
    · intro all
      exact ⟨fun j bound => all j (by omega),all count (by omega)⟩
end Itasca.Runtime.Interp.Simd

end

import Itasca.Runtime.Interp.Simd.Lanes.Access
import Itasca.Runtime.Interp.Simd.Lanes.SplatSound
import Itasca.Runtime.Spec.SegmentInitCases
import Itasca.Runtime.Spec.Simd.CompareInteger
import Itasca.Runtime.Interp.Simd.Lanes.Splat
import Itasca.Runtime.Interp.Simd.Lanes.Packing
import Itasca.Runtime.Spec.Simd.ExtendLanes

/-!
Sections, each formerly its own module: Signed, ExtractSigned, BinaryLoop, ShiftBits, WidenWords, WidenLanes, WidenSound, Shift, CompareLoop, CompareSigned.
-/

/-! ## Signed -/

section

/-!
Signed lane decoding and shifted integer values.

Main declarations: `shifted_signed` and `signed`. A direct consumer is `Interp.Simd.Integer.BinaryLoop`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem shifted_signed (bits : BitVec 64) (width : Nat)
    (positive : 0 < width) (bound : width ≤ 64) :
    (bits <<< (64-width)).sshiftRight (64-width) = (bits.setWidth width).signExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.msb_eq_getLsbD_last]
  by_cases valid : i < 64
  · have shiftValid : 64-width < 64 := by omega
    have last : 63-(64-width) = width-1 := by omega
    by_cases small : i < width
    · have fits : i+(64-width) < 64 := by omega
      simp [valid, small, Nat.add_comm, fits, Nat.not_le.mpr valid]
    · have outside : ¬i+(64-width) < 64 := by omega
      simp [valid, small, Nat.add_comm, outside, last, positive, Nat.not_le.mpr valid, Nat.not_lt.mpr (show 64-width ≤ 63 by omega)]
  · simp [valid]

@[step] theorem signed (v : U64) (width : U32)
    (positive : 0 < width.val) (bound : width.val ≤ 64) :
    runtime.interp.simd.signed v width ⦃ result =>
      result.val = (v.bv.setWidth width.val).toInt ⦄ := by
  unfold runtime.interp.simd.signed
  step as ⟨shift, shiftEq⟩
  step as ⟨shifted, shiftedEq, shiftedBits⟩
  rw [lift, bind_ok]
  step as ⟨answer, answerEq, answerBits⟩
  change answer.bv.toInt = _
  have answerBits' : answer.bv = shifted.bv.sshiftRight shift.val := answerBits
  calc
    answer.bv.toInt = (shifted.bv.sshiftRight shift.val).toInt :=
      congrArg BitVec.toInt answerBits'
    _ = ((v.bv <<< shift.val).sshiftRight shift.val).toInt :=
      congrArg (fun (x : BitVec 64) => (x.sshiftRight shift.val).toInt) shiftedBits
    _ = (v.bv.setWidth width.val).toInt := by
      rw [shiftEq, shifted_signed v.bv width.val positive bound,
        BitVec.toInt_signExtend_of_le bound]
end Itasca.Runtime.Interp.Simd

end

/-! ## ExtractSigned -/

section

/-!
Signed lane extraction: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Extract Signed Runtime -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

def extractSignedOpcode (ty : packtype) : U32 :=
  match ty with
  | .I8 => 21#u32
  | .I16 => 24#u32

@[step] theorem extract_signed_access (ty : packtype) (index : U32) (a b : U128)
    (valid : index.val < 128/psize ty) :
    runtime.interp.simd.access_lane (extractSignedOpcode ty) index a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        value.val = (SpecExt.Builtins.signedValue (psize ty)
          (a.val / 2^(psize ty*index.val) % 2^psize ty) % (2^32 : Int)).toNat ⦄ := by
  cases ty <;> unfold runtime.interp.simd.access_lane extractSignedOpcode
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) ⦃ _ ⦄
  all_goals rw [bind_ok]
  all_goals step as ⟨count, countEq⟩
  all_goals norm_num [psize] at valid countEq
  all_goals have fits : ¬ index ≥ count := by scalar_tac
  all_goals rw [if_neg fits]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok false) _) ⦃ _ ⦄
  all_goals rw [bind_ok]
  all_goals simp only [Bool.false_eq_true, ite_false]
  all_goals step with lane as ⟨laneValue, laneEq⟩
  all_goals with_unfolding_all change (Aeneas.Std.bind (runtime.interp.simd.signed _ _) _) ⦃ _ ⦄
  all_goals step with signed as ⟨signedValue, signedEq⟩
  all_goals simp only [lift, bind_ok, WP.spec_ok]
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt (by scalar_tac)]
  all_goals rw [IScalar.hcast_val_eq, signedEq, ←Spec.signed_value_bitvec, BitVec.toNat_setWidth]
  all_goals change (SpecExt.Builtins.signedValue _ (laneValue.val % _) % _).toNat = _
  all_goals rw [laneEq]
  all_goals simp [psize, UScalarTy.numBits]

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Extract Signed Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem extract_signed_access_sound (ty : packtype) (index : U32) (a b : U128)
    (valid : index.val < 128/psize ty) :
    runtime.interp.simd.access_lane (extractSignedOpcode ty) index a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        Step_pure [.VCONST .V128 (.mk_uN a.val),
          .VEXTRACT_LANE (Spec.Simd.shapeOf (lanetype_packtype ty)) (some .S) (.mk_uN index.val)]
          [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  apply WP.spec_mono (extract_signed_access ty index a b valid)
  rintro result ⟨value, exactResult, bits⟩
  refine ⟨value, exactResult, ?_⟩
  rw [bits]
  exact Spec.Simd.extract_signed_step ty index.val a.bv valid

theorem extract_signed_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : packtype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (extractSignedOpcode ty) offset laneIndex bits a b c memory =
      Aeneas.Std.bind (runtime.interp.simd.access_lane (extractSignedOpcode ty) laneIndex a b)
        (fun result => Result.ok (result, memory)) := by
  cases ty <;> unfold runtime.interp.simd.simd extractSignedOpcode <;> with_unfolding_all rfl

@[step] theorem extract_signed_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : packtype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) (valid : laneIndex.val < 128/psize ty) :
    runtime.interp.simd.simd floats (extractSignedOpcode ty) offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN a.val),
          .VEXTRACT_LANE (Spec.Simd.shapeOf (lanetype_packtype ty)) (some .S) (.mk_uN laneIndex.val)]
          [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  rw [extract_signed_dispatch_eq]
  step with extract_signed_access_sound ty laneIndex a b valid as ⟨result, value, exactResult, source⟩
  exact ⟨value, by rw [exactResult], source⟩

end Itasca.Runtime.Interp.Simd

end

end

/-! ## BinaryLoop -/

section

/-!
The word-level loop for binary integer lane operations.

Main declarations: `integerBinaryWord`. A direct consumer is `Interp.Simd.Integer.ArithmeticWord`.
-/

namespace Itasca.Runtime.Interp.Simd
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
        rw [lane_bits_to_nat]
        exact aEq
      step with lane y width index positive widthBound (by omega) as ⟨b,bEq⟩
      have bBits : b.val = (laneBits width.val index.val y.bv).toNat := by
        rw [lane_bits_to_nat]
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

end Itasca.Runtime.Interp.Simd

end

/-! ## ShiftBits -/

section

/-!
Bit-width and signed-value facts for lane shifts.

Main declarations: `shift_right_widen` and `signed_bits`. A direct consumer is `Interp.Simd.Integer.Shift`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem shift_right_widen (width : Nat) (bits : BitVec width) (shift : Nat) (bound : width ≤ 64) :
    ((bits.setWidth 64) >>> shift).setWidth width = bits >>> shift := by
  rw [←BitVec.setWidth_ushiftRight bound,BitVec.setWidth_setWidth_of_le _ bound,BitVec.setWidth_eq]

theorem shift_right_signed_widen (width : Nat) (bits : BitVec width) (shift : Nat)
    (positive : 0 < width) (bound : width ≤ 64) :
    ((bits.signExtend 64).sshiftRight shift).setWidth width = bits.sshiftRight shift := by
  by_cases full : width=64
  · subst width
    simp
  have lastFalse : ¬63 < width := by omega
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_sshiftRight,BitVec.getLsbD_signExtend,
    BitVec.msb_eq_getLsbD_last]
  by_cases inside : i < width
  · have valid : i < 64 := by omega
    by_cases shifted : shift+i < width
    · have fits : shift+i < 64 := by omega
      simp [inside,Nat.not_le.mpr inside,Nat.not_le.mpr valid,shifted,fits,lastFalse]
    · by_cases fits : shift+i < 64
      · simp [inside,Nat.not_le.mpr inside,Nat.not_le.mpr valid,shifted,fits,lastFalse]
      · simp [inside,Nat.not_le.mpr inside,Nat.not_le.mpr valid,shifted,fits,lastFalse]
  · simp [inside]

@[step] theorem lane_bits (v : U128) (width index : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (positionBound : width.val*index.val < 128) :
    runtime.interp.simd.lane v width index ⦃ result =>
      result.bv = (laneBits width.val index.val v.bv).setWidth 64 ⦄ := by
  apply WP.spec_mono (lane v width index positive widthBound positionBound)
  intro result value
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth,lane_bits_to_nat]
  change result.val = _
  rw [value]
  exact (Nat.mod_eq_of_lt (by
    apply lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
    exact Nat.pow_le_pow_right (by decide) widthBound)).symm

@[step] theorem signed_bits (v : U64) (width : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64) :
    runtime.interp.simd.signed v width ⦃ result =>
      result.bv = (v.bv.setWidth width.val).signExtend 64 ⦄ := by
  apply WP.spec_mono (signed v width positive widthBound)
  intro result value
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le widthBound]
  exact value
end Itasca.Runtime.Interp.Simd

end

/-! ## WidenWords -/

section

/-!
Widening integer lane calculations and their loop. Memory extension and pairwise addition consume these word facts without importing the final widening source correspondence.
-/

/-! ## Simd Widen Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def widenWord (width : U32) (extmul signed : Bool) (a b : U64) : Result U64 := do
  let a1 ← if signed then do
    let value ← runtime.interp.simd.signed a width
    Result.ok (IScalar.hcast .U64 value)
    else Result.ok a
  let b1 ← if signed then do
    let value ← runtime.interp.simd.signed b width
    Result.ok (IScalar.hcast .U64 value)
    else Result.ok b
  if extmul then Result.ok (core.num.U64.wrapping_mul a1 b1) else Result.ok a1

theorem widen_word_bind {α : Type} (width : U32) (extmul signed : Bool) (a b : U64) (k : U64 → Result α) :
    Aeneas.Std.bind (widenWord width extmul signed a b) k = (do
      let a1 ← if signed then do
        let value ← runtime.interp.simd.signed a width
        Result.ok (IScalar.hcast .U64 value)
        else Result.ok a
      let b1 ← if signed then do
        let value ← runtime.interp.simd.signed b width
        Result.ok (IScalar.hcast .U64 value)
        else Result.ok b
      let product ← if extmul then Result.ok (core.num.U64.wrapping_mul a1 b1) else Result.ok a1
      k product) := by
  simp only [widenWord,Std.bind_assoc]

theorem widen_loop (width i : U32) (extmul high signed : Bool) (x y initial : U128)
    (positive : 0 < width.val) (widthBound : width.val ≤ 32)
    (R : Nat → BitVec (width.val*2) → Prop)
    (wordLaw : ∀ j, j < 64/width.val → ∀ a b : U64,
      a.val = (laneBits width.val (j + if high then 64/width.val else 0) x.bv).toNat →
      b.val = (laneBits width.val (j + if high then 64/width.val else 0) y.bv).toNat →
      widenWord width extmul signed a b ⦃ value => R j (value.bv.setWidth (width.val*2)) ⦄)
    (position : i.val ≤ 64/width.val)
    (initializedPrefix : ∀ j, j < i.val → R j (laneBits (width.val*2) j initial.bv)) :
    runtime.interp.simd.widen_lanes_loop x width extmul high signed y initial i ⦃ result =>
      ∀ j, j < 64/width.val → R j (laneBits (width.val*2) j result.bv) ⦄ := by
  unfold runtime.interp.simd.widen_lanes_loop
  apply loop.spec_decr_nat (fun p => 64/width.val-p.2.val)
    (fun p => p.2.val ≤ 64/width.val ∧ ∀ j, j < p.2.val → R j (laneBits (width.val*2) j p.1.bv))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.widen_lanes_loop.body
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 64/width.val := by scalar_tac
      have countBound : 64/width.val ≤ 64 := Nat.div_le_self _ _
      have productBound : width.val*(64/width.val) ≤ 64 := Nat.mul_div_le _ _
      have indexProduct : width.val*(index.val+1) ≤ 64 :=
        (Nat.mul_le_mul_left _ less).trans productBound
      have range : width.val*2*index.val+width.val*2 ≤ 128 := by nlinarith
      have selectionBound : ∀ offset : U32, offset.val = (if high then 64/width.val else 0) →
          width.val*(index.val+offset.val) < 128 := by
        intro offset eq
        cases high <;> simp_all <;> nlinarith
      have offsetCall : (if high then Result.ok count else Result.ok 0#u32) ⦃ offset =>
          offset.val = (if high then 64/width.val else 0) ⦄ := by
        cases high <;> simp_all [WP.spec_ok]
      step with offsetCall as ⟨offset,offsetEq⟩
      have offsetBound : offset.val ≤ 64 := by cases high <;> simp_all
      step as ⟨selected,selectedEq⟩
      have selectedRange : width.val*selected.val < 128 := by rw [selectedEq]; exact selectionBound offset offsetEq
      step with lane x width selected positive (by omega) selectedRange as ⟨a,aEq⟩
      step with lane y width selected positive (by omega) selectedRange as ⟨b,bEq⟩
      have aBits : a.val = (laneBits width.val (index.val + if high then 64/width.val else 0) x.bv).toNat := by
        rw [lane_bits_to_nat,←offsetEq,←selectedEq]; exact aEq
      have bBits : b.val = (laneBits width.val (index.val + if high then 64/width.val else 0) y.bv).toNat := by
        rw [lane_bits_to_nat,←offsetEq,←selectedEq]; exact bEq
      with_unfolding_all rw [←widen_word_bind width extmul signed a b]
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

/-! ## Simd Widen Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

theorem sign_extend_restrict {width : Nat} (bits : BitVec width) (output : Nat) (le : output ≤ 64) :
    (bits.signExtend 64).setWidth output = bits.signExtend output := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_signExtend]
  by_cases inside : i < output
  · simp [inside,show i < 64 by omega]
  · simp [inside]

@[step] theorem widen_input (width : U32) (signed : Bool) (a : U64) (bits : BitVec width.val)
    (positive : 0 < width.val) (bound : width.val ≤ 32)
    (input : a.val = bits.toNat) :
    (if signed then do
      let value ← runtime.interp.simd.signed a width
      Result.ok (IScalar.hcast .U64 value)
      else Result.ok a) ⦃ result => result.bv.setWidth (width.val*2) = extendBits signed (width.val*2) bits ⦄ := by
  have aBits : a.bv = bits.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth_of_le (by omega)]
    exact input
  cases signed
  · simp only [Bool.false_eq_true,↓reduceIte,WP.spec_ok,extendBits]
    exact (congrArg (BitVec.setWidth (width.val*2)) aBits).trans
      (BitVec.setWidth_setWidth_of_le _ (by omega))
  · simp only [Bool.true_eq,↓reduceIte]
    step with signed_bits a width positive (by omega) as ⟨value,valueEq⟩
    simp only [IScalar.hcast_bv_eq,UScalarTy.U64_numBits_eq,IScalarTy.I64_numBits_eq,BitVec.signExtend_eq]
    have narrow : a.bv.setWidth width.val = bits := by
      rw [aBits,BitVec.setWidth_setWidth_of_le _ (by omega),BitVec.setWidth_eq]
    have exactValue : value.bv = bits.signExtend 64 := by rw [valueEq,narrow]
    exact (congrArg (BitVec.setWidth (width.val*2)) exactValue).trans
      (sign_extend_restrict bits _ (by omega))

@[step] theorem widen_word (width : U32) (multiply signed : Bool) (a b : U64)
    (x y : BitVec width.val) (positive : 0 < width.val) (bound : width.val ≤ 32)
    (aBits : a.val = x.toNat) (bBits : b.val = y.toNat) :
    widenWord width multiply signed a b ⦃ result =>
      result.bv.setWidth (width.val*2) = widenBits multiply signed x y ⦄ := by
  unfold widenWord
  step with widen_input width signed a x positive bound aBits as ⟨first,firstEq⟩
  step with widen_input width signed b y positive bound bBits as ⟨second,secondEq⟩
  cases multiply
  · exact WP.spec.ret firstEq
  · apply WP.spec.ret
    with_unfolding_all change (first.bv*second.bv).setWidth (width.val*2) = _
    rw [BitVec.setWidth_mul _ _ (by omega),firstEq,secondEq]
    rfl
end Itasca.Runtime.Interp.Simd

end

end

/-! ## WidenLanes -/

section

/-!
Widening lane widths and opcode correspondence.

Main declarations: `widenWidth` and `widenOpcode`. A direct consumer is `Interp.Simd.Integer.Pairwise`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def widenWidth (ty : WidenWidth) : U32 := match ty with
  | .i8 => 8#u32 | .i16 => 16#u32 | .i32 => 32#u32

def widenOpcode (ty : WidenWidth) (multiply high signed : Bool) : U32 :=
  ⟨BitVec.ofNat 32 ((match ty with | .i8 => 128 | .i16 => 160 | .i32 => 192) +
    (if multiply then 28 else 7) + (if signed then 0 else 2) + (if high then 1 else 0))⟩

theorem widen_width_val (ty : WidenWidth) : (widenWidth ty).val = ty.width := by cases ty <;> rfl

theorem widen_dispatch_eq (ty : WidenWidth) (multiply high signed : Bool) (x y : U128) :
    runtime.interp.simd.widen_lanes (widenOpcode ty multiply high signed) x y =
      (runtime.interp.simd.widen_lanes_loop x (widenWidth ty) multiply high
        signed (if multiply then y else 0#u128) 0#u128 0#u32) := by
  cases ty <;> cases multiply <;> cases high <;> cases signed
  all_goals unfold runtime.interp.simd.widen_lanes widenOpcode widenWidth
  all_goals repeat (with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _; rw [bind_ok])
  all_goals with_unfolding_all rfl

@[step] theorem widen_lanes (ty : WidenWidth) (multiply high signed : Bool) (x y : U128) :
    runtime.interp.simd.widen_lanes (widenOpcode ty multiply high signed) x y ⦃ result =>
      ∀ j, j < ty.count → laneBits (ty.width*2) j result.bv = widenBits multiply signed
        (laneBits ty.width (j+if high then ty.count else 0) x.bv)
        (laneBits ty.width (j+if high then ty.count else 0) y.bv) ⦄ := by
  rw [widen_dispatch_eq]
  have widthEq := widen_width_val ty
  have loopLaw := widen_loop (widenWidth ty) 0#u32 multiply high signed x (if multiply then y else 0#u128) 0#u128
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = widenBits multiply signed
      (laneBits (widenWidth ty).val (j+if high then 64/(widenWidth ty).val else 0) x.bv)
      (laneBits (widenWidth ty).val (j+if high then 64/(widenWidth ty).val else 0) (if multiply then y else 0#u128).bv))
    (by intro j valid a b aEq bEq; exact widen_word _ _ _ _ _ _ _ (by cases ty <;> decide) (by cases ty <;> decide) aEq bEq)
    (by simp) (by simp)
  apply WP.spec_mono loopLaw
  intro out lanes j valid
  rw [widthEq] at lanes
  have result := lanes j valid
  cases multiply <;> simpa only [Bool.false_eq_true,Bool.true_eq,↓reduceIte,widenBits,WidenWidth.count] using result
end Itasca.Runtime.Interp.Simd

end

/-! ## WidenSound -/

section

/-!
Packed-vector and source correspondence for widening operations.

Main declarations: `widen_packed` and `widen_simd_sound`. A direct consumer is `Interp.Simd.Execution.PureConversions`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem widen_packed (ty : WidenWidth) (multiply high signed : Bool) (x y result : U128)
    (lanes : ∀ j, j < ty.count → laneBits (ty.width*2) j result.bv = widenBits multiply signed
      (laneBits ty.width (j+if high then ty.count else 0) x.bv)
      (laneBits ty.width (j+if high then ty.count else 0) y.bv)) :
    uN.mk_uN result.val = widenResult ty multiply high signed x.bv y.bv := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty.output) ty.count result.bv.toNat
    (fun j => (widenBits multiply signed (laneBits ty.width (j+if high then ty.count else 0) x.bv)
      (laneBits ty.width (j+if high then ty.count else 0) y.bv)).toNat)
    (by intro j valid;rw [←lane_bits_to_nat];cases ty <;> exact congrArg BitVec.toNat (lanes j valid))
  have covers : lsize (lanetype_Jnn ty.output)*ty.count = 128 := by cases ty <;> decide
  rw [covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  unfold widenResult widenWords Map
  rw [List.map_map]
  have same (bits : Nat) : laneOfBits (lanetype_Jnn ty.output) bits = .mk_lane__0 ty.output (.mk_uN bits) := by cases ty <;> rfl
  simp only [same] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

@[step] theorem widen_lanes_sound (ty : WidenWidth) (multiply high signed : Bool) (x y : U128) :
    runtime.interp.simd.widen_lanes (widenOpcode ty multiply high signed) x y ⦃ result =>
      Step_pure ((if multiply then [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val)]
        else [.VCONST .V128 (.mk_uN x.val)]) ++ [widenSource ty multiply high signed])
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (widen_lanes ty multiply high signed x y)
  intro result lanes
  have packed := widen_packed ty multiply high signed x y result lanes
  cases multiply
  · exact extend_step ty high signed x.bv result.bv packed
  · exact widen_multiply_step ty high signed x.bv y.bv result.bv packed

theorem widen_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : WidenWidth) (multiply high signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (widenOpcode ty multiply high signed) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.widen_lanes (widenOpcode ty multiply high signed) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases multiply <;> cases high <;> cases signed
  all_goals unfold runtime.interp.simd.simd widenOpcode
  all_goals with_unfolding_all rfl

@[step] theorem widen_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : WidenWidth) (multiply high signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (widenOpcode ty multiply high signed) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure ((if multiply then [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val)]
          else [.VCONST .V128 (.mk_uN x.val)]) ++ [widenSource ty multiply high signed])
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [widen_simd_eq]
  step with widen_lanes_sound ty multiply high signed x y as ⟨value,source⟩
  exact ⟨value,rfl,source⟩
end Itasca.Runtime.Interp.Simd

end

/-! ## Shift -/

section

/-!
Integer lane shifts from scalar words through the lane loop. Bit extraction and the final source-dispatch result remain separate for their distinct consumers.
-/

/-! ## Simd Shift Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
open Itasca.Runtime.Spec.Simd

def shiftCode (kind : ShiftKind) : Nat :=
  match kind with | .left => 11 | .signedRight => 12 | .unsignedRight => 13

theorem shift_word (kind : ShiftKind) (op width amount : U32) (value : U64)
    (bits : BitVec width.val) (input : value.bv = bits.setWidth 64)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64) (amountBound : amount.val < width.val)
    (operation : op.val=shiftCode kind) :
    (match op with
      | 11#uscalar => value <<< amount
      | 12#uscalar => do
          let signedValue ← runtime.interp.simd.signed value width
          let shifted ← signedValue >>> amount
          Result.ok (IScalar.hcast .U64 shifted)
      | _ => value >>> amount) ⦃ result =>
        result.bv.setWidth width.val = shiftBits kind bits amount.val ⦄ := by
  have truncated : value.bv.setWidth width.val = bits := by rw [input,BitVec.setWidth_setWidth_of_le _ widthBound,BitVec.setWidth_eq]
  cases kind with
  | left =>
    have eq : op=11#u32 := UScalar.eq_of_val_eq operation
    subst op
    with_unfolding_all change (value <<< amount) ⦃ _ ⦄
    step as ⟨result,valueEq,bitsEq⟩
    simp only [shiftBits,bitsEq,BitVec.setWidth_shiftLeft_of_le widthBound,truncated]
  | signedRight =>
    have eq : op=12#u32 := UScalar.eq_of_val_eq operation
    subst op
    with_unfolding_all change (do
      let s ← runtime.interp.simd.signed value width
      let shifted ← s >>> amount
      Result.ok (IScalar.hcast .U64 shifted)) ⦃ _ ⦄
    step with signed_bits value width positive widthBound as ⟨signedValue,signedEq⟩
    step as ⟨shifted,shiftedEq,shiftedBits⟩
    simp only [shiftBits]
    simp only [IScalar.hcast_bv_eq, UScalarTy.U64_numBits_eq, IScalarTy.I64_numBits_eq, BitVec.signExtend_eq]
    rw [shiftedBits,signedEq,truncated,shift_right_signed_widen _ _ _ positive widthBound]
  | unsignedRight =>
    have eq : op=13#u32 := UScalar.eq_of_val_eq operation
    subst op
    with_unfolding_all change (value >>> amount) ⦃ _ ⦄
    step as ⟨result,valueEq,bitsEq⟩
    simp only [shiftBits]
    rw [bitsEq,input,shift_right_widen _ _ _ widthBound]
end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Shift Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

@[step] theorem shift_lanes_loop (kind : ShiftKind) (op width amount : U32) (x initial : U128) (i : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64) (amountBound : amount.val < width.val)
    (operation : op.val%32=shiftCode kind) (position : i.val ≤ 128/width.val)
    (initializedPrefix : ∀ j, j < i.val → laneBits width.val j initial.bv = shiftBits kind (laneBits width.val j x.bv) amount.val) :
    runtime.interp.simd.shift_lanes_loop op x width amount initial i ⦃ result =>
      ∀ j, j < 128/width.val → laneBits width.val j result.bv = shiftBits kind (laneBits width.val j x.bv) amount.val ⦄ := by
  unfold runtime.interp.simd.shift_lanes_loop
  apply loop.spec_decr_nat (fun p => 128/width.val-p.2.val)
    (fun p => p.2.val ≤ 128/width.val ∧
      ∀ j, j < p.2.val → laneBits width.val j p.1.bv = shiftBits kind (laneBits width.val j x.bv) amount.val)
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.shift_lanes_loop.body
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 128/width.val := by scalar_tac
      have range := lane_range width.val index.val less
      step with lane_bits x width index positive widthBound (by omega) as ⟨value,input⟩
      step as ⟨selected,selectedEq⟩
      step with shift_word kind selected width amount value (laneBits width.val index.val x.bv) input
        positive widthBound amountBound (selectedEq.trans operation) as ⟨shifted,shiftedEq⟩
      step with put_lanes current width index shifted positive widthBound range as ⟨updated,same,other⟩
      have countBound : 128/width.val ≤ 128 := Nat.div_le_self _ _
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j=index.val
        · subst j; exact same.trans shiftedEq
        · rw [other j (lane_range _ _ (by omega)) eq]
          exact initialized j (by omega)
      · omega
    · have finished : index.val=128/width.val := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩
end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Shift -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def shiftOpcode (ty : Jnn) (kind : ShiftKind) : U32 :=
  match ty,kind with
  | .I8,.left => 107#u32 | .I8,.signedRight => 108#u32 | .I8,.unsignedRight => 109#u32
  | .I16,.left => 139#u32 | .I16,.signedRight => 140#u32 | .I16,.unsignedRight => 141#u32
  | .I32,.left => 171#u32 | .I32,.signedRight => 172#u32 | .I32,.unsignedRight => 173#u32
  | .I64,.left => 203#u32 | .I64,.signedRight => 204#u32 | .I64,.unsignedRight => 205#u32

def shiftWidth (ty : Jnn) : U32 :=
  match ty with | .I8 => 8#u32 | .I16 => 16#u32 | .I32 => 32#u32 | .I64 => 64#u32

theorem shift_width_val (ty : Jnn) : (shiftWidth ty).val=lsize (lanetype_Jnn ty) := by cases ty <;> rfl

@[step] theorem shift_lanes (ty : Jnn) (kind : ShiftKind) (x y : U128) :
    runtime.interp.simd.shift_lanes (shiftOpcode ty kind) x y ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv =
          shiftBits kind (laneBits (lsize (lanetype_Jnn ty)) j x.bv)
            ((UScalar.cast .U32 y).val % lsize (lanetype_Jnn ty)) ⦄ := by
  unfold runtime.interp.simd.shift_lanes
  have opcodeBound : 96 ≤ (shiftOpcode ty kind).val := by cases ty <;> cases kind <;> decide
  step as ⟨difference,differenceEq⟩
  step as ⟨quotient,quotientEq⟩
  have quotientBound : quotient.val < 32 := by
    cases ty <;> cases kind <;> simp only [shiftOpcode] at differenceEq <;> scalar_tac
  step as ⟨width,widthEq,widthBits⟩
  have actualWidth : width = shiftWidth ty := by
    apply UScalar.eq_of_val_eq
    cases ty <;> cases kind <;> simp only [shiftOpcode,shiftWidth] at * <;> scalar_tac
  subst width
  simp only [lift,bind_ok]
  have positive : 0 < (shiftWidth ty).val := by cases ty <;> decide
  have bounded : (shiftWidth ty).val ≤ 64 := by cases ty <;> decide
  step as ⟨amount,amountEq⟩
  apply WP.spec_mono (shift_lanes_loop kind (shiftOpcode ty kind) (shiftWidth ty) amount x 0#u128 0#u32
    positive bounded (by scalar_tac)
    (by cases ty <;> cases kind <;> decide) (by cases ty <;> decide)
    (by intro j bound; change j < 0 at bound; omega))
  intro result lanes
  rw [amountEq] at lanes
  cases ty <;> with_unfolding_all exact lanes
end Itasca.Runtime.Interp.Simd

end

end

/-! ## CompareLoop -/

section

/-!
Packed comparison masks for integer lanes.

Main declarations: `comparisonBits`. A direct consumer is `Interp.Simd.Float.CompareLanes`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

def comparisonBits (width : Nat) (answer : Bool) : BitVec width :=
  if answer then (core.num.U64.MAX).bv.setWidth width else 0

@[step] theorem comparison_loop (x y initial : U128) (width cmp i : U32) (float : Bool)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (predicate : Nat → Bool)
    (compareLaw : ∀ j, j < 128/width.val → ∀ (a b : U64),
      a.val = (laneBits width.val j x.bv).toNat →
      b.val = (laneBits width.val j y.bv).toNat →
      (if float then runtime.interp.float.compare_float (UScalar.cast .U16 cmp) a b width
        else runtime.interp.int.compare_int (UScalar.cast .U16 cmp) a b width)
        ⦃ answer => answer = predicate j ⦄)
    (position : i.val ≤ 128/width.val)
    (initializedPrefix : ∀ j, j < i.val →
      laneBits width.val j initial.bv = comparisonBits width.val (predicate j))
    (zeroSuffix : ∀ j, i.val ≤ j → j < 128/width.val → laneBits width.val j initial.bv = 0) :
    runtime.interp.simd.compare_lanes_loop x y width cmp float initial i ⦃ result =>
      ∀ j, j < 128/width.val → laneBits width.val j result.bv = comparisonBits width.val (predicate j) ⦄ := by
  unfold runtime.interp.simd.compare_lanes_loop
  apply loop.spec_decr_nat (fun p => 128/width.val-p.2.val)
    (fun p => p.2.val ≤ 128/width.val ∧
      (∀ j, j < p.2.val → laneBits width.val j p.1.bv = comparisonBits width.val (predicate j)) ∧
      (∀ j, p.2.val ≤ j → j < 128/width.val → laneBits width.val j p.1.bv = 0))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized,zeros⟩
    dsimp only at indexBound initialized zeros
    unfold runtime.interp.simd.compare_lanes_loop.body
    dsimp only
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 128/width.val := by scalar_tac
      have range := lane_range width.val index.val less
      step with lane as ⟨a,aEq⟩
      step with lane as ⟨b,bEq⟩
      have aBits : a.val = (laneBits width.val index.val x.bv).toNat := by rw [lane_bits_to_nat]; exact aEq
      have bBits : b.val = (laneBits width.val index.val y.bv).toNat := by rw [lane_bits_to_nat]; exact bEq
      have compareCall :
          (if float then do
            let op ← lift (UScalar.cast .U16 cmp)
            runtime.interp.float.compare_float op a b width
           else do
            let op ← lift (UScalar.cast .U16 cmp)
            runtime.interp.int.compare_int op a b width)
          ⦃ answer => answer = predicate index.val ⦄ := by
        simpa only [lift,bind_ok] using compareLaw index.val less a b aBits bBits
      step with compareCall as ⟨answer,answerEq⟩
      have update : (if answer then runtime.interp.simd.put current width index core.num.U64.MAX
          else Result.ok current) ⦃ updated =>
        laneBits width.val index.val updated.bv = comparisonBits width.val answer ∧
        ∀ j, width.val*j+width.val ≤ 128 → j ≠ index.val →
          laneBits width.val j updated.bv = laneBits width.val j current.bv ⦄ := by
        cases answer
        · simp only [Bool.false_eq_true,if_false,WP.spec_ok,comparisonBits]
          exact ⟨zeros index.val (by omega) less,by simp⟩
        · simp only [if_true,comparisonBits]
          exact put_lanes current width index core.num.U64.MAX positive widthBound range
      step with update as ⟨updated,same,other⟩
      have countBound : 128/width.val ≤ 128 := Nat.div_le_self _ _
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; simpa only [answerEq] using same
        · exact (other j (lane_range _ _ (by omega)) eq).trans (initialized j (by omega))
      · intro j after valid
        exact (other j (lane_range _ _ valid) (by omega)).trans (zeros j (by omega) valid)
      · omega
    · have finished : index.val = 128/width.val := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix,zeroSuffix⟩

end Itasca.Runtime.Interp.Simd

end

/-! ## CompareSigned -/

section

/-!
Signed integer comparison and source ordering predicates.

Main declarations: `compare_int_lts` and `compare_int_ges`. A direct consumer is `Interp.Simd.Integer.CompareWords`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem compare_int_lts (a b : U64) (width : U32)
    (positive : 0 < width.val) (bound : width.val ≤ 64) :
    runtime.interp.int.compare_int 2#u16 a b width ⦃ result =>
      result = decide ((a.bv.setWidth width.val).toInt < (b.bv.setWidth width.val).toInt) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have valid : i.val < 64 := by scalar_tac
  simp only [HShiftLeft.hShiftLeft,UScalar.shiftLeft_UScalar,UScalar.shiftLeft,
    UScalarTy.numBits,valid,if_true,bind_ok,lift,HShiftRight.hShiftRight,
    IScalar.shiftRight_UScalar,IScalar.shiftRight,IScalarTy.numBits]
  with_unfolding_all change (Result.ok
    (decide ((⟨(a.bv <<< i.val).sshiftRight i.val⟩ : I64) < (⟨(b.bv <<< i.val).sshiftRight i.val⟩ : I64)))) ⦃ _ ⦄
  simp only [WP.spec_ok,IScalar.lt_equiv,IScalar.val,hi]
  rw [shifted_signed a.bv width.val positive bound,shifted_signed b.bv width.val positive bound,
    BitVec.toInt_signExtend_of_le bound,BitVec.toInt_signExtend_of_le bound]

@[step] theorem compare_int_gts (a b : U64) (width : U32)
    (positive : 0 < width.val) (bound : width.val ≤ 64) :
    runtime.interp.int.compare_int 4#u16 a b width ⦃ result =>
      result = decide ((a.bv.setWidth width.val).toInt > (b.bv.setWidth width.val).toInt) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have valid : i.val < 64 := by scalar_tac
  simp only [HShiftLeft.hShiftLeft,UScalar.shiftLeft_UScalar,UScalar.shiftLeft,
    UScalarTy.numBits,valid,if_true,bind_ok,lift,HShiftRight.hShiftRight,
    IScalar.shiftRight_UScalar,IScalar.shiftRight,IScalarTy.numBits]
  with_unfolding_all change (Result.ok
    (decide ((⟨(a.bv <<< i.val).sshiftRight i.val⟩ : I64) > (⟨(b.bv <<< i.val).sshiftRight i.val⟩ : I64)))) ⦃ _ ⦄
  simp only [WP.spec_ok,IScalar.lt_equiv,IScalar.val,hi]
  rw [shifted_signed a.bv width.val positive bound,shifted_signed b.bv width.val positive bound,
    BitVec.toInt_signExtend_of_le bound,BitVec.toInt_signExtend_of_le bound]

@[step] theorem compare_int_les (a b : U64) (width : U32)
    (positive : 0 < width.val) (bound : width.val ≤ 64) :
    runtime.interp.int.compare_int 6#u16 a b width ⦃ result =>
      result = decide ((a.bv.setWidth width.val).toInt ≤ (b.bv.setWidth width.val).toInt) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have valid : i.val < 64 := by scalar_tac
  simp only [HShiftLeft.hShiftLeft,UScalar.shiftLeft_UScalar,UScalar.shiftLeft,
    UScalarTy.numBits,valid,if_true,bind_ok,lift,HShiftRight.hShiftRight,
    IScalar.shiftRight_UScalar,IScalar.shiftRight,IScalarTy.numBits]
  with_unfolding_all change (Result.ok
    (decide ((⟨(a.bv <<< i.val).sshiftRight i.val⟩ : I64) ≤ (⟨(b.bv <<< i.val).sshiftRight i.val⟩ : I64)))) ⦃ _ ⦄
  simp only [WP.spec_ok,IScalar.le_equiv,IScalar.val,hi]
  rw [shifted_signed a.bv width.val positive bound,shifted_signed b.bv width.val positive bound,
    BitVec.toInt_signExtend_of_le bound,BitVec.toInt_signExtend_of_le bound]

@[step] theorem compare_int_ges (a b : U64) (width : U32)
    (positive : 0 < width.val) (bound : width.val ≤ 64) :
    runtime.interp.int.compare_int 8#u16 a b width ⦃ result =>
      result = decide ((a.bv.setWidth width.val).toInt ≥ (b.bv.setWidth width.val).toInt) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have valid : i.val < 64 := by scalar_tac
  simp only [HShiftLeft.hShiftLeft,UScalar.shiftLeft_UScalar,UScalar.shiftLeft,
    UScalarTy.numBits,valid,if_true,bind_ok,lift,HShiftRight.hShiftRight,
    IScalar.shiftRight_UScalar,IScalar.shiftRight,IScalarTy.numBits]
  with_unfolding_all change (Result.ok
    (decide ((⟨(a.bv <<< i.val).sshiftRight i.val⟩ : I64) ≥ (⟨(b.bv <<< i.val).sshiftRight i.val⟩ : I64)))) ⦃ _ ⦄
  simp only [WP.spec_ok,IScalar.le_equiv,IScalar.val,hi]
  rw [shifted_signed a.bv width.val positive bound,shifted_signed b.bv width.val positive bound,
    BitVec.toInt_signExtend_of_le bound,BitVec.toInt_signExtend_of_le bound]

end Itasca.Runtime.Interp.Simd

end

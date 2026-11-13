import Itasca.Runtime.Interp.Simd.Integer.UnaryAll
import Itasca.Runtime.Spec.Simd.IntegerMinMax
import Itasca.Runtime.Interp.Simd.Integer.UnaryWords
import Itasca.Runtime.Interp.Numeric.Integer.IntCounts
import SpecExt.Builtins.Examples
import Itasca.Runtime.Interp.Simd.Integer.CompareSigned
import Itasca.Runtime.Spec.Simd.ExtendLanes
import Itasca.Runtime.Spec.Simd.Pairwise

/-!
Sections, each formerly its own module: AllTrueSound, UnarySigns, BitmaskSound, Population, UnaryBits, PopcountSound, ShiftSound, UnarySound, Arithmetic, Average, MinMax, Q15.
-/

/-! ## AllTrueSound -/

section

/-!
Lane and dispatch correspondence for all-true reduction.

Main declarations: `all_true_lanes_sound` and `all_true_dispatch_eq`. A direct consumer is `Interp.Simd.Execution.PureUnary`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins
@[step] theorem all_true_lanes_sound (ty : Jnn) (x : U128) :
    runtime.interp.simd.integer_unary_lanes (unaryOpcode ty .allTrue) x
      ⦃ result => Step_pure [.VCONST .V128 (.mk_uN x.val),allTrueSource ty]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN result.val))] ⦄ := by
  apply WP.spec_mono (integer_unary_lanes ty .allTrue x)
  intro result outcome
  have truth := unary_all_iff (lsize (lanetype_Jnn ty)) x.bv
    (128/lsize (lanetype_Jnn ty)) (by cases ty <;> decide)
  have source := all_true_step ty x.bv
    (unaryAll (lsize (lanetype_Jnn ty)) x.bv (128/lsize (lanetype_Jnn ty))) truth
  change result = UScalar.cast .U128 (UScalar.cast_fromBool .U32 _) at outcome
  subst result
  cases h : unaryAll (lsize (lanetype_Jnn ty)) x.bv (128/lsize (lanetype_Jnn ty)) <;>
    simp only [h,Bool.false_eq_true,ite_false,ite_true] at source ⊢ <;>
    with_unfolding_all exact source

theorem all_true_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (unaryOpcode ty .allTrue) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.integer_unary_lanes (unaryOpcode ty .allTrue) x)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> unfold runtime.interp.simd.simd unaryOpcode <;> with_unfolding_all rfl
end Itasca.Runtime.Interp.Simd

end

/-! ## UnarySigns -/

section

/-!
Sign bits produced by unary lane operations.

Main declarations: `unary_sign_lane` and `unary_signs_get`. A direct consumer is `Interp.Simd.Integer.BitmaskSound`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem unary_sign_lane (width : Nat) (bits : BitVec width) (positive : 0 < width) (bound : width ≤ 64) :
    ((bits.setWidth 64 >>> (width-1)).setWidth 32) = (BitVec.ofBool bits.msb).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i valid
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight]
  by_cases zero : i=0
  · subst i
    simp [BitVec.msb,BitVec.getMsbD_eq_getLsbD,positive,show width-1<64 by omega]
  · have past : width ≤ i+(width-1) := by omega
    simp [BitVec.getLsbD_ofBool,zero,BitVec.getLsbD_of_ge bits (width-1+i) (by omega)]

theorem unary_signs_get (width : Nat) (x : BitVec 128) (count : Nat)
    (positive : 0 < width) (bound : width ≤ 64) (countBound : count ≤ 32) :
    ∀ i, i < 32 → (unarySigns width x count).getLsbD i =
      if i < count then (laneBits width i x).msb else false := by
  induction count with
  | zero => simp [unarySigns]
  | succ count ih =>
    intro i valid
    rw [unarySigns,BitVec.getLsbD_or,ih (by omega) i valid,unary_sign_lane width _ positive bound]
    simp only [BitVec.getLsbD_shiftLeft,BitVec.getLsbD_setWidth,BitVec.getLsbD_ofBool]
    by_cases before : i<count
    · simp [before,show i<count+1 from by omega]
    · by_cases same : i=count
      · subst i
        simp [valid]
      · have after : ¬ (i < count+1) := by omega
        have difference : i-count≠0 := by omega
        simp [before,after,difference]
end Itasca.Runtime.Interp.Simd

end

/-! ## BitmaskSound -/

section

/-!
Lane and dispatch correspondence for sign-bit masks.

Main declarations: `bitmask_lanes_sound` and `bitmask_dispatch_eq`. A direct consumer is `Interp.Simd.Execution.PureUnary`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins
@[step] theorem bitmask_lanes_sound (ty : Jnn) (x : U128) :
    runtime.interp.simd.integer_unary_lanes (unaryOpcode ty .bitmask) x
      ⦃ result => Step_pure [.VCONST .V128 (.mk_uN x.val),bitmaskSource ty]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN result.val))] ⦄ := by
  apply WP.spec_mono (integer_unary_lanes ty .bitmask x)
  intro result outcome
  let signs := unarySigns (lsize (lanetype_Jnn ty)) x.bv (128/lsize (lanetype_Jnn ty))
  have mask := unary_signs_get (lsize (lanetype_Jnn ty)) x.bv (128/lsize (lanetype_Jnn ty))
    (by cases ty <;> decide) (by cases ty <;> decide) (by cases ty <;> decide)
  have source := bitmask_step ty x.bv signs mask
  change result = UScalar.cast .U128 (⟨signs⟩ : U32) at outcome
  subst result
  have value : (UScalar.cast .U128 (⟨signs⟩ : U32)).val = signs.toNat := by
    simp only [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le signs.isLt (by decide))
  rw [value]
  exact source

theorem bitmask_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (unaryOpcode ty .bitmask) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.integer_unary_lanes (unaryOpcode ty .bitmask) x)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> unfold runtime.interp.simd.simd unaryOpcode <;> with_unfolding_all rfl
end Itasca.Runtime.Interp.Simd

end

/-! ## Population -/

section

/-!
Bit-count arithmetic within bounded lane widths.

Main declarations: `count_bits_zero` and `count_bits_width`. A direct consumer is `Interp.Simd.Integer.UnaryBits`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem count_bits_zero (width : Nat) : Primitive.countBits width 0 = 0 := by
  induction width with
  | zero => rfl
  | succ width ih => simp [Primitive.countBits,ih]

theorem count_bits_extend (width extra value : Nat) (bound : value < 2^width) :
    Primitive.countBits (width+extra) value = Primitive.countBits width value := by
  induction width generalizing value with
  | zero =>
    have zero : value=0 := by simpa using bound
    subst value
    simp [count_bits_zero]
  | succ width ih =>
    have half : value/2 < 2^width := by
      rw [Nat.pow_succ] at bound
      omega
    simp only [Nat.succ_add,Primitive.countBits]
    rw [ih (value/2) half]

theorem count_bits_width (width value : Nat) (bound : width ≤ 64) (fits : value < 2^width) :
    Primitive.countBits 64 value = Primitive.countBits width value := by
  have eq := count_bits_extend width (64-width) value fits
  simpa only [Nat.add_sub_of_le bound] using eq
end Itasca.Runtime.Interp.Simd

end

/-! ## UnaryBits -/

section

/-!
Low bits, signs and population counts of unary lane operations.

Main declarations: `sign_extend_low` and `unary_lane_population`. A direct consumer is `Interp.Simd.Integer.PopcountSound`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem sign_extend_low (width : Nat) (bits : BitVec width) (bound : width ≤ 64) :
    (bits.signExtend 64).setWidth width = bits := by
  apply BitVec.eq_of_getLsbD_eq
  intro i valid
  have fits : i < 64 := by omega
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_signExtend]
  simp only [valid,fits,ite_true,decide_true,Bool.true_and]

theorem unary_lane_neg (width : Nat) (bits : BitVec width) (bound : width ≤ 64) :
    unaryLane 1#u32 width bits = -bits := by
  have same := (congrArg (BitVec.setWidth width) (BitVec.zero_sub (bits.setWidth 64))).trans
    ((BitVec.setWidth_neg_of_le bound).trans
      (congrArg Neg.neg ((BitVec.setWidth_setWidth_of_le bits bound).trans (BitVec.setWidth_eq bits))))
  with_unfolding_all exact same

theorem unary_lane_abs (width : Nat) (bits : BitVec width) (bound : width ≤ 64) :
    unaryLane 0#u32 width bits = if bits.toInt < 0 then -bits else bits := by
  have sign : ((⟨bits.signExtend 64⟩ : I64) < 0#i64) ↔ bits.toInt < 0 := by
    change (bits.signExtend 64).toInt < 0 ↔ _
    rw [BitVec.toInt_signExtend_of_le bound]
  with_unfolding_all change
    ((if (⟨bits.signExtend 64⟩ : I64) < 0#i64
      then core.num.U64.wrapping_sub 0#u64 (IScalar.hcast .U64 (⟨bits.signExtend 64⟩ : I64))
      else IScalar.hcast .U64 (⟨bits.signExtend 64⟩ : I64)).bv).setWidth width = _
  simp only [sign]
  by_cases negative : bits.toInt < 0
  · rw [if_pos negative,if_pos negative]
    simp only [core.num.U64.wrapping_sub,UScalar.wrapping_sub,IScalar.hcast_bv_eq,
      UScalarTy.U64_numBits_eq,IScalarTy.I64_numBits_eq,BitVec.signExtend_eq]
    with_unfolding_all change (0 - bits.signExtend 64).setWidth width = -bits
    exact (congrArg (BitVec.setWidth width) (BitVec.zero_sub (bits.signExtend 64))).trans
      ((BitVec.setWidth_neg_of_le bound).trans (congrArg Neg.neg (sign_extend_low width bits bound)))
  · rw [if_neg negative,if_neg negative]
    simp only [IScalar.hcast_bv_eq,UScalarTy.U64_numBits_eq,IScalarTy.I64_numBits_eq,
      BitVec.signExtend_eq]
    exact sign_extend_low width bits bound
theorem unary_lane_population (bits : BitVec 8) :
    unaryLane 2#u32 8 bits = BitVec.ofNat 8 (SpecExt.Builtins.population (SpecExt.Builtins.integerBits 8 bits.toNat)) := by
  have widened : (bits.setWidth 64).toNat = bits.toNat := by
    rw [BitVec.toNat_setWidth,Nat.mod_eq_of_lt (lt_trans bits.isLt (by decide : 2^8 < 2^64))]
  have same := count_bits_width 8 bits.toNat (by decide) bits.isLt
  rw [Itasca.Runtime.Interp.count_bits_population 8] at same
  with_unfolding_all change
    ((BitVec.ofNat 32 (Primitive.countBits 64 (bits.setWidth 64).toNat)).setWidth 64).setWidth 8 = _
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
    BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 32),widened,same]

end Itasca.Runtime.Interp.Simd

end

/-! ## PopcountSound -/

section

/-!
Packed lane and dispatch correspondence for population count.

Main declarations: `popcount_packed` and `popcount_dispatch_sound`. A direct consumer is `Interp.Simd.Execution.PureUnary`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem popcount_packed (x result : U128)
    (lanes : ∀ j, j < 128/lsize .I8 →
      laneBits (lsize .I8) j result.bv =
        unaryLane (unaryAction .population) (lsize .I8)
          (laneBits (lsize .I8) j x.bv)) :
    uN.mk_uN result.val = inv_lanes_ (shapeOf .I8)
      ((popcountWords x.bv).map (lane_.mk_lane__0 .I8)) := by
  have laneValue (j : Nat) (valid : j < 128/lsize .I8) :
      result.bv.toNat / 2^(lsize .I8*j) % 2^lsize .I8 =
        (BitVec.ofNat 8 (population (integerBits 8 (vectorLane .I8 x.bv j).toNat))).toNat := by
    rw [←lane_bits_to_nat,lanes j valid]
    apply congrArg BitVec.toNat
    exact unary_lane_population _
  have packed := pack_map_of_lanes .I8 (128/lsize .I8) result.bv.toNat
    (fun j => (BitVec.ofNat 8 (population (integerBits 8 (vectorLane .I8 x.bv j).toNat))).toNat) laneValue
  rw [shape_of_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  change uN.mk_uN result.val = uN.mk_uN _
  apply congrArg uN.mk_uN
  refine packed.symm.trans ?_
  apply congrArg (packLanes .I8)
  simp only [popcountWords,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro j member
  have bound := population_bits_le 8 (vectorLane .I8 x.bv j).toNat
  simp [laneOfBits,BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show population (integerBits 8 (vectorLane .I8 x.bv j).toNat) < 256 by omega)]

@[step] theorem popcount_lanes_sound (x : U128) :
    runtime.interp.simd.integer_unary_lanes (unaryOpcode .I8 .population) x
      ⦃ result => Step_pure [.VCONST .V128 (.mk_uN x.val),popcountSource]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (integer_unary_lanes .I8 .population x)
  intro result outcome
  apply popcount_step x.bv result.bv
  apply popcount_packed x result
  exact outcome

theorem popcount_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (unaryOpcode .I8 .population) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.integer_unary_lanes (unaryOpcode .I8 .population) x)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  unfold runtime.interp.simd.simd unaryOpcode
  with_unfolding_all rfl

@[step] theorem popcount_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (unaryOpcode .I8 .population) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),popcountSource]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [popcount_dispatch_eq]
  step with popcount_lanes_sound x as ⟨value,source⟩
  exact ⟨value,rfl,source⟩
end Itasca.Runtime.Interp.Simd

end

/-! ## ShiftSound -/

section

/-!
Packed lane and dispatch correspondence for shifts.

Main declarations: `shift_packed` and `shift_dispatch_sound`. A direct consumer is `Interp.Simd.Execution.PureUnary`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem shift_packed (ty : Jnn) (kind : ShiftKind) (x result : U128) (amount : U32)
    (lanes : ∀ j, j < 128/lsize (lanetype_Jnn ty) →
      laneBits (lsize (lanetype_Jnn ty)) j result.bv =
        shiftBits kind (laneBits (lsize (lanetype_Jnn ty)) j x.bv)
          (amount.val % lsize (lanetype_Jnn ty))) :
    uN.mk_uN result.val = inv_lanes_ (shapeOf (lanetype_Jnn ty))
      (shiftLaneValues ty kind x.bv amount.val) := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty) (128/lsize (lanetype_Jnn ty)) result.bv.toNat
    (fun j => (shiftBits kind (laneBits (lsize (lanetype_Jnn ty)) j x.bv)
      (amount.val % lsize (lanetype_Jnn ty))).toNat) (by
      intro j valid
      rw [←lane_bits_to_nat,lanes j valid])
  rw [shape_of_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

@[step] theorem shift_lanes_sound (ty : Jnn) (kind : ShiftKind) (x y : U128) :
    runtime.interp.simd.shift_lanes (shiftOpcode ty kind) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),
        .CONST .I32 (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 y).val)), shiftSource ty kind]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (shift_lanes ty kind x y)
  intro result lanes
  exact shift_step ty kind x.bv result.bv (UScalar.cast .U32 y).bv
    (shift_packed ty kind x result (UScalar.cast .U32 y) lanes)

theorem shift_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (kind : ShiftKind) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (shiftOpcode ty kind) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.shift_lanes (shiftOpcode ty kind) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases kind <;> unfold runtime.interp.simd.simd shiftOpcode <;> with_unfolding_all rfl

@[step] theorem shift_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (kind : ShiftKind) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (shiftOpcode ty kind) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),
          .CONST .I32 (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 y).val)),shiftSource ty kind]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [shift_dispatch_eq]
  step with shift_lanes_sound ty kind x y as ⟨value,source⟩
  exact ⟨value,rfl,source⟩
end Itasca.Runtime.Interp.Simd

end

/-! ## UnarySound -/

section

/-!
Packed and source correspondence for signed unary lane actions.

Main declarations: `signedUnaryAction`. A direct consumer is `Interp.Simd.Execution.PureUnary`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

def signedUnaryAction : SignedUnaryKind → UnaryAction
  | .absolute => .absolute | .negate => .negate

theorem signed_unary_packed (ty : Jnn) (kind : SignedUnaryKind) (x result : U128)
    (lanes : ∀ j, j < 128/lsize (lanetype_Jnn ty) →
      laneBits (lsize (lanetype_Jnn ty)) j result.bv =
        unaryLane (unaryAction (signedUnaryAction kind)) (lsize (lanetype_Jnn ty))
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv)) :
    uN.mk_uN result.val = inv_lanes_ (shapeOf (lanetype_Jnn ty))
      ((signedUnaryWords ty kind x.bv).map (lane_.mk_lane__0 ty)) := by
  have laneValue (j : Nat) (valid : j < 128/lsize (lanetype_Jnn ty)) :
      result.bv.toNat / 2^(lsize (lanetype_Jnn ty)*j) % 2^lsize (lanetype_Jnn ty) =
        (signedUnaryBits kind (vectorLane (lanetype_Jnn ty) x.bv j)).toNat := by
    rw [←lane_bits_to_nat,lanes j valid]
    apply congrArg BitVec.toNat
    cases kind with
    | absolute => exact unary_lane_abs _ _ (by cases ty <;> decide)
    | negate => exact unary_lane_neg _ _ (by cases ty <;> decide)
  have packed := pack_map_of_lanes (lanetype_Jnn ty) (128/lsize (lanetype_Jnn ty)) result.bv.toNat
    (fun j => (signedUnaryBits kind (vectorLane (lanetype_Jnn ty) x.bv j)).toNat) laneValue
  rw [shape_of_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  change uN.mk_uN result.val = uN.mk_uN _
  apply congrArg uN.mk_uN
  refine packed.symm.trans ?_
  apply congrArg (packLanes (lanetype_Jnn ty))
  simp only [signedUnaryWords,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro j member
  cases ty <;> rfl

@[step] theorem signed_unary_lanes_sound (ty : Jnn) (kind : SignedUnaryKind) (x : U128) :
    runtime.interp.simd.integer_unary_lanes (unaryOpcode ty (signedUnaryAction kind)) x
      ⦃ result => Step_pure [.VCONST .V128 (.mk_uN x.val),signedUnarySource ty kind]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (integer_unary_lanes ty (signedUnaryAction kind) x)
  intro result outcome
  apply signed_unary_step ty kind x.bv result.bv
  apply signed_unary_packed ty kind x result
  cases kind <;> exact outcome

theorem signed_unary_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (kind : SignedUnaryKind) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (unaryOpcode ty (signedUnaryAction kind)) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.integer_unary_lanes (unaryOpcode ty (signedUnaryAction kind)) x)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases kind <;> unfold runtime.interp.simd.simd unaryOpcode signedUnaryAction <;> with_unfolding_all rfl

@[step] theorem signed_unary_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (kind : SignedUnaryKind) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (unaryOpcode ty (signedUnaryAction kind)) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),signedUnarySource ty kind]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [signed_unary_dispatch_eq]
  step with signed_unary_lanes_sound ty kind x as ⟨value,source⟩
  exact ⟨value,rfl,source⟩
end Itasca.Runtime.Interp.Simd

end

/-! ## Arithmetic -/

section

/-!
Wrapping integer lane arithmetic from scalar word calculations to packed source correspondence. Shared word calculations and lane iteration remain separate for conversion, saturation and reduction operations.
-/

/-! ## Simd Integer Arithmetic Packing -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem integer_arithmetic_packed (ty : Jnn) (kind : IntegerArithmetic) (x y result : U128)
    (lanes : ∀ j, j < 128/lsize (lanetype_Jnn ty) →
      laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerArithmeticBits kind
        (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv)) :
    uN.mk_uN result.val = integerArithmeticResult ty kind x.bv y.bv := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty) (128/lsize (lanetype_Jnn ty)) result.bv.toNat
    (fun j => (integerArithmeticBits kind (laneBits (lsize (lanetype_Jnn ty)) j x.bv)
      (laneBits (lsize (lanetype_Jnn ty)) j y.bv)).toNat)
    (by intro j valid; rw [←lane_bits_to_nat,lanes j valid])
  rw [shape_of_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  unfold integerArithmeticResult arithmeticWords Map
  rw [List.map_map]
  have same (bits : Nat) : laneOfBits (lanetype_Jnn ty) bits = .mk_lane__0 ty (.mk_uN bits) := by cases ty <;> rfl
  simp only [same] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Integer Arithmetic Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem integer_arithmetic_lanes_sound (ty : Jnn) (op : Spec.Simd.IntegerArithmetic) (x y : U128)
    (supported : Spec.Simd.integerArithmeticSupported ty op) :
    runtime.interp.simd.integer_binary_lanes (integerArithmeticOpcode ty op) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VBINOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.integerArithmeticSource ty op)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (integer_arithmetic_lanes ty op x y)
  intro result lanes
  exact Spec.Simd.integer_arithmetic_step ty op x.bv y.bv result.bv supported
    (integer_arithmetic_packed ty op x y result lanes)

theorem integer_arithmetic_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (op : Spec.Simd.IntegerArithmetic) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) (supported : Spec.Simd.integerArithmeticSupported ty op) :
    runtime.interp.simd.simd floats (integerArithmeticOpcode ty op) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.integer_binary_lanes (integerArithmeticOpcode ty op) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases op
  all_goals simp only [Spec.Simd.integerArithmeticSupported] at supported
  all_goals try contradiction
  all_goals unfold runtime.interp.simd.simd integerArithmeticOpcode
  all_goals with_unfolding_all rfl

@[step] theorem integer_arithmetic_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (op : Spec.Simd.IntegerArithmetic) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) (supported : Spec.Simd.integerArithmeticSupported ty op) :
    runtime.interp.simd.simd floats (integerArithmeticOpcode ty op) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VBINOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.integerArithmeticSource ty op)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [integer_arithmetic_simd_eq floats ty op offset laneIndex bits x y z memory supported]
  step with integer_arithmetic_lanes_sound ty op x y supported as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end

end

/-! ## Average -/

section

/-!
Unsigned lane averages: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Average Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

theorem average_word (width : U32) (a b : U64) (sa sb : I64)
    (widthBound : width.val ≤ 32)
    (aBound : a.val < 2^width.val) (bBound : b.val < 2^width.val) :
    integerBinaryWord 27#u32 width a b sa sb ⦃ result =>
      result.bv.setWidth width.val = averageBits (a.bv.setWidth width.val) (b.bv.setWidth width.val) ⦄ := by
  have power : 2^width.val ≤ 2^32 := Nat.pow_le_pow_right (by decide) widthBound
  have aValue : (a.bv.setWidth width.val).toNat = a.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt aBound
  have bValue : (b.bv.setWidth width.val).toNat = b.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt bBound
  unfold integerBinaryWord
  with_unfolding_all change (Aeneas.Std.bind _ _) ⦃ _ ⦄
  step as ⟨sum,sumEq⟩
  step as ⟨rounded,roundedEq⟩
  step as ⟨result,resultEq⟩
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth,average_bits_value,aValue,bValue]
  change result.val % 2^width.val = _
  rw [resultEq,roundedEq,sumEq]
  exact Nat.mod_eq_of_lt (by omega)

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Average Lanes -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def averageOpcode (ty : Jnn) : U32 :=
  match ty with | .I8 => 123#u32 | .I16 => 155#u32 | .I32 => 187#u32 | .I64 => 219#u32

theorem average_opcode_index (ty : Jnn) : (averageOpcode ty).val%32 = (27#u32).val := by
  cases ty <;> decide

theorem average_loop (ty : Jnn) (x y : U128)
    (supported : averageSupported ty) :
    runtime.interp.simd.integer_binary_lanes_loop (averageOpcode ty) x
      y (integerCompareWidth ty) 0#u128 0#u32 ⦃ result => ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = averageBits
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  have widthEq := integer_compare_width_val ty
  rw [←widthEq]
  apply integer_binary_loop x y 0#u128 (integerCompareWidth ty) (averageOpcode ty) 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = averageBits (laneBits (integerCompareWidth ty).val j x.bv)
      (laneBits (integerCompareWidth ty).val j y.bv))
  · intro j valid a b sa sb remainder aEq bEq _saEq _sbEq remainderEq
    have exactIndex : remainder = (27#u32) := by
      apply UScalar.eq_of_val_eq
      exact remainderEq.trans (average_opcode_index ty)
    subst remainder
    have aBits := lane_word_cast _ j x.bv a aEq
    have bBits := lane_word_cast _ j y.bv b bEq
    simpa only [aBits,bBits] using average_word (integerCompareWidth ty) a b sa sb
      (by cases ty <;> simp_all [averageSupported,integerCompareWidth])
      (by rw [aEq]; exact BitVec.isLt _) (by rw [bEq]; exact BitVec.isLt _)
  · simp
  · simp

theorem average_dispatch_eq (ty : Jnn) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes (averageOpcode ty) x y =
      (runtime.interp.simd.integer_binary_lanes_loop (averageOpcode ty)
        x y (integerCompareWidth ty) 0#u128 0#u32) := by
  cases ty
  all_goals unfold runtime.interp.simd.integer_binary_lanes averageOpcode integerCompareWidth
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals rfl

@[step] theorem average_lanes (ty : Jnn) (x y : U128)
    (supported : averageSupported ty) :
    runtime.interp.simd.integer_binary_lanes (averageOpcode ty) x y ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = averageBits
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  rw [average_dispatch_eq]
  apply WP.spec_mono (average_loop ty x y supported)
  intro result lanes
  simpa using lanes

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Average Packing -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem average_packed (ty : Jnn) (x y result : U128)
    (lanes : ∀ j, j < 128/lsize (lanetype_Jnn ty) →
      laneBits (lsize (lanetype_Jnn ty)) j result.bv = averageBits
        (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv)) :
    uN.mk_uN result.val = averageResult ty x.bv y.bv := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty) (128/lsize (lanetype_Jnn ty)) result.bv.toNat
    (fun j => (averageBits (laneBits (lsize (lanetype_Jnn ty)) j x.bv)
      (laneBits (lsize (lanetype_Jnn ty)) j y.bv)).toNat)
    (by intro j valid; rw [←lane_bits_to_nat,lanes j valid])
  rw [shape_of_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  unfold averageResult averageWords Map
  rw [List.map_map]
  have same (bits : Nat) : laneOfBits (lanetype_Jnn ty) bits = .mk_lane__0 ty (.mk_uN bits) := by cases ty <;> rfl
  simp only [same] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Average Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem average_lanes_sound (ty : Jnn) (x y : U128)
    (supported : Spec.Simd.averageSupported ty) :
    runtime.interp.simd.integer_binary_lanes (averageOpcode ty) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VBINOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.averageSource ty)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (average_lanes ty x y supported)
  intro result lanes
  exact Spec.Simd.average_step ty x.bv y.bv result.bv supported
    (average_packed ty x y result lanes)

theorem average_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) (supported : Spec.Simd.averageSupported ty) :
    runtime.interp.simd.simd floats (averageOpcode ty) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.integer_binary_lanes (averageOpcode ty) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty
  all_goals simp only [Spec.Simd.averageSupported] at supported
  all_goals try contradiction
  all_goals unfold runtime.interp.simd.simd averageOpcode
  all_goals with_unfolding_all rfl

@[step] theorem average_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) (supported : Spec.Simd.averageSupported ty) :
    runtime.interp.simd.simd floats (averageOpcode ty) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VBINOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.averageSource ty)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [average_simd_eq floats ty offset laneIndex bits x y z memory supported]
  step with average_lanes_sound ty x y supported as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end

end

/-! ## MinMax -/

section

/-!
Integer lane minima and maxima: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Integer Min Max Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def integerMinMaxIndex (kind : IntegerMinMax) : U32 :=
  match kind with | .minS => 22#u32 | .minU => 23#u32 | .maxS => 24#u32 | .maxU => 25#u32

theorem integer_minmax_word (kind : IntegerMinMax) (width : U32)
    (a b : U64) (sa sb : I64)
    (aBound : a.val < 2^width.val) (bBound : b.val < 2^width.val)
    (saEq : sa.val = (a.bv.setWidth width.val).toInt)
    (sbEq : sb.val = (b.bv.setWidth width.val).toInt) :
    integerBinaryWord (integerMinMaxIndex kind) width a b sa sb ⦃ result =>
      result.bv.setWidth width.val = integerMinMaxBits kind (a.bv.setWidth width.val) (b.bv.setWidth width.val) ⦄ := by
  have aValue : (a.bv.setWidth width.val).toNat = a.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt aBound
  have bValue : (b.bv.setWidth width.val).toNat = b.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt bBound
  cases kind
  all_goals unfold integerBinaryWord integerMinMaxIndex
  all_goals with_unfolding_all change (if _ then Result.ok a else Result.ok b) ⦃ _ ⦄
  all_goals simp only [IScalar.lt_equiv,UScalar.lt_equiv,saEq,sbEq,integerMinMaxBits,aValue,bValue]
  all_goals split <;> simp_all only [WP.spec_ok]

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Integer Min Max Lanes -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def integerMinMaxOpcode (ty : Jnn) (kind : IntegerMinMax) : U32 :=
  match ty,kind with
  | .I8,.minS => 118#u32 | .I8,.minU => 119#u32 | .I8,.maxS => 120#u32 | .I8,.maxU => 121#u32
  | .I16,.minS => 150#u32 | .I16,.minU => 151#u32 | .I16,.maxS => 152#u32 | .I16,.maxU => 153#u32
  | .I32,.minS => 182#u32 | .I32,.minU => 183#u32 | .I32,.maxS => 184#u32 | .I32,.maxU => 185#u32
  | .I64,.minS => 214#u32 | .I64,.minU => 215#u32 | .I64,.maxS => 216#u32 | .I64,.maxU => 217#u32

theorem integer_min_max_opcode_index (ty : Jnn) (kind : IntegerMinMax) :
    (integerMinMaxOpcode ty kind).val%32 = (integerMinMaxIndex kind).val := by
  cases ty <;> cases kind <;> decide

theorem integer_minmax_loop (ty : Jnn) (kind : IntegerMinMax) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes_loop (integerMinMaxOpcode ty kind) x
      y (integerCompareWidth ty) 0#u128 0#u32 ⦃ result => ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerMinMaxBits kind
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  have widthEq := integer_compare_width_val ty
  rw [←widthEq]
  apply integer_binary_loop x y 0#u128 (integerCompareWidth ty) (integerMinMaxOpcode ty kind) 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = integerMinMaxBits kind (laneBits (integerCompareWidth ty).val j x.bv)
      (laneBits (integerCompareWidth ty).val j y.bv))
  · intro j valid a b sa sb remainder aEq bEq saEq sbEq remainderEq
    have exactIndex : remainder = integerMinMaxIndex kind := by
      apply UScalar.eq_of_val_eq
      exact remainderEq.trans (integer_min_max_opcode_index ty kind)
    subst remainder
    have aBits := lane_word_cast _ j x.bv a aEq
    have bBits := lane_word_cast _ j y.bv b bEq
    simpa only [aBits,bBits] using integer_minmax_word kind (integerCompareWidth ty) a b sa sb
      (by rw [aEq]; exact BitVec.isLt _) (by rw [bEq]; exact BitVec.isLt _) saEq sbEq
  · simp
  · simp

theorem integer_minmax_dispatch_eq (ty : Jnn) (kind : IntegerMinMax) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes (integerMinMaxOpcode ty kind) x y =
      (runtime.interp.simd.integer_binary_lanes_loop (integerMinMaxOpcode ty kind)
        x y (integerCompareWidth ty) 0#u128 0#u32) := by
  cases ty <;> cases kind
  all_goals unfold runtime.interp.simd.integer_binary_lanes integerMinMaxOpcode integerCompareWidth
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals rfl

@[step] theorem integer_minmax_lanes (ty : Jnn) (kind : IntegerMinMax) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes (integerMinMaxOpcode ty kind) x y ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerMinMaxBits kind
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  rw [integer_minmax_dispatch_eq]
  apply WP.spec_mono (integer_minmax_loop ty kind x y)
  intro result lanes
  simpa using lanes

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Integer Min Max Packing -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem integer_minmax_packed (ty : Jnn) (kind : IntegerMinMax) (x y result : U128)
    (lanes : ∀ j, j < 128/lsize (lanetype_Jnn ty) →
      laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerMinMaxBits kind
        (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv)) :
    uN.mk_uN result.val = integerMinMaxResult ty kind x.bv y.bv := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty) (128/lsize (lanetype_Jnn ty)) result.bv.toNat
    (fun j => (integerMinMaxBits kind (laneBits (lsize (lanetype_Jnn ty)) j x.bv)
      (laneBits (lsize (lanetype_Jnn ty)) j y.bv)).toNat)
    (by intro j valid; rw [←lane_bits_to_nat,lanes j valid])
  rw [shape_of_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  unfold integerMinMaxResult minmaxWords Map
  rw [List.map_map]
  have same (bits : Nat) : laneOfBits (lanetype_Jnn ty) bits = .mk_lane__0 ty (.mk_uN bits) := by cases ty <;> rfl
  simp only [same] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Integer Min Max Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem integer_minmax_lanes_sound (ty : Jnn) (op : Spec.Simd.IntegerMinMax) (x y : U128)
    (supported : Spec.Simd.integerMinMaxSupported ty op) :
    runtime.interp.simd.integer_binary_lanes (integerMinMaxOpcode ty op) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VBINOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.integerMinMaxSource ty op)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (integer_minmax_lanes ty op x y)
  intro result lanes
  exact Spec.Simd.integer_minmax_step ty op x.bv y.bv result.bv supported
    (integer_minmax_packed ty op x y result lanes)

theorem integer_minmax_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (op : Spec.Simd.IntegerMinMax) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) (supported : Spec.Simd.integerMinMaxSupported ty op) :
    runtime.interp.simd.simd floats (integerMinMaxOpcode ty op) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.integer_binary_lanes (integerMinMaxOpcode ty op) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases op
  all_goals simp only [Spec.Simd.integerMinMaxSupported] at supported
  all_goals try contradiction
  all_goals unfold runtime.interp.simd.simd integerMinMaxOpcode
  all_goals with_unfolding_all rfl

@[step] theorem integer_minmax_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (op : Spec.Simd.IntegerMinMax) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) (supported : Spec.Simd.integerMinMaxSupported ty op) :
    runtime.interp.simd.simd floats (integerMinMaxOpcode ty op) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VBINOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.integerMinMaxSource ty op)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [integer_minmax_simd_eq floats ty op offset laneIndex bits x y z memory supported]
  step with integer_minmax_lanes_sound ty op x y supported as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end

end

/-! ## Q15 -/

section

/-!
Rounded saturating Q15 multiplication through lane iteration, packed words and source dispatch. The shared scalar Q15 word lemma remains separate for dot products.
-/

/-! ## Simd Q15 Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

theorem q15_loop (x y initial : U128) (i : U32)
    (position : i.val ≤ 8)
    (initializedPrefix : ∀ j, j < i.val → laneBits 16 j initial.bv =
      q15Bits (laneBits 16 j x.bv) (laneBits 16 j y.bv)) :
    runtime.interp.simd.multiply_lanes_loop 130#u32 x y initial i ⦃ result =>
      ∀ j, j < 8 → laneBits 16 j result.bv = q15Bits (laneBits 16 j x.bv) (laneBits 16 j y.bv) ⦄ := by
  unfold runtime.interp.simd.multiply_lanes_loop
  apply loop.spec_decr_nat (fun p => 8-p.2.val)
    (fun p => p.2.val ≤ 8 ∧ ∀ j, j < p.2.val → laneBits 16 j p.1.bv =
      q15Bits (laneBits 16 j x.bv) (laneBits 16 j y.bv))
  · rintro ⟨current,index⟩ ⟨indexBound,initialized⟩
    dsimp only at indexBound initialized
    unfold runtime.interp.simd.multiply_lanes_loop.body
    simp only [↓reduceIte]
    split
    · rename_i more
      have less : index.val < 8 := by scalar_tac
      step with lane x 16#u32 index (by decide) (by decide) (by scalar_tac) as ⟨a,aEq⟩
      have aBits : a.bv.setWidth 16 = laneBits 16 index.val x.bv :=
        lane_word_cast 16 _ _ a (by rw [lane_bits_to_nat]; exact aEq)
      step with signed a 16#u32 (by decide) (by decide) as ⟨sa,saEq⟩
      step with lane y 16#u32 index (by decide) (by decide) (by scalar_tac) as ⟨b,bEq⟩
      have bBits : b.bv.setWidth 16 = laneBits 16 index.val y.bv :=
        lane_word_cast 16 _ _ b (by rw [lane_bits_to_nat]; exact bEq)
      step with signed b 16#u32 (by decide) (by decide) as ⟨sb,sbEq⟩
      have aBound : -32768 ≤ sa.val ∧ sa.val < 32768 := by
        rw [saEq]; exact ⟨BitVec.le_toInt _,BitVec.toInt_lt⟩
      have bBound : -32768 ≤ sb.val ∧ sb.val < 32768 := by
        rw [sbEq]; exact ⟨BitVec.le_toInt _,BitVec.toInt_lt⟩
      rw [←Std.bind_assoc,←Std.bind_assoc,←Std.bind_assoc,←Std.bind_assoc]
      with_unfolding_all change (Aeneas.Std.bind (q15Word sa sb) _) ⦃ _ ⦄
      step with q15_word sa sb aBound bBound as ⟨value,valueEq⟩
      change sa.val = (a.bv.setWidth 16).toInt at saEq
      change sb.val = (b.bv.setWidth 16).toInt at sbEq
      rw [aBits] at saEq
      rw [bBits] at sbEq
      have correct : value.bv.setWidth 16 = q15Bits (laneBits 16 index.val x.bv) (laneBits 16 index.val y.bv) := by
        with_unfolding_all simpa only [q15Bits,saEq,sbEq] using valueEq
      step with put_lanes current 16#u32 index value (by decide) (by decide) (by scalar_tac) as ⟨updated,same,other⟩
      change laneBits 16 index.val updated.bv = value.bv.setWidth 16 at same
      change ∀ j, 16*j+16 ≤ 128 → j ≠ index.val → laneBits 16 j updated.bv = laneBits 16 j current.bv at other
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j = index.val
        · subst j; rw [same]; exact correct
        · rw [other j (by omega) eq]; exact initialized j (by omega)
      · omega
    · have finished : index.val = 8 := by scalar_tac
      simpa [finished] using initialized
  · exact ⟨position,initializedPrefix⟩

@[step] theorem q15_lanes (x y : U128) :
    runtime.interp.simd.multiply_lanes 130#u32 x y ⦃ result =>
      ∀ j, j < 8 → laneBits 16 j result.bv = q15Bits (laneBits 16 j x.bv) (laneBits 16 j y.bv) ⦄ := by
  unfold runtime.interp.simd.multiply_lanes
  apply WP.spec_mono (q15_loop x y 0#u128 0#u32 (by decide) (by simp))
  intro result lanes
  simpa using lanes

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Q15 Packing -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem q15_packed (x y result : U128)
    (lanes : ∀ j, j < 128/lsize .I16 →
      laneBits (lsize .I16) j result.bv = q15Bits
        (laneBits (lsize .I16) j x.bv) (laneBits (lsize .I16) j y.bv)) :
    uN.mk_uN result.val = q15Result x.bv y.bv := by
  have packed := pack_map_of_lanes .I16 (128/lsize .I16) result.bv.toNat
    (fun j => (q15Bits (laneBits (lsize .I16) j x.bv)
      (laneBits (lsize .I16) j y.bv)).toNat)
    (by intro j valid; rw [←lane_bits_to_nat,lanes j valid]; rfl)
  rw [shape_of_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  unfold q15Result q15Words Map
  rw [List.map_map]
  have same (bits : Nat) : laneOfBits .I16 bits = .mk_lane__0 .I16 (.mk_uN bits) := by rfl
  simp only [same] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Q15 Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem q15_lanes_sound (x y : U128)
    :
    runtime.interp.simd.multiply_lanes ((130#u32)) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VBINOP (Spec.Simd.shapeOf .I16) (Spec.Simd.q15Source)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (q15_lanes x y)
  intro result lanes
  exact Spec.Simd.q15_step x.bv y.bv result.bv
    (q15_packed x y result lanes)

theorem q15_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats ((130#u32)) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.multiply_lanes ((130#u32)) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  unfold runtime.interp.simd.simd
  with_unfolding_all rfl

@[step] theorem q15_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats ((130#u32)) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VBINOP (Spec.Simd.shapeOf .I16) (Spec.Simd.q15Source)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [q15_simd_eq floats offset laneIndex bits x y z memory]
  step with q15_lanes_sound x y as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end

end

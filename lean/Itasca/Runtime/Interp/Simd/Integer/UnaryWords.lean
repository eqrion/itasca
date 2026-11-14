import Itasca.Runtime.Interp.Simd.Integer.CompareSigned
import Itasca.Runtime.Spec.Simd.CompareInteger
import Itasca.Runtime.Spec.Simd.ExtendLanes
import Itasca.Runtime.Interp.Numeric.Integer.IntCounts

/-!
Sections, each formerly its own module: CompareWords, CompareLanes, CompareMaskBits, Compare, ArithmeticWord, ArithmeticLanes, UnaryWord, UnaryWords.
-/

/-! ## CompareWords -/

section

/-!
Integer lane comparison word calculations and opcode dispatch, shared by lane comparison and wrapping arithmetic.
-/

/-! ## Simd Compare Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def integerCompareIndex (op : vrelop_Jnn_N) : U16 :=
  match op with
  | .EQ => 0#u16 | .NE => 1#u16
  | .LT .S => 2#u16 | .LT .U => 3#u16
  | .GT .S => 4#u16 | .GT .U => 5#u16
  | .LE .S => 6#u16 | .LE .U => 7#u16
  | .GE .S => 8#u16 | .GE .U => 9#u16

@[step] theorem integer_compare_word (op : vrelop_Jnn_N) (a b : U64) (width : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (aBound : a.val < 2^width.val) (bBound : b.val < 2^width.val) :
    runtime.interp.int.compare_int (integerCompareIndex op) a b width ⦃ result =>
      result = Spec.Simd.integerLaneCompare op (a.bv.setWidth width.val) (b.bv.setWidth width.val) ⦄ := by
  have aValue : (a.bv.setWidth width.val).toNat = a.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt aBound
  have bValue : (b.bv.setWidth width.val).toNat = b.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt bBound
  cases op with
  | EQ => simpa only [integerCompareIndex,Spec.Simd.integerLaneCompare,aValue,bValue] using
      Itasca.Runtime.Interp.compare_int_eq a b width positive widthBound
  | NE => simpa only [integerCompareIndex,Spec.Simd.integerLaneCompare,aValue,bValue] using
      Itasca.Runtime.Interp.compare_int_ne a b width positive widthBound
  | LT sign => cases sign with
    | S => exact compare_int_lts a b width positive widthBound
    | U => simpa only [integerCompareIndex,Spec.Simd.integerLaneCompare,aValue,bValue] using
        Itasca.Runtime.Interp.compare_int_ltu a b width positive widthBound
  | GT sign => cases sign with
    | S => exact compare_int_gts a b width positive widthBound
    | U => simpa only [integerCompareIndex,Spec.Simd.integerLaneCompare,aValue,bValue] using
        Itasca.Runtime.Interp.compare_int_gtu a b width positive widthBound
  | LE sign => cases sign with
    | S => exact compare_int_les a b width positive widthBound
    | U => simpa only [integerCompareIndex,Spec.Simd.integerLaneCompare,aValue,bValue] using
        Itasca.Runtime.Interp.compare_int_leu a b width positive widthBound
  | GE sign => cases sign with
    | S => exact compare_int_ges a b width positive widthBound
    | U => simpa only [integerCompareIndex,Spec.Simd.integerLaneCompare,aValue,bValue] using
        Itasca.Runtime.Interp.compare_int_geu a b width positive widthBound

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Compare Dispatch -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def integerCompareWidth (ty : Jnn) : U32 :=
  match ty with
  | .I8 => 8#u32 | .I16 => 16#u32 | .I32 => 32#u32 | .I64 => 64#u32

def integerCompareOpcode (ty : Jnn) (op : vrelop_Jnn_N) : U32 :=
  match ty,op with
  | .I8,.EQ => 35#u32
  | .I8,.NE => 36#u32
  | .I8,.LT .S => 37#u32
  | .I8,.LT .U => 38#u32
  | .I8,.GT .S => 39#u32
  | .I8,.GT .U => 40#u32
  | .I8,.LE .S => 41#u32
  | .I8,.LE .U => 42#u32
  | .I8,.GE .S => 43#u32
  | .I8,.GE .U => 44#u32
  | .I16,.EQ => 45#u32
  | .I16,.NE => 46#u32
  | .I16,.LT .S => 47#u32
  | .I16,.LT .U => 48#u32
  | .I16,.GT .S => 49#u32
  | .I16,.GT .U => 50#u32
  | .I16,.LE .S => 51#u32
  | .I16,.LE .U => 52#u32
  | .I16,.GE .S => 53#u32
  | .I16,.GE .U => 54#u32
  | .I32,.EQ => 55#u32
  | .I32,.NE => 56#u32
  | .I32,.LT .S => 57#u32
  | .I32,.LT .U => 58#u32
  | .I32,.GT .S => 59#u32
  | .I32,.GT .U => 60#u32
  | .I32,.LE .S => 61#u32
  | .I32,.LE .U => 62#u32
  | .I32,.GE .S => 63#u32
  | .I32,.GE .U => 64#u32
  | .I64,.EQ => 214#u32
  | .I64,.NE => 215#u32
  | .I64,.LT _ => 216#u32
  | .I64,.GT _ => 217#u32
  | .I64,.LE _ => 218#u32
  | .I64,.GE _ => 219#u32

theorem integer_compare_width_val (ty : Jnn) :
    (integerCompareWidth ty).val = lsize (lanetype_Jnn ty) := by cases ty <;> rfl

theorem integer_compare_index_roundtrip (op : vrelop_Jnn_N) :
    UScalar.cast .U16 (UScalar.cast .U32 (integerCompareIndex op)) = integerCompareIndex op := by
  cases op <;> (try rename_i sign; cases sign) <;> rfl

theorem integer_compare_dispatch_eq (ty : Jnn) (op : vrelop_Jnn_N) (x y : U128)
    (supported : Spec.Simd.integerCompareSupported ty op) :
    runtime.interp.simd.compare_lanes (integerCompareOpcode ty op) x y =
      (runtime.interp.simd.compare_lanes_loop x y (integerCompareWidth ty)
        (UScalar.cast .U32 (integerCompareIndex op)) false 0#u128 0#u32) := by
  cases ty <;> cases op <;> (try rename_i sign; cases sign)
  all_goals simp only [Spec.Simd.integerCompareSupported] at supported
  all_goals try contradiction
  all_goals unfold runtime.interp.simd.compare_lanes integerCompareOpcode integerCompareWidth integerCompareIndex
  all_goals with_unfolding_all change (Aeneas.Std.bind (Aeneas.Std.bind (Result.ok _) _) _) = _
  all_goals simp only [bind_ok]
  all_goals rfl

end Itasca.Runtime.Interp.Simd

end

end

/-! ## CompareLanes -/

section

/-!
Integer comparison loops and lane results.

Main declarations: `integer_compare_loop` and `integer_compare_lanes`. A direct consumer is `Interp.Simd.Integer.CompareMaskBits`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem integer_compare_loop (op : vrelop_Jnn_N) (x y : U128) (width : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64) :
    runtime.interp.simd.compare_lanes_loop x y width (UScalar.cast .U32 (integerCompareIndex op)) false 0#u128 0#u32
      ⦃ result => ∀ j, j < 128/width.val → laneBits width.val j result.bv =
        comparisonBits width.val (Spec.Simd.integerLaneCompare op (laneBits width.val j x.bv) (laneBits width.val j y.bv)) ⦄ := by
  apply comparison_loop x y 0#u128 width (UScalar.cast .U32 (integerCompareIndex op)) 0#u32 false
    positive widthBound (fun j => Spec.Simd.integerLaneCompare op (laneBits width.val j x.bv) (laneBits width.val j y.bv))
  · intro j valid a b aEq bEq
    simp only [Bool.false_eq_true,if_false,integer_compare_index_roundtrip]
    have aBound : a.val < 2^width.val := by rw [aEq]; exact BitVec.isLt _
    have bBound : b.val < 2^width.val := by rw [bEq]; exact BitVec.isLt _
    have aBits : a.bv.setWidth width.val = laneBits width.val j x.bv := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth]
      change a.val%2^width.val = _
      rw [Nat.mod_eq_of_lt aBound,aEq]
    have bBits : b.bv.setWidth width.val = laneBits width.val j y.bv := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth]
      change b.val%2^width.val = _
      rw [Nat.mod_eq_of_lt bBound,bEq]
    simpa only [aBits,bBits] using integer_compare_word op a b width positive widthBound aBound bBound
  · simp
  · simp
  · intro j after valid
    change ((0 : BitVec 128) >>> (width.val*j)).setWidth width.val = 0
    simp

@[step] theorem integer_compare_lanes (ty : Jnn) (op : vrelop_Jnn_N) (x y : U128)
    (supported : Spec.Simd.integerCompareSupported ty op) :
    runtime.interp.simd.compare_lanes (integerCompareOpcode ty op) x y ⦃ result =>
      ∀ j, j < 128/(integerCompareWidth ty).val → laneBits (integerCompareWidth ty).val j result.bv =
        comparisonBits (integerCompareWidth ty).val (Spec.Simd.integerLaneCompare op
          (laneBits (integerCompareWidth ty).val j x.bv) (laneBits (integerCompareWidth ty).val j y.bv)) ⦄ := by
  rw [integer_compare_dispatch_eq ty op x y supported]
  apply WP.spec_mono (integer_compare_loop op x y (integerCompareWidth ty)
    (by cases ty <;> decide) (by cases ty <;> decide))
  intro result lanes
  simpa using lanes

end Itasca.Runtime.Interp.Simd

end

/-! ## CompareMaskBits -/

section

/-!
Sign extension of packed comparison masks.

Main declarations: `comparison_bits_sign_extend`. A direct consumer is `Interp.Simd.Float.Compare`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem comparison_bits_sign_extend (width : Nat) (bound : width ≤ 64) (answer : Bool) :
    comparisonBits width answer = (BitVec.ofNat 1 (nat_of_bool answer)).signExtend width := by
  cases answer
  · simp [comparisonBits,nat_of_bool,BitVec.signExtend]
  · apply BitVec.eq_of_getLsbD_eq
    intro i valid
    simp only [comparisonBits,nat_of_bool,ite_true]
    change ((BitVec.allOnes 64).setWidth width).getLsbD i = _
    rw [BitVec.getLsbD_setWidth,BitVec.getLsbD_allOnes]
    have small : i < 64 := by omega
    simp [valid,small,BitVec.getLsbD_signExtend]

end Itasca.Runtime.Interp.Simd

end

/-! ## Compare -/

section

/-!
Integer comparison masks packed into the source result. Shared mask, lane and word facts remain below integer and floating-point comparison.
-/

/-! ## Simd Compare Packing -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt.Builtins Itasca.Runtime.Spec.Simd

theorem comparison_masks_lanes (ty : Jnn) (op : vrelop_Jnn_N) (x y : BitVec 128) :
    Map (lane_.mk_lane__0 ty) (comparisonMasks ty op x y) =
      (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
        laneOfBits (lanetype_Jnn ty) (comparisonBits (lsize (lanetype_Jnn ty))
          (integerLaneCompare op (laneBits (lsize (lanetype_Jnn ty)) j x)
            (laneBits (lsize (lanetype_Jnn ty)) j y))).toNat) := by
  simp only [comparisonMasks,comparisonAnswers,Map,List.map_map]
  apply List.map_congr_left
  intro j member
  simp only [Function.comp_apply,proj_uN_0,boolean_extend]
  rw [comparison_bits_sign_extend _ (by cases ty <;> decide)]
  cases ty <;> rfl

theorem integer_compare_packed (ty : Jnn) (op : vrelop_Jnn_N) (x y result : U128)
    (lanes : ∀ j, j < 128/lsize (lanetype_Jnn ty) →
      laneBits (lsize (lanetype_Jnn ty)) j result.bv =
        comparisonBits (lsize (lanetype_Jnn ty)) (integerLaneCompare op
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv))) :
    uN.mk_uN result.val = integerComparisonResult ty op x.bv y.bv := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty) (128/lsize (lanetype_Jnn ty)) result.bv.toNat
    (fun j => (comparisonBits (lsize (lanetype_Jnn ty)) (integerLaneCompare op
      (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv))).toNat)
    (by intro j valid; rw [←lane_bits_to_nat,lanes j valid])
  have covers : lsize (lanetype_Jnn ty)*(128/lsize (lanetype_Jnn ty)) = 128 := by cases ty <;> decide
  rw [covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  rw [integerComparisonResult,comparison_masks_lanes]
  exact congrArg uN.mk_uN packed.symm

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Compare Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem integer_compare_lanes_sound (ty : Jnn) (op : vrelop_Jnn_N) (x y : U128)
    (supported : Spec.Simd.integerCompareSupported ty op) :
    runtime.interp.simd.compare_lanes (integerCompareOpcode ty op) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VRELOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.integerCompareSource ty op)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (integer_compare_lanes ty op x y supported)
  intro result lanes
  rw [integer_compare_width_val] at lanes
  exact Spec.Simd.integer_comparison_step ty op x.bv y.bv result.bv supported
    (integer_compare_packed ty op x y result lanes)

theorem integer_compare_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (op : vrelop_Jnn_N) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (integerCompareOpcode ty op) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.compare_lanes (integerCompareOpcode ty op) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases op <;> (try rename_i sign; cases sign)
  all_goals unfold runtime.interp.simd.simd integerCompareOpcode
  all_goals with_unfolding_all rfl

@[step] theorem integer_compare_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (op : vrelop_Jnn_N) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) (supported : Spec.Simd.integerCompareSupported ty op) :
    runtime.interp.simd.simd floats (integerCompareOpcode ty op) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VRELOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.integerCompareSource ty op)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [integer_compare_simd_eq]
  step with integer_compare_lanes_sound ty op x y supported as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end

end

/-! ## ArithmeticWord -/

section

/-!
Word-level dispatch indices for integer lane arithmetic.

Main declarations: `integerArithmeticIndex`. A direct consumer is `Interp.Simd.Integer.ArithmeticLanes`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def integerArithmeticIndex (kind : IntegerArithmetic) : U32 :=
  match kind with | .add => 14#u32 | .sub => 17#u32 | .mul => 21#u32

theorem integer_arithmetic_word (kind : IntegerArithmetic) (width : U32)
    (a b : U64) (sa sb : I64) (widthBound : width.val ≤ 64) :
    integerBinaryWord (integerArithmeticIndex kind) width a b sa sb ⦃ result =>
      result.bv.setWidth width.val = integerArithmeticBits kind (a.bv.setWidth width.val) (b.bv.setWidth width.val) ⦄ := by
  cases kind
  all_goals unfold integerBinaryWord integerArithmeticIndex
  all_goals with_unfolding_all change (Result.ok _) ⦃ _ ⦄
  all_goals rw [WP.spec_ok]
  · with_unfolding_all change (a.bv+b.bv).setWidth width.val = _
    exact BitVec.setWidth_add _ _ widthBound
  · with_unfolding_all change (a.bv-b.bv).setWidth width.val = _
    rw [BitVec.sub_eq_add_neg,BitVec.setWidth_add _ _ widthBound,BitVec.setWidth_neg_of_le widthBound]
    exact (BitVec.sub_eq_add_neg _ _).symm
  · with_unfolding_all change (a.bv*b.bv).setWidth width.val = _
    exact BitVec.setWidth_mul _ _ widthBound

end Itasca.Runtime.Interp.Simd

end

/-! ## ArithmeticLanes -/

section

/-!
Integer arithmetic opcodes and lane calculations.

Main declarations: `integerArithmeticOpcode`. A direct consumer is `Interp.Simd.Float.Resize`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def integerArithmeticOpcode (ty : Jnn) (kind : IntegerArithmetic) : U32 :=
  match ty,kind with
  | .I8,.add => 110#u32 | .I8,.sub => 113#u32 | .I8,.mul => 117#u32
  | .I16,.add => 142#u32 | .I16,.sub => 145#u32 | .I16,.mul => 149#u32
  | .I32,.add => 174#u32 | .I32,.sub => 177#u32 | .I32,.mul => 181#u32
  | .I64,.add => 206#u32 | .I64,.sub => 209#u32 | .I64,.mul => 213#u32

theorem integer_arithmetic_opcode_index (ty : Jnn) (kind : IntegerArithmetic) :
    (integerArithmeticOpcode ty kind).val%32 = (integerArithmeticIndex kind).val := by
  cases ty <;> cases kind <;> decide

theorem lane_word_cast (width j : Nat) (x : BitVec 128) (a : U64)
    (value : a.val = (laneBits width j x).toNat) : a.bv.setWidth width = laneBits width j x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth]
  change a.val%2^width = _
  rw [value,Nat.mod_eq_of_lt (BitVec.isLt _)]

theorem integer_arithmetic_loop (ty : Jnn) (kind : IntegerArithmetic) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes_loop (integerArithmeticOpcode ty kind) x
      y (integerCompareWidth ty) 0#u128 0#u32 ⦃ result => ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerArithmeticBits kind
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  have widthEq := integer_compare_width_val ty
  rw [←widthEq]
  apply integer_binary_loop x y 0#u128 (integerCompareWidth ty) (integerArithmeticOpcode ty kind) 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = integerArithmeticBits kind (laneBits (integerCompareWidth ty).val j x.bv)
      (laneBits (integerCompareWidth ty).val j y.bv))
  · intro j valid a b sa sb remainder aEq bEq saEq sbEq remainderEq
    have exactIndex : remainder = integerArithmeticIndex kind := by
      apply UScalar.eq_of_val_eq
      exact remainderEq.trans (integer_arithmetic_opcode_index ty kind)
    subst remainder
    have aBits := lane_word_cast _ j x.bv a aEq
    have bBits := lane_word_cast _ j y.bv b bEq
    simpa only [aBits,bBits] using integer_arithmetic_word kind (integerCompareWidth ty) a b sa sb (by cases ty <;> decide)
  · simp
  · simp

theorem integer_arithmetic_dispatch_eq (ty : Jnn) (kind : IntegerArithmetic) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes (integerArithmeticOpcode ty kind) x y =
      (runtime.interp.simd.integer_binary_lanes_loop (integerArithmeticOpcode ty kind)
        x y (integerCompareWidth ty) 0#u128 0#u32) := by
  cases ty <;> cases kind
  all_goals unfold runtime.interp.simd.integer_binary_lanes integerArithmeticOpcode integerCompareWidth
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals rfl

@[step] theorem integer_arithmetic_lanes (ty : Jnn) (kind : IntegerArithmetic) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes (integerArithmeticOpcode ty kind) x y ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerArithmeticBits kind
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  rw [integer_arithmetic_dispatch_eq]
  apply WP.spec_mono (integer_arithmetic_loop ty kind x y)
  intro result lanes
  simpa using lanes

end Itasca.Runtime.Interp.Simd

end

/-! ## UnaryWord -/

section

/-!
Word and lane interpretations of unary SIMD operations.

Main declarations: `unaryWord` and `unaryLane`. A direct consumer is `Interp.Simd.Integer.UnaryBits`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

def unaryWord (action : U32) (value : U64) (signedValue : I64) : U64 :=
  match action with
  | 0#uscalar => if signedValue < 0#i64
      then core.num.U64.wrapping_sub 0#u64 (IScalar.hcast .U64 signedValue)
      else IScalar.hcast .U64 signedValue
  | 1#uscalar => core.num.U64.wrapping_sub 0#u64 value
  | 2#uscalar => UScalar.cast .U64 (⟨BitVec.ofNat 32 (Primitive.countBits 64 value.val)⟩ : U32)
  | _ => value

theorem unary_word (action : U32) (value : U64) (signedValue : I64) :
    (match action with
      | 0#uscalar => if signedValue < 0#i64
          then Aeneas.Std.bind (Aeneas.Std.lift (IScalar.hcast .U64 signedValue))
            (fun cast => Result.ok (core.num.U64.wrapping_sub 0#u64 cast))
          else Result.ok (IScalar.hcast .U64 signedValue)
      | 1#uscalar => Result.ok (core.num.U64.wrapping_sub 0#u64 value)
      | 2#uscalar => Aeneas.Std.bind (core.num.U64.count_ones value)
          (fun count => Result.ok (UScalar.cast .U64 count))
      | _ => Result.ok value) = .ok (unaryWord action value signedValue) := by
  unfold unaryWord
  split
  · split <;> simp only [Aeneas.Std.lift,Aeneas.Std.bind_ok]
  · rfl
  · simp only [core.num.U64.count_ones,bind_ok]
  · rfl

@[step] theorem unary_word_effect (action : U32) (value : U64) (signedValue : I64) :
    (match action with
      | 0#uscalar => if signedValue < 0#i64 then
          Aeneas.Std.bind (Aeneas.Std.lift (IScalar.hcast .U64 signedValue))
            (fun cast => Result.ok (core.num.U64.wrapping_sub 0#u64 cast))
        else Result.ok (IScalar.hcast .U64 signedValue)
      | 1#uscalar => Result.ok (core.num.U64.wrapping_sub 0#u64 value)
      | 2#uscalar => Aeneas.Std.bind (core.num.U64.count_ones value)
          (fun count => Result.ok (UScalar.cast .U64 count))
      | _ => Result.ok value) ⦃ out => out = unaryWord action value signedValue ⦄ := by
  rw [unary_word]
  exact WP.spec.ret rfl

def unaryLane (action : U32) (width : Nat) (bits : BitVec width) : BitVec width :=
  (unaryWord action ⟨bits.setWidth 64⟩ ⟨bits.signExtend 64⟩).bv.setWidth width

def unaryAll (width : Nat) (x : BitVec 128) : Nat → Bool
  | 0 => true
  | n+1 => unaryAll width x n && ((⟨(laneBits width n x).setWidth 64⟩ : U64) != 0#u64)

def unarySigns (width : Nat) (x : BitVec 128) : Nat → BitVec 32
  | 0 => 0
  | n+1 => unarySigns width x n |||
      ((((laneBits width n x).setWidth 64 >>> (width-1)).setWidth 32) <<< n)
end Itasca.Runtime.Interp.Simd

end

/-! ## UnaryWords -/

section

/-!
Unary integer lane arithmetic and iteration. Specialized all-true, sign-mask and population-count adapters remain separate consumers.
-/

/-! ## Simd Unary Loop -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem integer_unary_loop (width action : U32) (x initial : U128)
    (all : Bool) (signs i : U32) (lower : 8 ≤ width.val) (upper : width.val ≤ 64)
    (position : i.val ≤ 128/width.val)
    (initializedPrefix : ∀ j, j < i.val → laneBits width.val j initial.bv =
      unaryLane action width.val (laneBits width.val j x.bv))
    (allPrefix : all = unaryAll width.val x.bv i.val)
    (signPrefix : signs.bv = unarySigns width.val x.bv i.val) :
    runtime.interp.simd.integer_unary_lanes_loop x width action initial all signs i ⦃ out =>
      (∀ j, j < 128/width.val → laneBits width.val j out.1.bv =
        unaryLane action width.val (laneBits width.val j x.bv)) ∧
      out.2.1 = unaryAll width.val x.bv (128/width.val) ∧
      out.2.2.bv = unarySigns width.val x.bv (128/width.val) ⦄ := by
  unfold runtime.interp.simd.integer_unary_lanes_loop
  apply loop.spec_decr_nat (fun p => 128/width.val-p.2.2.2.val)
    (fun p => p.2.2.2.val ≤ 128/width.val ∧
      (∀ j, j < p.2.2.2.val → laneBits width.val j p.1.bv =
        unaryLane action width.val (laneBits width.val j x.bv)) ∧
      p.2.1 = unaryAll width.val x.bv p.2.2.2.val ∧
      p.2.2.1.bv = unarySigns width.val x.bv p.2.2.2.val)
  · rintro ⟨current,all,signs,index⟩ ⟨indexBound,initialized,allEq,signEq⟩
    dsimp only at indexBound initialized allEq signEq
    unfold runtime.interp.simd.integer_unary_lanes_loop.body
    step as ⟨count,countEq⟩
    split
    · rename_i more
      have less : index.val < 128/width.val := by scalar_tac
      have range := lane_range width.val index.val less
      have countBound : 128/width.val ≤ 16 := Nat.div_le_div_left lower (by decide)
      step with lane_bits x width index (by omega) upper (by omega) as ⟨value,input⟩
      step with signed_bits value width (by omega) upper as ⟨signedValue,signedEq⟩
      step with unary_word_effect action value signedValue as ⟨word,wordEq⟩
      subst word
      step with put_lanes current width index (unaryWord action value signedValue)
        (by omega) upper range as ⟨updated,same,other⟩
      have valueEq : value = ⟨(laneBits width.val index.val x.bv).setWidth 64⟩ :=
        (UScalar.eq_equiv_bv_eq _ _).mpr input
      have signedValueEq : signedValue = ⟨(laneBits width.val index.val x.bv).signExtend 64⟩ := by
        apply (IScalar.eq_equiv_bv_eq _ _).mpr
        have truncated : value.bv.setWidth width.val = laneBits width.val index.val x.bv :=
          (congrArg (BitVec.setWidth width.val) input).trans
            ((BitVec.setWidth_setWidth_of_le _ upper).trans (BitVec.setWidth_eq _))
        exact signedEq.trans (congrArg (BitVec.signExtend 64) truncated)
      have allUpdate : (if all then Result.ok (value != 0#u64) else Result.ok false) =
          Result.ok (all && (value != 0#u64)) := by cases all <;> rfl
      rw [allUpdate,bind_ok]
      step as ⟨last,lastEq⟩
      step as ⟨sign,signValue,signBits⟩
      simp only [lift,bind_ok]
      step as ⟨shifted,shiftedValue,shiftedBits⟩
      try simp only [lift,bind_ok]
      step as ⟨next,nextEq⟩
      refine ⟨?_,?_,?_,?_,?_⟩
      · omega
      · intro j bound
        by_cases eq : j=index.val
        · subst j
          simpa only [unaryLane,valueEq,signedValueEq] using same
        · exact (other j (lane_range _ _ (by omega)) eq).trans (initialized j (by omega))
      · simp only [nextEq,unaryAll,allEq,valueEq]
      · simp only [nextEq,unarySigns]
        change signs.bv ||| shifted.bv = _
        apply congrArg₂ (· ||| ·) signEq
        have shiftedEq := shiftedBits.trans
          (congrArg (fun b : BitVec 32 => b <<< index.val) (UScalar.cast_bv_eq .U32 sign))
        have signEq2 : sign.bv = (laneBits width.val index.val x.bv).setWidth 64 >>> (width.val-1) :=
          signBits.trans ((congrArg (fun b : BitVec 64 => b >>> last.val) input).trans
            (congrArg (fun n => (laneBits width.val index.val x.bv).setWidth 64 >>> n) lastEq))
        exact shiftedEq.trans (congrArg (fun b : BitVec 64 => b.setWidth 32 <<< index.val) signEq2)
      · omega
    · have finished : index.val=128/width.val := by scalar_tac
      simpa [finished] using And.intro initialized (And.intro allEq signEq)
  · exact ⟨position,initializedPrefix,allPrefix,signPrefix⟩
end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Unary -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

inductive UnaryAction where | absolute | negate | population | allTrue | bitmask

def unaryAction : UnaryAction → U32
  | .absolute => 0#u32
  | .negate => 1#u32
  | .population => 2#u32
  | .allTrue => 3#u32
  | .bitmask => 4#u32

def unaryOpcode (ty : Jnn) (action : UnaryAction) : U32 :=
  match ty,action with
  | .I8,.absolute => 96#u32
  | .I8,.negate => 97#u32
  | .I8,.population => 98#u32
  | .I8,.allTrue => 99#u32
  | .I8,.bitmask => 100#u32
  | .I16,.absolute => 128#u32
  | .I16,.negate => 129#u32
  | .I16,.population => 130#u32
  | .I16,.allTrue => 131#u32
  | .I16,.bitmask => 132#u32
  | .I32,.absolute => 160#u32
  | .I32,.negate => 161#u32
  | .I32,.population => 162#u32
  | .I32,.allTrue => 163#u32
  | .I32,.bitmask => 164#u32
  | .I64,.absolute => 192#u32
  | .I64,.negate => 193#u32
  | .I64,.population => 194#u32
  | .I64,.allTrue => 195#u32
  | .I64,.bitmask => 196#u32

def UnaryOutcome (ty : Jnn) (action : UnaryAction) (x result : U128) : Prop :=
  let width := lsize (lanetype_Jnn ty)
  match action with
  | .allTrue => result = UScalar.cast .U128 (UScalar.cast_fromBool .U32 (unaryAll width x.bv (128/width)))
  | .bitmask => result = UScalar.cast .U128 (⟨unarySigns width x.bv (128/width)⟩ : U32)
  | _ => ∀ j, j < 128/width → laneBits width j result.bv =
      unaryLane (unaryAction action) width (laneBits width j x.bv)

@[step] theorem integer_unary_lanes (ty : Jnn) (action : UnaryAction) (x : U128) :
    runtime.interp.simd.integer_unary_lanes (unaryOpcode ty action) x
      ⦃ result => UnaryOutcome ty action x result ⦄ := by
  unfold runtime.interp.simd.integer_unary_lanes
  have opcodeBound : 96 ≤ (unaryOpcode ty action).val := by cases ty <;> cases action <;> decide
  step as ⟨difference,differenceEq⟩
  step as ⟨quotient,quotientEq⟩
  have quotientBound : quotient.val < 32 := by
    cases ty <;> cases action <;> simp only [unaryOpcode] at differenceEq <;> scalar_tac
  step as ⟨width,widthEq,widthBits⟩
  have actualWidth : width = shiftWidth ty := by
    apply UScalar.eq_of_val_eq
    cases ty <;> cases action <;> simp only [unaryOpcode,shiftWidth] at * <;> scalar_tac
  subst width
  step as ⟨selected,selectedEq⟩
  have actualAction : selected = unaryAction action := by
    apply UScalar.eq_of_val_eq
    cases ty <;> cases action <;> simp only [unaryOpcode,unaryAction] at * <;> scalar_tac
  subst selected
  step with integer_unary_loop (shiftWidth ty) (unaryAction action) x 0#u128 true 0#u32 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide) (by cases ty <;> decide)
    (by intro j invalid; change j<0 at invalid; omega) rfl rfl as ⟨result,all,signs,lanes,allEq,signEq⟩
  try dsimp only at lanes allEq signEq ⊢
  cases action
  all_goals simp only [unaryAction,
    show (0#u32=3#u32) ↔ False by decide, show (0#u32=4#u32) ↔ False by decide,
    show (1#u32=3#u32) ↔ False by decide, show (1#u32=4#u32) ↔ False by decide,
    show (2#u32=3#u32) ↔ False by decide, show (2#u32=4#u32) ↔ False by decide,
    show (4#u32=3#u32) ↔ False by decide, ite_false,ite_true,
    lift,bind_ok,WP.spec_ok,UnaryOutcome]
  case absolute | negate | population => cases ty <;> with_unfolding_all exact lanes
  case allTrue =>
    have bridge : ∀ answer : Bool, UScalar.cast_fromBool .U128 answer =
        UScalar.cast .U128 (UScalar.cast_fromBool .U32 answer) := by
      intro answer; cases answer <;> decide
    rw [bridge]
    apply congrArg (fun answer => UScalar.cast .U128 (UScalar.cast_fromBool .U32 answer))
    cases ty <;> with_unfolding_all exact allEq
  case bitmask =>
    apply congrArg (UScalar.cast .U128)
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    cases ty <;> with_unfolding_all exact signEq
end Itasca.Runtime.Interp.Simd

end

end

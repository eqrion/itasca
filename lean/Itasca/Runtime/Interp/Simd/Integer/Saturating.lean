import Itasca.Runtime.Interp.Simd.Integer.Saturation
import Itasca.Runtime.Spec.Simd.IntegerSaturating
import Itasca.Runtime.Interp.Simd.Integer.ArithmeticLanes

/-!
Saturating lane arithmetic: scalar word calculations, lane iteration, packing and source correspondence. The final handler facts feed SIMD dispatch and machine execution; independently consumed primitives remain below this construction.
-/

/-! ## Simd Integer Saturating Word -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def integerSaturatingIndex (kind : IntegerSaturating) : U32 :=
  match kind with | .addS => 15#u32 | .addU => 16#u32 | .subS => 18#u32 | .subU => 19#u32

theorem integer_saturating_word (kind : IntegerSaturating) (width : U32)
    (a b : U64) (sa sb : I64) (supported : width.val ∈ [8,16,32])
    (aBound : a.val < 2^width.val) (bBound : b.val < 2^width.val)
    (saEq : sa.val = (a.bv.setWidth width.val).toInt)
    (sbEq : sb.val = (b.bv.setWidth width.val).toInt) :
    integerBinaryWord (integerSaturatingIndex kind) width a b sa sb ⦃ result =>
      result.bv.setWidth width.val = integerSaturatingBits kind (a.bv.setWidth width.val) (b.bv.setWidth width.val) ⦄ := by
  have aValue : (a.bv.setWidth width.val).toNat = a.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt aBound
  have bValue : (b.bv.setWidth width.val).toNat = b.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt bBound
  have aCast : (a.val:Int).bmod (2^128) = a.val := Int.bmod_eq_of_le (by scalar_tac) (by scalar_tac)
  have bCast : (b.val:Int).bmod (2^128) = b.val := Int.bmod_eq_of_le (by scalar_tac) (by scalar_tac)
  cases kind
  all_goals unfold integerBinaryWord integerSaturatingIndex
  all_goals with_unfolding_all change (Aeneas.Std.bind _ _) ⦃ _ ⦄
  all_goals step* <;> simp_all [integerSaturatingBits,aCast,bCast,I128.min,I128.max] <;> scalar_tac

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Integer Saturating Lanes -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def integerSaturatingOpcode (ty : Jnn) (kind : IntegerSaturating) : U32 :=
  match ty,kind with
  | .I8,.addS => 111#u32 | .I8,.addU => 112#u32 | .I8,.subS => 114#u32 | .I8,.subU => 115#u32
  | .I16,.addS => 143#u32 | .I16,.addU => 144#u32 | .I16,.subS => 146#u32 | .I16,.subU => 147#u32
  | .I32,.addS => 175#u32 | .I32,.addU => 176#u32 | .I32,.subS => 178#u32 | .I32,.subU => 179#u32
  | .I64,.addS => 207#u32 | .I64,.addU => 208#u32 | .I64,.subS => 210#u32 | .I64,.subU => 211#u32

theorem integer_saturating_opcode_index (ty : Jnn) (kind : IntegerSaturating) :
    (integerSaturatingOpcode ty kind).val%32 = (integerSaturatingIndex kind).val := by
  cases ty <;> cases kind <;> decide

theorem integer_saturating_loop (ty : Jnn) (kind : IntegerSaturating) (x y : U128)
    (supported : integerSaturatingSupported ty kind) :
    runtime.interp.simd.integer_binary_lanes_loop (integerSaturatingOpcode ty kind) x
      y (integerCompareWidth ty) 0#u128 0#u32 ⦃ result => ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerSaturatingBits kind
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  have widthEq := integer_compare_width_val ty
  rw [←widthEq]
  apply integer_binary_loop x y 0#u128 (integerCompareWidth ty) (integerSaturatingOpcode ty kind) 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = integerSaturatingBits kind (laneBits (integerCompareWidth ty).val j x.bv)
      (laneBits (integerCompareWidth ty).val j y.bv))
  · intro j valid a b sa sb remainder aEq bEq saEq sbEq remainderEq
    have exactIndex : remainder = integerSaturatingIndex kind := by
      apply UScalar.eq_of_val_eq
      exact remainderEq.trans (integer_saturating_opcode_index ty kind)
    subst remainder
    have aBits := lane_word_cast _ j x.bv a aEq
    have bBits := lane_word_cast _ j y.bv b bEq
    simpa only [aBits,bBits] using integer_saturating_word kind (integerCompareWidth ty) a b sa sb
      (by cases ty <;> simp_all [integerSaturatingSupported,integerCompareWidth])
      (by rw [aEq]; exact BitVec.isLt _) (by rw [bEq]; exact BitVec.isLt _) saEq sbEq
  · simp
  · simp

theorem integer_saturating_dispatch_eq (ty : Jnn) (kind : IntegerSaturating) (x y : U128) :
    runtime.interp.simd.integer_binary_lanes (integerSaturatingOpcode ty kind) x y =
      (runtime.interp.simd.integer_binary_lanes_loop (integerSaturatingOpcode ty kind)
        x y (integerCompareWidth ty) 0#u128 0#u32) := by
  cases ty <;> cases kind
  all_goals unfold runtime.interp.simd.integer_binary_lanes integerSaturatingOpcode integerCompareWidth
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals rfl

@[step] theorem integer_saturating_lanes (ty : Jnn) (kind : IntegerSaturating) (x y : U128)
    (supported : integerSaturatingSupported ty kind) :
    runtime.interp.simd.integer_binary_lanes (integerSaturatingOpcode ty kind) x y ⦃ result =>
      ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerSaturatingBits kind
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  rw [integer_saturating_dispatch_eq]
  apply WP.spec_mono (integer_saturating_loop ty kind x y supported)
  intro result lanes
  simpa using lanes

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Integer Saturating Packing -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem integer_saturating_packed (ty : Jnn) (kind : IntegerSaturating) (x y result : U128)
    (lanes : ∀ j, j < 128/lsize (lanetype_Jnn ty) →
      laneBits (lsize (lanetype_Jnn ty)) j result.bv = integerSaturatingBits kind
        (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv)) :
    uN.mk_uN result.val = integerSaturatingResult ty kind x.bv y.bv := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty) (128/lsize (lanetype_Jnn ty)) result.bv.toNat
    (fun j => (integerSaturatingBits kind (laneBits (lsize (lanetype_Jnn ty)) j x.bv)
      (laneBits (lsize (lanetype_Jnn ty)) j y.bv)).toNat)
    (by intro j valid; rw [←lane_bits_to_nat,lanes j valid])
  rw [shape_of_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  unfold integerSaturatingResult saturatingWords Map
  rw [List.map_map]
  have same (bits : Nat) : laneOfBits (lanetype_Jnn ty) bits = .mk_lane__0 ty (.mk_uN bits) := by cases ty <;> rfl
  simp only [same] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

end Itasca.Runtime.Interp.Simd

end

/-! ## Simd Integer Saturating Sound -/

section

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem integer_saturating_lanes_sound (ty : Jnn) (op : Spec.Simd.IntegerSaturating) (x y : U128)
    (supported : Spec.Simd.integerSaturatingSupported ty op) :
    runtime.interp.simd.integer_binary_lanes (integerSaturatingOpcode ty op) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VBINOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.integerSaturatingSource ty op)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (integer_saturating_lanes ty op x y supported)
  intro result lanes
  exact Spec.Simd.integer_saturating_step ty op x.bv y.bv result.bv supported
    (integer_saturating_packed ty op x y result lanes)

theorem integer_saturating_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (op : Spec.Simd.IntegerSaturating) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) (supported : Spec.Simd.integerSaturatingSupported ty op) :
    runtime.interp.simd.simd floats (integerSaturatingOpcode ty op) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.integer_binary_lanes (integerSaturatingOpcode ty op) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases op
  all_goals simp only [Spec.Simd.integerSaturatingSupported] at supported
  all_goals try contradiction
  all_goals unfold runtime.interp.simd.simd integerSaturatingOpcode
  all_goals with_unfolding_all rfl

@[step] theorem integer_saturating_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (op : Spec.Simd.IntegerSaturating) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) (supported : Spec.Simd.integerSaturatingSupported ty op) :
    runtime.interp.simd.simd floats (integerSaturatingOpcode ty op) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VBINOP (Spec.Simd.shapeOf (lanetype_Jnn ty)) (Spec.Simd.integerSaturatingSource ty op)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [integer_saturating_simd_eq floats ty op offset laneIndex bits x y z memory supported]
  step with integer_saturating_lanes_sound ty op x y supported as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

end

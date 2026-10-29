import Itasca.Runtime.Interp.Simd.Integer.BinaryLoop
import Itasca.Runtime.Spec.Simd.IntegerMinMax
import Itasca.Runtime.Interp.Simd.Integer.ArithmeticLanes

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

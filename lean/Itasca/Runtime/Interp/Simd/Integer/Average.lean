import Itasca.Runtime.Interp.Simd.Integer.BinaryLoop
import Itasca.Runtime.Spec.Simd.Average
import Itasca.Runtime.Interp.Simd.Integer.ArithmeticLanes

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

theorem averageOpcode_index (ty : Jnn) : (averageOpcode ty).val%32 = (27#u32).val := by
  cases ty <;> decide

theorem average_loop (ty : Jnn) (x y : U128)
    (supported : averageSupported ty) :
    runtime.interp.simd.integer_binary_lanes_loop (averageOpcode ty) x
      y (integerCompareWidth ty) 0#u128 0#u32 ⦃ result => ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        laneBits (lsize (lanetype_Jnn ty)) j result.bv = averageBits
          (laneBits (lsize (lanetype_Jnn ty)) j x.bv) (laneBits (lsize (lanetype_Jnn ty)) j y.bv) ⦄ := by
  have widthEq := integerCompareWidth_val ty
  rw [←widthEq]
  apply integer_binary_loop x y 0#u128 (integerCompareWidth ty) (averageOpcode ty) 0#u32
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = averageBits (laneBits (integerCompareWidth ty).val j x.bv)
      (laneBits (integerCompareWidth ty).val j y.bv))
  · intro j valid a b sa sb remainder aEq bEq _saEq _sbEq remainderEq
    have exactIndex : remainder = (27#u32) := by
      apply UScalar.eq_of_val_eq
      exact remainderEq.trans (averageOpcode_index ty)
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
    (by intro j valid; rw [←laneBits_toNat,lanes j valid])
  rw [shapeOf_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
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

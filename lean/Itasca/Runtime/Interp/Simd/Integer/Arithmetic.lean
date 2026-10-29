import Itasca.Runtime.Interp.Simd.Integer.ArithmeticLanes
import Itasca.Runtime.Spec.Simd.IntegerArithmetic

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

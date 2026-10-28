import Exec.Interp.Simd.Integer.SimdIntegerArithmeticPacking
import Exec.Spec.SimdIntegerArithmeticStep
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

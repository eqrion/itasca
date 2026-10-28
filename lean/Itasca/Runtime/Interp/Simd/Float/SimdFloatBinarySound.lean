import Itasca.Runtime.Interp.Simd.Float.SimdFloatBinaryLanes
import Itasca.Runtime.Spec.SimdFloatBinaryChoices
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Platform

@[step] theorem float_binary_lanes_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vbinop_Fnn_N) (x y : U128) :
    runtime.interp.simd.float_binary_lanes floats (floatBinaryOpcode ty op) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        .VBINOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatBinarySource ty op)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (float_binary_lanes floats laws ty op x y)
  intro result allowed
  exact Spec.Simd.float_binary_step ty op x.bv y.bv result.bv allowed

theorem float_binary_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (op : vbinop_Fnn_N) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatBinaryOpcode ty op) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.float_binary_lanes floats (floatBinaryOpcode ty op) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases op
  all_goals unfold runtime.interp.simd.simd floatBinaryOpcode
  all_goals with_unfolding_all rfl

@[step] theorem float_binary_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vbinop_Fnn_N)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatBinaryOpcode ty op) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          .VBINOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatBinarySource ty op)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [float_binary_simd_eq]
  step with float_binary_lanes_sound floats laws ty op x y as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

import Exec.Interp.Simd.Float.SimdFloatUnaryLanes
import Exec.Spec.SimdFloatUnaryChoices
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Platform

@[step] theorem float_unary_lanes_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vunop_Fnn_N) (x : U128) :
    runtime.interp.simd.float_unary_lanes floats (floatUnaryOpcode ty op) x ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),
        .VUNOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatUnarySource ty op)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (float_unary_lanes floats laws ty op x)
  intro result allowed
  exact Spec.Simd.float_unary_step ty op x.bv result.bv allowed

theorem float_unary_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (op : vunop_Fnn_N) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatUnaryOpcode ty op) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.float_unary_lanes floats (floatUnaryOpcode ty op) x)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases op
  all_goals unfold runtime.interp.simd.simd floatUnaryOpcode
  all_goals with_unfolding_all rfl

@[step] theorem float_unary_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (op : vunop_Fnn_N)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatUnaryOpcode ty op) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),
          .VUNOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.floatUnarySource ty op)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [float_unary_simd_eq]
  step with float_unary_lanes_sound floats laws ty op x as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

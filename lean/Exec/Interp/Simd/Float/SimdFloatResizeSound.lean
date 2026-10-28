import Exec.Interp.Simd.Float.SimdFloatResizeLanes
import Exec.Spec.SimdFloatResizeStep
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Platform

@[step] theorem float_resize_lanes_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (kind : Spec.Simd.FloatResize) (x : U128) :
    runtime.interp.simd.convert_lanes floats (floatResizeOpcode kind) x ⦃ out =>
      ∃ result, out = .Ok result ∧
      Step_pure [.VCONST .V128 (.mk_uN x.val),
        .VCVTOP (Spec.Simd.shapeOf (lanetype_Fnn kind.output)) (Spec.Simd.shapeOf (lanetype_Fnn kind.input))
          (Spec.Simd.floatResizeSource kind)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (float_resize_lanes floats laws kind x)
  rintro out ⟨result,rfl,allowed,zeroed⟩
  exact ⟨result,rfl,Spec.Simd.float_resize_step kind x.bv result.bv allowed zeroed⟩

theorem float_resize_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (kind : Spec.Simd.FloatResize) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatResizeOpcode kind) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.convert_lanes floats (floatResizeOpcode kind) x)
        (fun result => Result.ok (result,memory)) := by
  cases kind
  all_goals unfold runtime.interp.simd.simd floatResizeOpcode
  all_goals with_unfolding_all rfl

@[step] theorem float_resize_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (kind : Spec.Simd.FloatResize)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (floatResizeOpcode kind) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),
          .VCVTOP (Spec.Simd.shapeOf (lanetype_Fnn kind.output)) (Spec.Simd.shapeOf (lanetype_Fnn kind.input))
            (Spec.Simd.floatResizeSource kind)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [float_resize_simd_eq]
  step with float_resize_lanes_sound floats laws kind x as ⟨out,value,eq,source⟩
  subst out
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

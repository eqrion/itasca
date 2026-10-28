import Exec.Interp.Simd.Integer.SimdConvertIntegerLanes
import Exec.Spec.SimdConvertIntegerStep
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Platform

@[step] theorem convert_integer_lanes_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (signed : Bool) (x : U128) :
    runtime.interp.simd.convert_lanes floats (convertIntegerOpcode ty signed) x ⦃ out =>
      ∃ result, out = .Ok result ∧
      Step_pure [.VCONST .V128 (.mk_uN x.val),
        .VCVTOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.shapeOf .I32)
          (Spec.Simd.convertIntegerSource ty (if signed then .S else .U))]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (convert_integer_lanes floats laws ty signed x)
  rintro out ⟨result,rfl,allowed⟩
  exact ⟨result,rfl,Spec.Simd.convert_integer_step ty (if signed then .S else .U) x.bv result.bv allowed⟩

theorem convert_integer_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (convertIntegerOpcode ty signed) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.convert_lanes floats (convertIntegerOpcode ty signed) x)
        (fun result => Result.ok (result,memory)) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.simd convertIntegerOpcode
  all_goals with_unfolding_all rfl

@[step] theorem convert_integer_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (laws : FloatOpsCorrect floats) (ty : Fnn) (signed : Bool)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (convertIntegerOpcode ty signed) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),
          .VCVTOP (Spec.Simd.shapeOf (lanetype_Fnn ty)) (Spec.Simd.shapeOf .I32)
            (Spec.Simd.convertIntegerSource ty (if signed then .S else .U))]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [convert_integer_simd_eq]
  step with convert_integer_lanes_sound floats laws ty signed x as ⟨out,value,eq,source⟩
  subst out
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

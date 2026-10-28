import Exec.Interp.Simd.Common.SimdTruncSatLanes
import Exec.Spec.SimdTruncSatStep
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Platform

@[step] theorem trunc_sat_lanes_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool) (x : U128) :
    runtime.interp.simd.convert_lanes floats (truncSatOpcode ty signed) x ⦃ out =>
      ∃ result, out = .Ok result ∧
      Step_pure [.VCONST .V128 (.mk_uN x.val),
        .VCVTOP (Spec.Simd.shapeOf .I32) (Spec.Simd.shapeOf (lanetype_Fnn ty))
          (Spec.Simd.truncSatSource ty (if signed then .S else .U))]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (trunc_sat_lanes floats ty signed x)
  rintro out ⟨result,rfl,allowed,zeroed⟩
  exact ⟨result,rfl,Spec.Simd.trunc_sat_step ty (if signed then .S else .U) x.bv result.bv allowed zeroed⟩

theorem trunc_sat_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (truncSatOpcode ty signed) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.convert_lanes floats (truncSatOpcode ty signed) x)
        (fun result => Result.ok (result,memory)) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.simd truncSatOpcode
  all_goals with_unfolding_all rfl

@[step] theorem trunc_sat_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Fnn) (signed : Bool)
    (offset laneIndex : U32) (bits x y z : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (truncSatOpcode ty signed) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),
          .VCVTOP (Spec.Simd.shapeOf .I32) (Spec.Simd.shapeOf (lanetype_Fnn ty))
            (Spec.Simd.truncSatSource ty (if signed then .S else .U))]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [trunc_sat_simd_eq]
  step with trunc_sat_lanes_sound floats ty signed x as ⟨out,value,eq,source⟩
  subst out
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

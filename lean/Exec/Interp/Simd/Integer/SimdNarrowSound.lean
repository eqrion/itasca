import Exec.Interp.Simd.Integer.SimdNarrowPacking
import Exec.Spec.SimdNarrowSource
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem narrow_lanes_sound (ty : Spec.Simd.NarrowWidth) (signed : Bool) (x y : U128)
    :
    runtime.interp.simd.narrow_lanes (narrowOpcode ty signed) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
        (Spec.Simd.narrowSource ty signed)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (narrow_lanes ty signed x y)
  intro result lanes
  exact Spec.Simd.narrow_step ty signed x.bv y.bv result.bv
    (narrow_packed ty signed x y result lanes)

theorem narrow_simd_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Spec.Simd.NarrowWidth) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (narrowOpcode ty signed) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.narrow_lanes (narrowOpcode ty signed) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.simd narrowOpcode
  all_goals with_unfolding_all rfl

@[step] theorem narrow_simd_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Spec.Simd.NarrowWidth) (signed : Bool) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (narrowOpcode ty signed) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),.VCONST .V128 (.mk_uN y.val),
          (Spec.Simd.narrowSource ty signed)]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [narrow_simd_eq floats ty signed offset laneIndex bits x y z memory]
  step with narrow_lanes_sound ty signed x y as ⟨value,source⟩
  exact ⟨value,rfl,source⟩

end Itasca.Runtime.Interp.Simd

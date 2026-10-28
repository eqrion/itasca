import Exec.Interp.Simd.Integer.SimdNarrowLoop
import Exec.Spec.SimdNarrowSource
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def narrowWidth : NarrowWidth → U32 | .i8 => 8#u32 | .i16 => 16#u32

def narrowOpcode (ty : NarrowWidth) (signed : Bool) : U32 :=
  match ty,signed with
  | .i8,true => 101#u32 | .i8,false => 102#u32
  | .i16,true => 133#u32 | .i16,false => 134#u32

theorem narrow_dispatch_eq (ty : NarrowWidth) (signed : Bool) (x y : U128) :
    runtime.interp.simd.narrow_lanes (narrowOpcode ty signed) x y =
      (runtime.interp.simd.narrow_lanes_loop x y (narrowWidth ty) signed 0#u128 0#u32) := by
  cases ty <;> cases signed
  all_goals unfold runtime.interp.simd.narrow_lanes narrowOpcode narrowWidth
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals rfl

@[step] theorem narrow_lanes (ty : NarrowWidth) (signed : Bool) (x y : U128) :
    runtime.interp.simd.narrow_lanes (narrowOpcode ty signed) x y ⦃ result =>
      ∀ j, j < 128/ty.width → laneBits ty.width j result.bv = narrowLane ty.width signed x.bv y.bv j ⦄ := by
  rw [narrow_dispatch_eq]
  apply WP.spec_mono (narrow_loop x y 0#u128 (narrowWidth ty) 0#u32 signed (by cases ty <;> decide) (by simp) (by simp))
  intro result lanes
  cases ty <;> with_unfolding_all exact lanes

end Itasca.Runtime.Interp.Simd

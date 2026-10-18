import Exec.Interp.Simd.Integer.SimdNarrowLoop
import Exec.Spec.SimdNarrowSource
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd

def narrowWidth : NarrowWidth → U32 | .i8 => 8#u32 | .i16 => 16#u32

def narrowOpcode (ty : NarrowWidth) (signed : Bool) : U32 :=
  match ty,signed with
  | .i8,true => 101#u32 | .i8,false => 102#u32
  | .i16,true => 133#u32 | .i16,false => 134#u32

theorem narrowWidth_val (ty : NarrowWidth) : (narrowWidth ty).val = ty.width := by cases ty <;> rfl

theorem narrow_dispatch_eq (ty : NarrowWidth) (signed : Bool) (x y : U128) :
    runtime.interp.simd.narrow_lanes (narrowOpcode ty signed) x y =
      Aeneas.Std.bind (runtime.interp.simd.narrow_lanes_loop (narrowWidth ty) signed y x 0#u128 0#u32)
        runtime.interp.simd.vector := by
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
  step with narrow_loop x y 0#u128 (narrowWidth ty) 0#u32 signed (by cases ty <;> decide) (by simp) (by simp) as ⟨result,lanes⟩
  unfold runtime.interp.simd.vector
  rw [WP.spec_ok]
  cases ty <;> with_unfolding_all exact lanes

end Exec.Interp.Simd

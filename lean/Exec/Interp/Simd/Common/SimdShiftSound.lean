import Exec.Interp.Simd.Common.SimdShift
import Exec.Spec.SimdShiftSource
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd SpecExt.Builtins

theorem shift_packed (ty : Jnn) (kind : ShiftKind) (x result : U128) (amount : U32)
    (lanes : ∀ j, j < 128/lsize (lanetype_Jnn ty) →
      laneBits (lsize (lanetype_Jnn ty)) j result.bv =
        shiftBits kind (laneBits (lsize (lanetype_Jnn ty)) j x.bv)
          (amount.val % lsize (lanetype_Jnn ty))) :
    uN.mk_uN result.val = inv_lanes_ (shapeOf (lanetype_Jnn ty))
      (shiftLaneValues ty kind x.bv amount.val) := by
  have packed := pack_map_of_lanes (lanetype_Jnn ty) (128/lsize (lanetype_Jnn ty)) result.bv.toNat
    (fun j => (shiftBits kind (laneBits (lsize (lanetype_Jnn ty)) j x.bv)
      (amount.val % lsize (lanetype_Jnn ty))).toNat) (by
      intro j valid
      rw [←laneBits_toNat,lanes j valid])
  rw [shapeOf_covers,Nat.mod_eq_of_lt result.bv.isLt] at packed
  with_unfolding_all exact congrArg uN.mk_uN packed.symm

@[step] theorem shift_lanes_sound (ty : Jnn) (kind : ShiftKind) (x y : U128) :
    runtime.interp.simd.shift_lanes (shiftOpcode ty kind) x y ⦃ result =>
      Step_pure [.VCONST .V128 (.mk_uN x.val),
        .CONST .I32 (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 y).val)), shiftSource ty kind]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (shift_lanes ty kind x y)
  intro result lanes
  exact shift_step ty kind x.bv result.bv (UScalar.cast .U32 y).bv
    (shift_packed ty kind x result (UScalar.cast .U32 y) lanes)

theorem shift_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (kind : ShiftKind) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (shiftOpcode ty kind) offset laneIndex bits x y z memory =
      Aeneas.Std.bind (runtime.interp.simd.shift_lanes (shiftOpcode ty kind) x y)
        (fun result => Result.ok (core.result.Result.Ok result,memory)) := by
  cases ty <;> cases kind <;> unfold runtime.interp.simd.simd shiftOpcode <;> with_unfolding_all rfl

@[step] theorem shift_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Jnn) (kind : ShiftKind) (offset laneIndex : U32) (bits x y z : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (shiftOpcode ty kind) offset laneIndex bits x y z memory
      ⦃ result => ∃ value, result = (.Ok value,memory) ∧
        Step_pure [.VCONST .V128 (.mk_uN x.val),
          .CONST .I32 (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 y).val)),shiftSource ty kind]
          [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [shift_dispatch_eq]
  step with shift_lanes_sound ty kind x y as ⟨value,source⟩
  exact ⟨value,rfl,source⟩
end Itasca.Runtime.Interp.Simd

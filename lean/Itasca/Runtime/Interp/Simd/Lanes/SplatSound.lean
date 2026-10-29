import Itasca.Runtime.Interp.Simd.Lanes.Packing
import Itasca.Runtime.Spec.Simd.Shape

/-!
Opcode, input and source correspondence for scalar splatting.

Main declarations: `splatOpcode` and `splatInput`. A direct consumer is `Interp.Simd.Execution.PureUnary`.
-/

set_option maxRecDepth 4096
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

@[step] theorem splat_sound (ty : lanetype) (x : U64) (width : U32)
    (widthEq : width.val = lsize ty) :
    runtime.interp.simd.splat x width ⦃ result =>
      Step_pure [.CONST (unpack ty) (Spec.Simd.scalarInput ty x.bv), .VSPLAT (Spec.Simd.shapeOf ty)]
        [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  apply WP.spec_mono (splat_packed ty x width widthEq)
  intro result packed
  exact Spec.Simd.splat_step ty x.bv result.bv packed

def splatOpcode (ty : lanetype) : U32 :=
  match ty with
  | .I8 => 15#u32
  | .I16 => 16#u32
  | .I32 => 17#u32
  | .I64 => 18#u32
  | .F32 => 19#u32
  | .F64 => 20#u32

def splatInput (ty : lanetype) (a : U128) : U64 :=
  match ty with
  | .I8 | .I16 | .I32 | .F32 => UScalar.cast .U64 (UScalar.cast .U32 a)
  | .I64 | .F64 => UScalar.cast .U64 a

def splatWidth (ty : lanetype) : U32 :=
  match ty with
  | .I8 => 8#u32
  | .I16 => 16#u32
  | .I32 | .F32 => 32#u32
  | .I64 | .F64 => 64#u32

theorem splat_width_val (ty : lanetype) : (splatWidth ty).val = lsize ty := by
  cases ty <;> rfl

theorem splat_lanes_eq (ty : lanetype) (a : U128) :
    runtime.interp.simd.splat_lanes (splatOpcode ty) a =
      (runtime.interp.simd.splat (splatInput ty a) (splatWidth ty)) := by
  cases ty <;> unfold runtime.interp.simd.splat_lanes splatOpcode splatInput splatWidth
  all_goals simp only [lift, bind_ok]
  all_goals try simp only [
    show (15#u32 - 15#u32) = Result.ok 0#u32 by with_unfolding_all rfl,
    show (16#u32 - 15#u32) = Result.ok 1#u32 by with_unfolding_all rfl,
    show (17#u32 - 15#u32) = Result.ok 2#u32 by with_unfolding_all rfl, bind_ok,
    show (8#u32 <<< 0#u32) = Result.ok 8#u32 by with_unfolding_all rfl,
    show (8#u32 <<< 1#u32) = Result.ok 16#u32 by with_unfolding_all rfl,
    show (8#u32 <<< 2#u32) = Result.ok 32#u32 by with_unfolding_all rfl]
  all_goals try simp only [bind_ok]
  case I8 =>
    with_unfolding_all change (Aeneas.Std.bind (Result.ok (UScalar.cast .U64 (UScalar.cast .U32 a), 8#u32))
      (fun p => (runtime.interp.simd.splat p.1 p.2)) = _)
    rw [bind_ok]
  case I16 =>
    with_unfolding_all change (Aeneas.Std.bind (Result.ok (UScalar.cast .U64 (UScalar.cast .U32 a), 16#u32))
      (fun p => (runtime.interp.simd.splat p.1 p.2)) = _)
    rw [bind_ok]
  case I32 =>
    with_unfolding_all change (Aeneas.Std.bind (Result.ok (UScalar.cast .U64 (UScalar.cast .U32 a), 32#u32))
      (fun p => (runtime.interp.simd.splat p.1 p.2)) = _)
    rw [bind_ok]
  case I64 =>
    with_unfolding_all change (Aeneas.Std.bind (Result.ok (UScalar.cast .U64 a, 64#u32))
      (fun p => (runtime.interp.simd.splat p.1 p.2)) = _)
    rw [bind_ok]
  case F32 =>
    with_unfolding_all change (Aeneas.Std.bind (Result.ok (UScalar.cast .U64 (UScalar.cast .U32 a), 32#u32))
      (fun p => (runtime.interp.simd.splat p.1 p.2)) = _)
    rw [bind_ok]
  case F64 =>
    with_unfolding_all change (Aeneas.Std.bind (Result.ok (UScalar.cast .U64 a, 64#u32))
      (fun p => (runtime.interp.simd.splat p.1 p.2)) = _)
    rw [bind_ok]

theorem splat_input_source (ty : lanetype) (a : U128) :
    Spec.Simd.scalarInput ty (splatInput ty a).bv =
      Spec.Simd.scalarInput ty (UScalar.cast .U64 a).bv := by
  have low32 : ((UScalar.cast .U64 (UScalar.cast .U32 a)).bv).setWidth 32 =
      ((UScalar.cast .U64 a).bv).setWidth 32 := by
    change ((a.bv.setWidth 32).setWidth 64).setWidth 32 = (a.bv.setWidth 64).setWidth 32
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  cases ty with
  | I64 | F64 => rfl
  | I8 | I16 | I32 =>
    exact congrArg (fun (b : BitVec 32) => num_.mk_num__0 .I32 (.mk_uN b.toNat)) low32
  | F32 =>
    exact congrArg (fun (b : BitVec 32) => num_.mk_num__1 .F32 (SpecExt.Builtins.floatOfBits 32 b.toNat)) low32

@[step] theorem splat_lanes_sound (ty : lanetype) (a : U128) :
    runtime.interp.simd.splat_lanes (splatOpcode ty) a ⦃ result =>
      Step_pure [.CONST (unpack ty) (Spec.Simd.scalarInput ty (UScalar.cast .U64 a).bv),
        .VSPLAT (Spec.Simd.shapeOf ty)] [.VCONST .V128 (.mk_uN result.val)] ⦄ := by
  rw [splat_lanes_eq]
  apply WP.spec_mono (splat_sound ty (splatInput ty a) (splatWidth ty) (splat_width_val ty))
  intro result source
  rw [splat_input_source] at source
  exact source

theorem splat_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : lanetype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (splatOpcode ty) offset laneIndex bits a b c memory =
      Aeneas.Std.bind (runtime.interp.simd.splat_lanes (splatOpcode ty) a)
        (fun result => Result.ok (core.result.Result.Ok result, memory)) := by
  cases ty <;> unfold runtime.interp.simd.simd splatOpcode <;> with_unfolding_all rfl

@[step] theorem splat_dispatch_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : lanetype) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (splatOpcode ty) offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧
        Step_pure [.CONST (unpack ty) (Spec.Simd.scalarInput ty (UScalar.cast .U64 a).bv),
          .VSPLAT (Spec.Simd.shapeOf ty)] [.VCONST .V128 (.mk_uN value.val)] ⦄ := by
  rw [splat_dispatch_eq]
  step with splat_lanes_sound ty a as ⟨value, source⟩
  exact ⟨value, rfl, source⟩

end Itasca.Runtime.Interp.Simd

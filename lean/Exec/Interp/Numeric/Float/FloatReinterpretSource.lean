import Exec.Interp.Numeric.Float.Float
import Exec.Spec.FloatReinterpret

namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins SpecExt.Builtins.Float

theorem scalar_f32_reinterpret_i32_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 190#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .I32 (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val)), .CVTOP .F32 .I32 (.mk_cvtop___1 .I32 .F32 .REINTERPRET)]
        [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 value.val))] ⦄ := by
  have run : runtime.interp.float.scalar ops 190#u16 a b = .ok (.Ok (UScalar.cast .U64 (UScalar.cast .U32 a))) := by
    unfold runtime.interp.float.scalar
    with_unfolding_all change
      (lift (UScalar.cast .U32 a) >>= fun small => lift (UScalar.cast .U64 small) >>= fun out =>
        Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) = _
    simp only [lift, Bind.bind, bind_ok]
  rw [run]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  simp only [U32.cast_U64_val_eq]
  exact Spec.f32_reinterpret_i32_pure _ (by scalar_tac)

theorem scalar_i32_reinterpret_f32_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 188#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F32 (.mk_num__1 .F32 (floatOfBits 32 (UScalar.cast .U32 a).val)), .CVTOP .I32 .F32 (.mk_cvtop___2 .F32 .I32 .REINTERPRET)]
        [.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val))] ⦄ := by
  have run : runtime.interp.float.scalar ops 188#u16 a b = .ok (.Ok (UScalar.cast .U64 (UScalar.cast .U32 a))) := by
    unfold runtime.interp.float.scalar
    with_unfolding_all change
      (lift (UScalar.cast .U32 a) >>= fun small => lift (UScalar.cast .U64 small) >>= fun out =>
        Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) = _
    simp only [lift, Bind.bind, bind_ok]
  rw [run]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  simp only [U32.cast_U64_val_eq]
  exact Spec.i32_reinterpret_f32_pure _ (by scalar_tac)

theorem scalar_f64_reinterpret_i64_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 191#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .I64 (.mk_num__0 .I64 (.mk_uN a.val)), .CVTOP .F64 .I64 (.mk_cvtop___1 .I64 .F64 .REINTERPRET)]
        [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 value.val))] ⦄ := by
  have run : runtime.interp.float.scalar ops 191#u16 a b = .ok (.Ok (a)) := by
    unfold runtime.interp.float.scalar
    with_unfolding_all rfl
  rw [run]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  exact Spec.f64_reinterpret_i64_pure _ (by scalar_tac)

theorem scalar_i64_reinterpret_f64_source {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.float.scalar ops 189#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
      Step_pure [.CONST .F64 (.mk_num__1 .F64 (floatOfBits 64 a.val)), .CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 .REINTERPRET)]
        [.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val))] ⦄ := by
  have run : runtime.interp.float.scalar ops 189#u16 a b = .ok (.Ok (a)) := by
    unfold runtime.interp.float.scalar
    with_unfolding_all rfl
  rw [run]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  exact Spec.i64_reinterpret_f64_pure _ (by scalar_tac)

end Exec.Interp

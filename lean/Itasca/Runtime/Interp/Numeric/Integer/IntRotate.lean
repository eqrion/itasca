import Itasca.Runtime.Interp.Numeric.Integer.IntShift
import Itasca.Runtime.Spec.IntegerRotate

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem scalar_i32_rotl_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 119#u16 a b = .ok (.Ok (UScalar.cast .U64 (core.num.U32.rotate_left (UScalar.cast .U32 a) (UScalar.cast .U32 b)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change
    (Aeneas.Std.bind (lift (core.num.U32.rotate_left (UScalar.cast .U32 a) (UScalar.cast .U32 b)))
      (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value))
        (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) = _
  simp only [lift, bind_ok]

theorem scalar_i32_rotl_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 119#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_binop_ .I32 (.mk_binop__0 .I32 .ROTL)
        (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val)) (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 b).val))
        (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i32_rotl_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  rw [U32.cast_U64_val_eq]
  exact Spec.integer_rotleft_relation .I32 (UScalar.cast .U32 a).bv (UScalar.cast .U32 b).val

theorem scalar_i32_rotr_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 120#u16 a b = .ok (.Ok (UScalar.cast .U64 (core.num.U32.rotate_right (UScalar.cast .U32 a) (UScalar.cast .U32 b)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change
    (Aeneas.Std.bind (lift (core.num.U32.rotate_right (UScalar.cast .U32 a) (UScalar.cast .U32 b)))
      (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value))
        (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) = _
  simp only [lift, bind_ok]

theorem scalar_i32_rotr_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 120#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_binop_ .I32 (.mk_binop__0 .I32 .ROTR)
        (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val)) (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 b).val))
        (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i32_rotr_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  rw [U32.cast_U64_val_eq]
  exact Spec.integer_rotright_relation .I32 (UScalar.cast .U32 a).bv (UScalar.cast .U32 b).val

theorem scalar_i64_rotl_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 137#u16 a b = .ok (.Ok (core.num.U64.rotate_left a (UScalar.cast .U32 b))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change
    (Aeneas.Std.bind (lift (UScalar.cast .U32 b)) (fun shift =>
      Aeneas.Std.bind (lift (core.num.U64.rotate_left a shift))
        (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) = _
  simp only [lift, bind_ok]

theorem scalar_i64_rotl_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 137#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_binop_ .I64 (.mk_binop__0 .I64 .ROTL)
        (.mk_num__0 .I64 (.mk_uN a.val)) (.mk_num__0 .I64 (.mk_uN b.val))
        (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i64_rotl_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  have count : (UScalar.cast .U32 b).val % 64 = b.val % 64 := by
    simp only [UScalar.cast_val_eq, UScalarTy.numBits]
    omega
  have same : a.bv.rotateLeft (UScalar.cast .U32 b).val = a.bv.rotateLeft b.val := by
    rw [← BitVec.rotateLeft_mod_eq_rotateLeft (r := (UScalar.cast .U32 b).val),
      ← BitVec.rotateLeft_mod_eq_rotateLeft (r := b.val)]
    exact congrArg (BitVec.rotateLeft a.bv) count
  change fun_binop_ .I64 (.mk_binop__0 .I64 .ROTL) _ _
    (some [.mk_num__0 .I64 (.mk_uN (a.bv.rotateLeft (UScalar.cast .U32 b).val).toNat)])
  rw [same]
  exact Spec.integer_rotleft_relation .I64 a.bv b.val

theorem scalar_i64_rotr_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 138#u16 a b = .ok (.Ok (core.num.U64.rotate_right a (UScalar.cast .U32 b))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change
    (Aeneas.Std.bind (lift (UScalar.cast .U32 b)) (fun shift =>
      Aeneas.Std.bind (lift (core.num.U64.rotate_right a shift))
        (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) = _
  simp only [lift, bind_ok]

theorem scalar_i64_rotr_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 138#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_binop_ .I64 (.mk_binop__0 .I64 .ROTR)
        (.mk_num__0 .I64 (.mk_uN a.val)) (.mk_num__0 .I64 (.mk_uN b.val))
        (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i64_rotr_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  have count : (UScalar.cast .U32 b).val % 64 = b.val % 64 := by
    simp only [UScalar.cast_val_eq, UScalarTy.numBits]
    omega
  have same : a.bv.rotateRight (UScalar.cast .U32 b).val = a.bv.rotateRight b.val := by
    rw [← BitVec.rotateRight_mod_eq_rotateRight (r := (UScalar.cast .U32 b).val),
      ← BitVec.rotateRight_mod_eq_rotateRight (r := b.val)]
    exact congrArg (BitVec.rotateRight a.bv) count
  change fun_binop_ .I64 (.mk_binop__0 .I64 .ROTR) _ _
    (some [.mk_num__0 .I64 (.mk_uN (a.bv.rotateRight (UScalar.cast .U32 b).val).toNat)])
  rw [same]
  exact Spec.integer_rotright_relation .I64 a.bv b.val

end Itasca.Runtime.Interp

import Itasca.Runtime.Interp.Numeric.Integer.IntSigned
import Itasca.Runtime.Spec.IntegerShift

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem scalar_i32_shrs_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 117#u16 a b = .ok (.Ok
      (UScalar.cast .U64 (IScalar.hcast .U32 (core.num.I32.wrapping_shr
        (UScalar.hcast .I32 (UScalar.cast .U32 a)) (UScalar.cast .U32 b))))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change
    (Aeneas.Std.bind (lift (UScalar.hcast .I32 (UScalar.cast .U32 a))) (fun x =>
      Aeneas.Std.bind (lift (core.num.I32.wrapping_shr x (UScalar.cast .U32 b))) (fun shifted =>
        Aeneas.Std.bind (lift (IScalar.hcast .U32 shifted)) (fun unsigned =>
          Aeneas.Std.bind (lift (UScalar.cast .U64 unsigned)) (fun result =>
            Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))))) = _
  simp only [lift, bind_ok]

theorem scalar_i64_shrs_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 135#u16 a b = .ok (.Ok
      (IScalar.hcast .U64 (core.num.I64.wrapping_shr (UScalar.hcast .I64 a) (UScalar.cast .U32 b)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change
    (Aeneas.Std.bind (lift (UScalar.hcast .I64 a)) (fun x =>
      Aeneas.Std.bind (lift (UScalar.cast .U32 b)) (fun shift =>
        Aeneas.Std.bind (lift (core.num.I64.wrapping_shr x shift)) (fun shifted =>
          Aeneas.Std.bind (lift (IScalar.hcast .U64 shifted)) (fun result =>
            Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))))) = _
  simp only [lift, bind_ok]

theorem scalar_i32_shrs_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 117#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_binop_ .I32 (.mk_binop__0 .I32 (.SHR .S))
        (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val))
        (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 b).val))
        (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i32_shrs_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  have bits : (IScalar.hcast .U32 (core.num.I32.wrapping_shr
      (UScalar.hcast .I32 (UScalar.cast .U32 a)) (UScalar.cast .U32 b))).bv =
      (UScalar.cast .U32 a).bv.sshiftRight ((UScalar.cast .U32 b).val % 32) := by
    simp only [IScalar.hcast_bv_eq, core.num.I32.wrapping_shr, IScalar.wrapping_shr,
      UScalar.hcast_bv_eq, UScalarTy.U32_numBits_eq, IScalarTy.I32_numBits_eq,
      BitVec.setWidth_eq, BitVec.signExtend_eq]
  rw [U32.cast_U64_val_eq]
  change fun_binop_ .I32 (.mk_binop__0 .I32 (.SHR .S)) _ _
    (some [.mk_num__0 .I32 (.mk_uN (IScalar.hcast .U32 (core.num.I32.wrapping_shr
      (UScalar.hcast .I32 (UScalar.cast .U32 a)) (UScalar.cast .U32 b))).bv.toNat)])
  rw [bits]
  exact Spec.integer_shrs_relation .I32 (UScalar.cast .U32 a).bv (UScalar.cast .U32 b).val

theorem scalar_i64_shrs_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 135#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_binop_ .I64 (.mk_binop__0 .I64 (.SHR .S))
        (.mk_num__0 .I64 (.mk_uN a.val)) (.mk_num__0 .I64 (.mk_uN b.val))
        (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i64_shrs_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  have count : (UScalar.cast .U32 b).val % 64 = b.val % 64 := by
    simp only [UScalar.cast_val_eq, UScalarTy.numBits]
    omega
  have bits : (IScalar.hcast .U64 (core.num.I64.wrapping_shr
      (UScalar.hcast .I64 a) (UScalar.cast .U32 b))).bv = a.bv.sshiftRight (b.val % 64) := by
    simp only [IScalar.hcast_bv_eq, core.num.I64.wrapping_shr, IScalar.wrapping_shr,
      UScalar.hcast_bv_eq, UScalarTy.U64_numBits_eq, IScalarTy.I64_numBits_eq,
      BitVec.setWidth_eq, BitVec.signExtend_eq, count]
  change fun_binop_ .I64 (.mk_binop__0 .I64 (.SHR .S)) _ _
    (some [.mk_num__0 .I64 (.mk_uN (IScalar.hcast .U64 (core.num.I64.wrapping_shr
      (UScalar.hcast .I64 a) (UScalar.cast .U32 b))).bv.toNat)])
  rw [bits]
  exact Spec.integer_shrs_relation .I64 a.bv b.val

end Itasca.Runtime.Interp

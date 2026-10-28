import Itasca.Runtime.Interp.Numeric.Integer.IntCounts
import Itasca.Runtime.Spec.IntegerExtend

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem scalar_i32_extend8_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 192#u16 a b = .ok (.Ok (UScalar.cast .U64 (IScalar.hcast .U32 (IScalar.cast .I32 (UScalar.hcast .I8 (UScalar.cast .U32 a)))))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (Aeneas.Std.bind (lift (UScalar.hcast .I8 (UScalar.cast .U32 a))) (fun i => Aeneas.Std.bind (lift (IScalar.cast .I32 i)) (fun j => Aeneas.Std.bind (lift (IScalar.hcast .U32 j)) (fun k => Aeneas.Std.bind (lift (UScalar.cast .U64 k)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))))) = _
  simp only [lift, bind_ok]

theorem scalar_i32_extend8_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 192#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_unop_ .I32 (.mk_unop__0 .I32 (.EXTEND 8))
        (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val))
        (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i32_extend8_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  rw [U32.cast_U64_val_eq]
  have bits : (IScalar.hcast .U32 (IScalar.cast .I32 (UScalar.hcast .I8 (UScalar.cast .U32 a)))).bv = ((UScalar.cast .U32 a).bv.setWidth 8).signExtend 32 := by
    simp only [IScalar.hcast_bv_eq, IScalar.cast_bv_eq, UScalar.hcast_bv_eq,
      IScalarTy.numBits, UScalarTy.numBits, BitVec.signExtend_eq]
  have value := congrArg BitVec.toNat bits
  rw [UScalar.bv_toNat] at value
  rw [value]
  exact Spec.extend_unary_bitvec .I32 8 (UScalar.cast .U32 a).bv

theorem scalar_i32_extend16_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 193#u16 a b = .ok (.Ok (UScalar.cast .U64 (IScalar.hcast .U32 (IScalar.cast .I32 (UScalar.hcast .I16 (UScalar.cast .U32 a)))))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (Aeneas.Std.bind (lift (UScalar.hcast .I16 (UScalar.cast .U32 a))) (fun i => Aeneas.Std.bind (lift (IScalar.cast .I32 i)) (fun j => Aeneas.Std.bind (lift (IScalar.hcast .U32 j)) (fun k => Aeneas.Std.bind (lift (UScalar.cast .U64 k)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))))) = _
  simp only [lift, bind_ok]

theorem scalar_i32_extend16_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 193#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_unop_ .I32 (.mk_unop__0 .I32 (.EXTEND 16))
        (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val))
        (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i32_extend16_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  rw [U32.cast_U64_val_eq]
  have bits : (IScalar.hcast .U32 (IScalar.cast .I32 (UScalar.hcast .I16 (UScalar.cast .U32 a)))).bv = ((UScalar.cast .U32 a).bv.setWidth 16).signExtend 32 := by
    simp only [IScalar.hcast_bv_eq, IScalar.cast_bv_eq, UScalar.hcast_bv_eq,
      IScalarTy.numBits, UScalarTy.numBits, BitVec.signExtend_eq]
  have value := congrArg BitVec.toNat bits
  rw [UScalar.bv_toNat] at value
  rw [value]
  exact Spec.extend_unary_bitvec .I32 16 (UScalar.cast .U32 a).bv

theorem scalar_i64_extend8_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 194#u16 a b = .ok (.Ok (IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I8 a)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (Aeneas.Std.bind (lift (UScalar.hcast .I8 a)) (fun i => Aeneas.Std.bind (lift (IScalar.cast .I64 i)) (fun j => Aeneas.Std.bind (lift (IScalar.hcast .U64 j)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))))) = _
  simp only [lift, bind_ok]

theorem scalar_i64_extend8_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 194#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_unop_ .I64 (.mk_unop__0 .I64 (.EXTEND 8))
        (.mk_num__0 .I64 (.mk_uN a.val))
        (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i64_extend8_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  have bits : (IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I8 a))).bv = (a.bv.setWidth 8).signExtend 64 := by
    simp only [IScalar.hcast_bv_eq, IScalar.cast_bv_eq, UScalar.hcast_bv_eq,
      IScalarTy.numBits, UScalarTy.numBits, BitVec.signExtend_eq]
  have value := congrArg BitVec.toNat bits
  rw [UScalar.bv_toNat] at value
  rw [value]
  exact Spec.extend_unary_bitvec .I64 8 a.bv

theorem scalar_i64_extend16_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 195#u16 a b = .ok (.Ok (IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I16 a)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (Aeneas.Std.bind (lift (UScalar.hcast .I16 a)) (fun i => Aeneas.Std.bind (lift (IScalar.cast .I64 i)) (fun j => Aeneas.Std.bind (lift (IScalar.hcast .U64 j)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))))) = _
  simp only [lift, bind_ok]

theorem scalar_i64_extend16_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 195#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_unop_ .I64 (.mk_unop__0 .I64 (.EXTEND 16))
        (.mk_num__0 .I64 (.mk_uN a.val))
        (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i64_extend16_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  have bits : (IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I16 a))).bv = (a.bv.setWidth 16).signExtend 64 := by
    simp only [IScalar.hcast_bv_eq, IScalar.cast_bv_eq, UScalar.hcast_bv_eq,
      IScalarTy.numBits, UScalarTy.numBits, BitVec.signExtend_eq]
  have value := congrArg BitVec.toNat bits
  rw [UScalar.bv_toNat] at value
  rw [value]
  exact Spec.extend_unary_bitvec .I64 16 a.bv

theorem scalar_i64_extend32_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 196#u16 a b = .ok (.Ok (IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I32 a)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (Aeneas.Std.bind (lift (UScalar.hcast .I32 a)) (fun i => Aeneas.Std.bind (lift (IScalar.cast .I64 i)) (fun j => Aeneas.Std.bind (lift (IScalar.hcast .U64 j)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))))) = _
  simp only [lift, bind_ok]

theorem scalar_i64_extend32_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 196#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_unop_ .I64 (.mk_unop__0 .I64 (.EXTEND 32))
        (.mk_num__0 .I64 (.mk_uN a.val))
        (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i64_extend32_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  have bits : (IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I32 a))).bv = (a.bv.setWidth 32).signExtend 64 := by
    simp only [IScalar.hcast_bv_eq, IScalar.cast_bv_eq, UScalar.hcast_bv_eq,
      IScalarTy.numBits, UScalarTy.numBits, BitVec.signExtend_eq]
  have value := congrArg BitVec.toNat bits
  rw [UScalar.bv_toNat] at value
  rw [value]
  exact Spec.extend_unary_bitvec .I64 32 a.bv

theorem scalar_wrap_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 167#u16 a b = .ok (.Ok (UScalar.cast .U64 (UScalar.cast .U32 a))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 a)))
    (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))) = _
  simp only [lift, bind_ok]

theorem scalar_wrap_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 167#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_cvtop__ .I64 .I32 (.mk_cvtop___0 .I64 .I32 .WRAP)
        (.mk_num__0 .I64 (.mk_uN a.val))
        (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_wrap_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  rw [U32.cast_U64_val_eq]
  exact Spec.integer_wrap_relation a.bv

theorem scalar_extendu_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 173#u16 a b = .ok (.Ok (UScalar.cast .U64 (UScalar.cast .U32 a))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 a)))
    (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))) = _
  simp only [lift, bind_ok]

theorem scalar_extendu_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 173#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_cvtop__ .I32 .I64 (.mk_cvtop___0 .I32 .I64 (.EXTEND .U))
        (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val))
        (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_extendu_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  rw [U32.cast_U64_val_eq]
  exact Spec.integer_extendu_relation (UScalar.cast .U32 a).bv

theorem scalar_extends_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 172#u16 a b = .ok (.Ok
      (IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I32 (UScalar.cast .U32 a))))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (Aeneas.Std.bind (lift (UScalar.hcast .I32 (UScalar.cast .U32 a)))
    (fun i => Aeneas.Std.bind (lift (IScalar.cast .I64 i))
      (fun j => Aeneas.Std.bind (lift (IScalar.hcast .U64 j))
        (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))))) = _
  simp only [lift, bind_ok]

theorem scalar_extends_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 172#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_cvtop__ .I32 .I64 (.mk_cvtop___0 .I32 .I64 (.EXTEND .S))
        (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val))
        (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_extends_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  have bits : (IScalar.hcast .U64 (IScalar.cast .I64 (UScalar.hcast .I32 (UScalar.cast .U32 a)))).bv =
      (UScalar.cast .U32 a).bv.signExtend 64 := by
    simp only [IScalar.hcast_bv_eq, IScalar.cast_bv_eq, UScalar.hcast_bv_eq,
      IScalarTy.numBits, UScalarTy.numBits, BitVec.signExtend_eq, BitVec.setWidth_eq]
  have value := congrArg BitVec.toNat bits
  rw [UScalar.bv_toNat] at value
  rw [value]
  exact Spec.integer_extends_relation (UScalar.cast .U32 a).bv

end Itasca.Runtime.Interp

import Itasca.Runtime.Interp.Numeric.Integer.SignedOperationsAndCounts
import Itasca.Runtime.Spec.TypingAndNumericOperations
import Itasca.Runtime.SourceMachine.Numeric.TransitionSafety
import Itasca.Runtime.Spec.PrimitiveOperations
import Itasca.Runtime.Interp.Relations.SlotsAndDefaults
import Itasca.Runtime.Compiler.Local.Lowering.Integer.Lowering
import Itasca.Runtime.SourceMachine.Numeric.Transition

open WebAssembly

/-!
Proofs for Runtime / Interp / Numeric / Integer.

This module collects ConversionsAndBinaryContracts, InstructionEffects.
Each section documents its contracts and consumers.
-/

/-! ## ConversionsAndBinaryContracts -/

section

/-!
# Conversions And Binary Contracts

Integer conversions and binary instructions satisfy their source and machine contracts.
-/

/-! ## IntExtend -/

section

namespace Itasca.Interp
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

end Itasca.Interp

end

/-! ## IntCompareSigned -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

theorem shifted_signed32 (bits : BitVec 64) :
    (bits <<< 32).sshiftRight 32 = (bits.setWidth 32).signExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.msb_eq_getLsbD_last]
  by_cases small : i < 32 <;> by_cases valid : i < 64 <;> simp_all +arith

@[step] theorem compare_int_lts32 (a b : U64) :
    runtime.interp.int.compare_int 2#u16 a b 32#u32 ⦃ result =>
      result = decide ((a.bv.setWidth 32).toInt < (b.bv.setWidth 32).toInt) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have exactI : i = 32#u32 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    UScalarTy.numBits, show (32#u32).val < 64 by decide, if_true, bind_ok, lift,
    HShiftRight.hShiftRight, IScalar.shiftRight_UScalar, IScalar.shiftRight, IScalarTy.numBits]
  with_unfolding_all change (Result.ok
    (decide ((⟨(a.bv <<< 32).sshiftRight 32⟩ : I64) < (⟨(b.bv <<< 32).sshiftRight 32⟩ : I64)))) ⦃ _ ⦄
  simp only [WP.spec_ok, IScalar.lt_equiv, IScalar.val, shifted_signed32]
  rw [BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64), BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64)]

@[step] theorem compare_int_gts32 (a b : U64) :
    runtime.interp.int.compare_int 4#u16 a b 32#u32 ⦃ result =>
      result = decide ((a.bv.setWidth 32).toInt > (b.bv.setWidth 32).toInt) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have exactI : i = 32#u32 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    UScalarTy.numBits, show (32#u32).val < 64 by decide, if_true, bind_ok, lift,
    HShiftRight.hShiftRight, IScalar.shiftRight_UScalar, IScalar.shiftRight, IScalarTy.numBits]
  with_unfolding_all change (Result.ok
    (decide ((⟨(a.bv <<< 32).sshiftRight 32⟩ : I64) > (⟨(b.bv <<< 32).sshiftRight 32⟩ : I64)))) ⦃ _ ⦄
  simp only [WP.spec_ok, IScalar.lt_equiv, IScalar.val, shifted_signed32]
  rw [BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64), BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64)]

@[step] theorem compare_int_les32 (a b : U64) :
    runtime.interp.int.compare_int 6#u16 a b 32#u32 ⦃ result =>
      result = decide ((a.bv.setWidth 32).toInt ≤ (b.bv.setWidth 32).toInt) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have exactI : i = 32#u32 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    UScalarTy.numBits, show (32#u32).val < 64 by decide, if_true, bind_ok, lift,
    HShiftRight.hShiftRight, IScalar.shiftRight_UScalar, IScalar.shiftRight, IScalarTy.numBits]
  with_unfolding_all change (Result.ok
    (decide ((⟨(a.bv <<< 32).sshiftRight 32⟩ : I64) ≤ (⟨(b.bv <<< 32).sshiftRight 32⟩ : I64)))) ⦃ _ ⦄
  simp only [WP.spec_ok, IScalar.le_equiv, IScalar.val, shifted_signed32]
  rw [BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64), BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64)]

@[step] theorem compare_int_ges32 (a b : U64) :
    runtime.interp.int.compare_int 8#u16 a b 32#u32 ⦃ result =>
      result = decide ((a.bv.setWidth 32).toInt ≥ (b.bv.setWidth 32).toInt) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have exactI : i = 32#u32 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    UScalarTy.numBits, show (32#u32).val < 64 by decide, if_true, bind_ok, lift,
    HShiftRight.hShiftRight, IScalar.shiftRight_UScalar, IScalar.shiftRight, IScalarTy.numBits]
  with_unfolding_all change (Result.ok
    (decide ((⟨(a.bv <<< 32).sshiftRight 32⟩ : I64) ≥ (⟨(b.bv <<< 32).sshiftRight 32⟩ : I64)))) ⦃ _ ⦄
  simp only [WP.spec_ok, IScalar.le_equiv, IScalar.val, shifted_signed32]
  rw [BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64), BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64)]

@[step] theorem compare_int_lts64 (a b : U64) :
    runtime.interp.int.compare_int 2#u16 a b 64#u32 ⦃ result =>
      result = decide (a.bv.toInt < b.bv.toInt) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have exactI : i = 0#u32 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    UScalarTy.numBits, show (0#u32).val < 64 by decide, if_true, bind_ok, lift,
    HShiftRight.hShiftRight, IScalar.shiftRight_UScalar, IScalar.shiftRight, IScalarTy.numBits]
  with_unfolding_all change (Result.ok
    (decide ((⟨(a.bv <<< 0).sshiftRight 0⟩ : I64) < (⟨(b.bv <<< 0).sshiftRight 0⟩ : I64)))) ⦃ _ ⦄
  simp [WP.spec_ok, IScalar.lt_equiv, IScalar.val]

@[step] theorem compare_int_gts64 (a b : U64) :
    runtime.interp.int.compare_int 4#u16 a b 64#u32 ⦃ result =>
      result = decide (a.bv.toInt > b.bv.toInt) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have exactI : i = 0#u32 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    UScalarTy.numBits, show (0#u32).val < 64 by decide, if_true, bind_ok, lift,
    HShiftRight.hShiftRight, IScalar.shiftRight_UScalar, IScalar.shiftRight, IScalarTy.numBits]
  with_unfolding_all change (Result.ok
    (decide ((⟨(a.bv <<< 0).sshiftRight 0⟩ : I64) > (⟨(b.bv <<< 0).sshiftRight 0⟩ : I64)))) ⦃ _ ⦄
  simp [WP.spec_ok, IScalar.lt_equiv, IScalar.val]

@[step] theorem compare_int_les64 (a b : U64) :
    runtime.interp.int.compare_int 6#u16 a b 64#u32 ⦃ result =>
      result = decide (a.bv.toInt ≤ b.bv.toInt) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have exactI : i = 0#u32 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    UScalarTy.numBits, show (0#u32).val < 64 by decide, if_true, bind_ok, lift,
    HShiftRight.hShiftRight, IScalar.shiftRight_UScalar, IScalar.shiftRight, IScalarTy.numBits]
  with_unfolding_all change (Result.ok
    (decide ((⟨(a.bv <<< 0).sshiftRight 0⟩ : I64) ≤ (⟨(b.bv <<< 0).sshiftRight 0⟩ : I64)))) ⦃ _ ⦄
  simp [WP.spec_ok, IScalar.le_equiv, IScalar.val]

@[step] theorem compare_int_ges64 (a b : U64) :
    runtime.interp.int.compare_int 8#u16 a b 64#u32 ⦃ result =>
      result = decide (a.bv.toInt ≥ b.bv.toInt) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have exactI : i = 0#u32 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    UScalarTy.numBits, show (0#u32).val < 64 by decide, if_true, bind_ok, lift,
    HShiftRight.hShiftRight, IScalar.shiftRight_UScalar, IScalar.shiftRight, IScalarTy.numBits]
  with_unfolding_all change (Result.ok
    (decide ((⟨(a.bv <<< 0).sshiftRight 0⟩ : I64) ≥ (⟨(b.bv <<< 0).sshiftRight 0⟩ : I64)))) ⦃ _ ⦄
  simp [WP.spec_ok, IScalar.le_equiv, IScalar.val]

@[step] theorem scalar_i32_lts {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 72#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      value.val = if (UScalar.cast .U32 a).bv.toInt < (UScalar.cast .U32 b).bv.toInt then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (Aeneas.Std.bind (72#u16 - 70#u16) (fun i => Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 a))) (fun x => Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 b))) (fun y => Aeneas.Std.bind (runtime.interp.int.compare_int i x y 32#u32) (fun answer => Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))))))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have exactI : i = 2#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : (UScalar.cast .U32 a).bv.toInt < (UScalar.cast .U32 b).bv.toInt <;> simp_all [Bool.toNat]

@[step] theorem scalar_i32_gts {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 74#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      value.val = if (UScalar.cast .U32 a).bv.toInt > (UScalar.cast .U32 b).bv.toInt then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (Aeneas.Std.bind (74#u16 - 70#u16) (fun i => Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 a))) (fun x => Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 b))) (fun y => Aeneas.Std.bind (runtime.interp.int.compare_int i x y 32#u32) (fun answer => Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))))))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have exactI : i = 4#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : (UScalar.cast .U32 a).bv.toInt > (UScalar.cast .U32 b).bv.toInt <;> simp_all [Bool.toNat]

@[step] theorem scalar_i32_les {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 76#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      value.val = if (UScalar.cast .U32 a).bv.toInt ≤ (UScalar.cast .U32 b).bv.toInt then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (Aeneas.Std.bind (76#u16 - 70#u16) (fun i => Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 a))) (fun x => Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 b))) (fun y => Aeneas.Std.bind (runtime.interp.int.compare_int i x y 32#u32) (fun answer => Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))))))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have exactI : i = 6#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : (UScalar.cast .U32 a).bv.toInt ≤ (UScalar.cast .U32 b).bv.toInt <;> simp_all [Bool.toNat]

@[step] theorem scalar_i32_ges {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 78#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      value.val = if (UScalar.cast .U32 a).bv.toInt ≥ (UScalar.cast .U32 b).bv.toInt then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (Aeneas.Std.bind (78#u16 - 70#u16) (fun i => Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 a))) (fun x => Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 b))) (fun y => Aeneas.Std.bind (runtime.interp.int.compare_int i x y 32#u32) (fun answer => Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))))))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have exactI : i = 8#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : (UScalar.cast .U32 a).bv.toInt ≥ (UScalar.cast .U32 b).bv.toInt <;> simp_all [Bool.toNat]

@[step] theorem scalar_i64_lts {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 83#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      value.val = if a.bv.toInt < b.bv.toInt then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (Aeneas.Std.bind (83#u16 - 81#u16) (fun i => Aeneas.Std.bind (runtime.interp.int.compare_int i a b 64#u32) (fun answer => Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have exactI : i = 2#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : a.bv.toInt < b.bv.toInt <;> simp_all [Bool.toNat]

@[step] theorem scalar_i64_gts {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 85#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      value.val = if a.bv.toInt > b.bv.toInt then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (Aeneas.Std.bind (85#u16 - 81#u16) (fun i => Aeneas.Std.bind (runtime.interp.int.compare_int i a b 64#u32) (fun answer => Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have exactI : i = 4#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : a.bv.toInt > b.bv.toInt <;> simp_all [Bool.toNat]

@[step] theorem scalar_i64_les {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 87#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      value.val = if a.bv.toInt ≤ b.bv.toInt then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (Aeneas.Std.bind (87#u16 - 81#u16) (fun i => Aeneas.Std.bind (runtime.interp.int.compare_int i a b 64#u32) (fun answer => Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have exactI : i = 6#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : a.bv.toInt ≤ b.bv.toInt <;> simp_all [Bool.toNat]

@[step] theorem scalar_i64_ges {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 89#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      value.val = if a.bv.toInt ≥ b.bv.toInt then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (Aeneas.Std.bind (89#u16 - 81#u16) (fun i => Aeneas.Std.bind (runtime.interp.int.compare_int i a b 64#u32) (fun answer => Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have exactI : i = 8#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : a.bv.toInt ≥ b.bv.toInt <;> simp_all [Bool.toNat]

theorem scalar_i32_lts_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 72#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_relop_ .I32 (.mk_relop__0 .I32 (.LT .S))
        (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val)) (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 b).val))
        (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  apply WP.spec_mono (scalar_i32_lts ops a b)
  rintro result ⟨value, exactResult, exactValue⟩
  refine ⟨value, exactResult, ?_⟩
  rw [exactValue]
  exact Spec.integer_lts_relation .I32 (UScalar.cast .U32 a).bv (UScalar.cast .U32 b).bv

theorem scalar_i32_gts_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 74#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_relop_ .I32 (.mk_relop__0 .I32 (.GT .S))
        (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val)) (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 b).val))
        (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  apply WP.spec_mono (scalar_i32_gts ops a b)
  rintro result ⟨value, exactResult, exactValue⟩
  refine ⟨value, exactResult, ?_⟩
  rw [exactValue]
  exact Spec.integer_gts_relation .I32 (UScalar.cast .U32 a).bv (UScalar.cast .U32 b).bv

theorem scalar_i32_les_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 76#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_relop_ .I32 (.mk_relop__0 .I32 (.LE .S))
        (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val)) (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 b).val))
        (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  apply WP.spec_mono (scalar_i32_les ops a b)
  rintro result ⟨value, exactResult, exactValue⟩
  refine ⟨value, exactResult, ?_⟩
  rw [exactValue]
  exact Spec.integer_les_relation .I32 (UScalar.cast .U32 a).bv (UScalar.cast .U32 b).bv

theorem scalar_i32_ges_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 78#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_relop_ .I32 (.mk_relop__0 .I32 (.GE .S))
        (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val)) (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 b).val))
        (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  apply WP.spec_mono (scalar_i32_ges ops a b)
  rintro result ⟨value, exactResult, exactValue⟩
  refine ⟨value, exactResult, ?_⟩
  rw [exactValue]
  exact Spec.integer_ges_relation .I32 (UScalar.cast .U32 a).bv (UScalar.cast .U32 b).bv

theorem scalar_i64_lts_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 83#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_relop_ .I64 (.mk_relop__0 .I64 (.LT .S))
        (.mk_num__0 .I64 (.mk_uN a.val)) (.mk_num__0 .I64 (.mk_uN b.val))
        (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  apply WP.spec_mono (scalar_i64_lts ops a b)
  rintro result ⟨value, exactResult, exactValue⟩
  refine ⟨value, exactResult, ?_⟩
  rw [exactValue]
  exact Spec.integer_lts_relation .I64 a.bv b.bv

theorem scalar_i64_gts_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 85#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_relop_ .I64 (.mk_relop__0 .I64 (.GT .S))
        (.mk_num__0 .I64 (.mk_uN a.val)) (.mk_num__0 .I64 (.mk_uN b.val))
        (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  apply WP.spec_mono (scalar_i64_gts ops a b)
  rintro result ⟨value, exactResult, exactValue⟩
  refine ⟨value, exactResult, ?_⟩
  rw [exactValue]
  exact Spec.integer_gts_relation .I64 a.bv b.bv

theorem scalar_i64_les_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 87#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_relop_ .I64 (.mk_relop__0 .I64 (.LE .S))
        (.mk_num__0 .I64 (.mk_uN a.val)) (.mk_num__0 .I64 (.mk_uN b.val))
        (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  apply WP.spec_mono (scalar_i64_les ops a b)
  rintro result ⟨value, exactResult, exactValue⟩
  refine ⟨value, exactResult, ?_⟩
  rw [exactValue]
  exact Spec.integer_les_relation .I64 a.bv b.bv

theorem scalar_i64_ges_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 89#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_relop_ .I64 (.mk_relop__0 .I64 (.GE .S))
        (.mk_num__0 .I64 (.mk_uN a.val)) (.mk_num__0 .I64 (.mk_uN b.val))
        (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  apply WP.spec_mono (scalar_i64_ges ops a b)
  rintro result ⟨value, exactResult, exactValue⟩
  refine ⟨value, exactResult, ?_⟩
  rw [exactValue]
  exact Spec.integer_ges_relation .I64 a.bv b.bv

end Itasca.Interp

end

/-! ## IntegerBinary -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

def integerWord (ty : Inn) (raw : U64) : BitVec (sizenn (numtype_Inn ty)) :=
  match ty with
  | .I32 => (UScalar.cast .U32 raw).bv
  | .I64 => raw.bv

@[simp] theorem integer_word32_to_nat (raw : U64) :
    (integerWord .I32 raw).toNat = raw.val % 4294967296 := by
  change (UScalar.cast .U32 raw).bv.toNat = _
  rw [UScalar.bv_toNat, UScalar.cast_val_eq]
  rfl

@[simp] theorem integer_word64_to_nat (raw : U64) :
    (integerWord .I64 raw).toNat = raw.val := by
  change raw.bv.toNat = _
  exact UScalar.bv_toNat raw

def binaryOpcode (ty : Inn) (op : binop_Inn) : U16 :=
  match ty, op with
  | .I32, .ADD => 106#u16
  | .I32, .SUB => 107#u16
  | .I32, .MUL => 108#u16
  | .I32, .DIV .S => 109#u16
  | .I32, .DIV .U => 110#u16
  | .I32, .REM .S => 111#u16
  | .I32, .REM .U => 112#u16
  | .I32, .AND => 113#u16
  | .I32, .OR => 114#u16
  | .I32, .XOR => 115#u16
  | .I32, .SHL => 116#u16
  | .I32, .SHR .S => 117#u16
  | .I32, .SHR .U => 118#u16
  | .I32, .ROTL => 119#u16
  | .I32, .ROTR => 120#u16
  | .I64, .ADD => 124#u16
  | .I64, .SUB => 125#u16
  | .I64, .MUL => 126#u16
  | .I64, .DIV .S => 127#u16
  | .I64, .DIV .U => 128#u16
  | .I64, .REM .S => 129#u16
  | .I64, .REM .U => 130#u16
  | .I64, .AND => 131#u16
  | .I64, .OR => 132#u16
  | .I64, .XOR => 133#u16
  | .I64, .SHL => 134#u16
  | .I64, .SHR .S => 135#u16
  | .I64, .SHR .U => 136#u16
  | .I64, .ROTL => 137#u16
  | .I64, .ROTR => 138#u16

/-- Numeric handlers either return their exact source result or a numeric trap. -/
def BinaryStatus (ty : Inn) (op : binop_Inn) (a b : U64)
    (status : core.result.Result U64 runtime.ExecError) : Prop :=
  match status with
  | .Ok value => fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty op)
      (.mk_num__0 ty (.mk_uN (integerWord ty a).toNat))
      (.mk_num__0 ty (.mk_uN (integerWord ty b).toNat))
      (some [.mk_num__0 ty (.mk_uN value.val)])
  | .Err (.Trap trap) => (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
      fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty op)
        (.mk_num__0 ty (.mk_uN (integerWord ty a).toNat))
        (.mk_num__0 ty (.mk_uN (integerWord ty b).toNat)) (some [])
  | _ => False

theorem scalar_binary_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Inn) (op : binop_Inn) (a b : U64) :
    runtime.interp.int.scalar floats (binaryOpcode ty op) a b ⦃ BinaryStatus ty op a b ⦄ := by
  cases ty with
  | I32 =>
    cases op with
    | ADD =>
      apply WP.spec_mono (scalar_i32_add_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | SUB =>
      apply WP.spec_mono (scalar_i32_sub_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | MUL =>
      apply WP.spec_mono (scalar_i32_mul_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | DIV sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i32_divs_sound floats a b)
        intro status evidence
        rcases evidence with ⟨value, rfl, relation⟩ | trapped
        · exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
        · rcases trapped with ⟨trap, rfl, allowed, relation⟩
          exact ⟨allowed, by exact (by simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)⟩
      | U =>
        apply WP.spec_mono (scalar_i32_divu_sound floats a b)
        intro status evidence
        rcases evidence with ⟨value, rfl, relation⟩ | trapped
        · exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
        · rcases trapped with ⟨rfl, relation⟩
          exact ⟨Or.inl rfl, by exact (by simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)⟩
    | REM sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i32_rems_sound floats a b)
        intro status evidence
        rcases evidence with ⟨value, rfl, relation⟩ | trapped
        · exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
        · rcases trapped with ⟨rfl, relation⟩
          exact ⟨Or.inl rfl, by exact (by simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)⟩
      | U =>
        apply WP.spec_mono (scalar_i32_remu_sound floats a b)
        intro status evidence
        rcases evidence with ⟨value, rfl, relation⟩ | trapped
        · exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
        · rcases trapped with ⟨rfl, relation⟩
          exact ⟨Or.inl rfl, by exact (by simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)⟩
    | AND =>
      apply WP.spec_mono (scalar_i32_and_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | OR =>
      apply WP.spec_mono (scalar_i32_or_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | XOR =>
      apply WP.spec_mono (scalar_i32_xor_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | SHL =>
      apply WP.spec_mono (scalar_i32_shl_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | SHR sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i32_shrs_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
      | U =>
        apply WP.spec_mono (scalar_i32_shru_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | ROTL =>
      apply WP.spec_mono (scalar_i32_rotl_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | ROTR =>
      apply WP.spec_mono (scalar_i32_rotr_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
  | I64 =>
    cases op with
    | ADD =>
      apply WP.spec_mono (scalar_i64_add_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | SUB =>
      apply WP.spec_mono (scalar_i64_sub_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | MUL =>
      apply WP.spec_mono (scalar_i64_mul_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | DIV sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i64_divs_sound floats a b)
        intro status evidence
        rcases evidence with ⟨value, rfl, relation⟩ | trapped
        · exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
        · rcases trapped with ⟨trap, rfl, allowed, relation⟩
          exact ⟨allowed, by exact (by simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)⟩
      | U =>
        apply WP.spec_mono (scalar_i64_divu_sound floats a b)
        intro status evidence
        rcases evidence with ⟨value, rfl, relation⟩ | trapped
        · exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
        · rcases trapped with ⟨rfl, relation⟩
          exact ⟨Or.inl rfl, by exact (by simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)⟩
    | REM sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i64_rems_sound floats a b)
        intro status evidence
        rcases evidence with ⟨value, rfl, relation⟩ | trapped
        · exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
        · rcases trapped with ⟨rfl, relation⟩
          exact ⟨Or.inl rfl, by exact (by simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)⟩
      | U =>
        apply WP.spec_mono (scalar_i64_remu_sound floats a b)
        intro status evidence
        rcases evidence with ⟨value, rfl, relation⟩ | trapped
        · exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
        · rcases trapped with ⟨rfl, relation⟩
          exact ⟨Or.inl rfl, by exact (by simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)⟩
    | AND =>
      apply WP.spec_mono (scalar_i64_and_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | OR =>
      apply WP.spec_mono (scalar_i64_or_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | XOR =>
      apply WP.spec_mono (scalar_i64_xor_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | SHL =>
      apply WP.spec_mono (scalar_i64_shl_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | SHR sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i64_shrs_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
      | U =>
        apply WP.spec_mono (scalar_i64_shru_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | ROTL =>
      apply WP.spec_mono (scalar_i64_rotl_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)
    | ROTR =>
      apply WP.spec_mono (scalar_i64_rotr_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      exact (by try (simp only [BinaryStatus]); simp only [integer_word32_to_nat, integer_word64_to_nat]; simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation)

/-- Concrete results equal the deterministic word semantics; traps preserve the
same empty source result, and cannot become unrelated runtime errors. -/
def BinaryExact (ty : Inn) (op : binop_Inn) (a b : U64)
    (status : core.result.Result U64 runtime.ExecError) : Prop :=
  match status with
  | .Ok value => ∃ word, SourceMachine.Numeric.binary ty op (integerWord ty a) (integerWord ty b) = some word ∧ value.val = word.toNat
  | .Err (.Trap trap) => (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
      SourceMachine.Numeric.binary ty op (integerWord ty a) (integerWord ty b) = none
  | _ => False

theorem BinaryStatus.exact {ty : Inn} {op : binop_Inn} {a b : U64}
    {status : core.result.Result U64 runtime.ExecError} (sound : BinaryStatus ty op a b status) :
    BinaryExact ty op a b status := by
  have specified := SourceMachine.Numeric.binary_relation ty op (integerWord ty a) (integerWord ty b)
  cases status with
  | Ok value =>
    have same := Spec.integer_binop_deterministic sound specified
    cases result : SourceMachine.Numeric.binary ty op (integerWord ty a) (integerWord ty b) with
    | none => simp [result, SourceMachine.Numeric.binaryNumbers] at same
    | some word =>
      refine ⟨word, result, ?_⟩
      simpa only [result, SourceMachine.Numeric.binaryNumbers, List.singleton_inj, num_.mk_num__0.injEq, uN.mk_uN.injEq, true_and] using same
  | Err error =>
    cases error <;> try exact False.elim sound
    rename_i trap
    have same := Spec.integer_binop_deterministic sound.2 specified
    refine ⟨sound.1, ?_⟩
    cases result : SourceMachine.Numeric.binary ty op (integerWord ty a) (integerWord ty b) with
    | none => rfl
    | some word => simp [result, SourceMachine.Numeric.binaryNumbers] at same

theorem scalar_binary_exact {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Inn) (op : binop_Inn) (a b : U64) :
    runtime.interp.int.scalar floats (binaryOpcode ty op) a b ⦃ BinaryExact ty op a b ⦄ := by
  apply WP.spec_mono (scalar_binary_sound floats ty op a b)
  exact fun _ sound => sound.exact

end Itasca.Interp

end

end

/-! ## InstructionEffects -/

section

open Itasca.Representation

/-!
# Instruction Effects

Integer dispatch, operand fetching and numeric instructions produce the specified interpreter effects.
-/

/-! ## IntegerDispatch -/

section

/-!
Scalar integer instruction dispatch. Comparison, conversion and unary opcode facts join the separately proved binary arithmetic facts in one exact instruction-effect argument.
-/

/-! ## Integer Compare -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

def compareOpcode (ty : Inn) (op : relop_Inn) : U16 :=
  match ty, op with
  | .I32, .EQ => 70#u16
  | .I32, .NE => 71#u16
  | .I32, .LT .S => 72#u16
  | .I32, .LT .U => 73#u16
  | .I32, .GT .S => 74#u16
  | .I32, .GT .U => 75#u16
  | .I32, .LE .S => 76#u16
  | .I32, .LE .U => 77#u16
  | .I32, .GE .S => 78#u16
  | .I32, .GE .U => 79#u16
  | .I64, .EQ => 81#u16
  | .I64, .NE => 82#u16
  | .I64, .LT .S => 83#u16
  | .I64, .LT .U => 84#u16
  | .I64, .GT .S => 85#u16
  | .I64, .GT .U => 86#u16
  | .I64, .LE .S => 87#u16
  | .I64, .LE .U => 88#u16
  | .I64, .GE .S => 89#u16
  | .I64, .GE .U => 90#u16

theorem scalar_compare_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Inn) (op : relop_Inn) (a b : U64) :
    runtime.interp.int.scalar floats (compareOpcode ty op) a b ⦃ status => ∃ value, status = .Ok value ∧
      fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty op)
        (.mk_num__0 ty (.mk_uN (integerWord ty a).toNat))
        (.mk_num__0 ty (.mk_uN (integerWord ty b).toNat))
        (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  cases ty with
  | I32 =>
    cases op with
    | EQ =>
      apply WP.spec_mono (scalar_i32_eq_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integer_word32_to_nat, integer_word64_to_nat]
      simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | NE =>
      apply WP.spec_mono (scalar_i32_ne_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integer_word32_to_nat, integer_word64_to_nat]
      simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | LT sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i32_lts_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integer_word32_to_nat, integer_word64_to_nat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
      | U =>
        apply WP.spec_mono (scalar_i32_ltu_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integer_word32_to_nat, integer_word64_to_nat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | GT sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i32_gts_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integer_word32_to_nat, integer_word64_to_nat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
      | U =>
        apply WP.spec_mono (scalar_i32_gtu_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integer_word32_to_nat, integer_word64_to_nat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | LE sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i32_les_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integer_word32_to_nat, integer_word64_to_nat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
      | U =>
        apply WP.spec_mono (scalar_i32_leu_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integer_word32_to_nat, integer_word64_to_nat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | GE sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i32_ges_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integer_word32_to_nat, integer_word64_to_nat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
      | U =>
        apply WP.spec_mono (scalar_i32_geu_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integer_word32_to_nat, integer_word64_to_nat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
  | I64 =>
    cases op with
    | EQ =>
      apply WP.spec_mono (scalar_i64_eq_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integer_word32_to_nat, integer_word64_to_nat]
      simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | NE =>
      apply WP.spec_mono (scalar_i64_ne_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integer_word32_to_nat, integer_word64_to_nat]
      simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | LT sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i64_lts_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integer_word32_to_nat, integer_word64_to_nat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
      | U =>
        apply WP.spec_mono (scalar_i64_ltu_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integer_word32_to_nat, integer_word64_to_nat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | GT sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i64_gts_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integer_word32_to_nat, integer_word64_to_nat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
      | U =>
        apply WP.spec_mono (scalar_i64_gtu_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integer_word32_to_nat, integer_word64_to_nat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | LE sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i64_les_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integer_word32_to_nat, integer_word64_to_nat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
      | U =>
        apply WP.spec_mono (scalar_i64_leu_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integer_word32_to_nat, integer_word64_to_nat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | GE sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i64_ges_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integer_word32_to_nat, integer_word64_to_nat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
      | U =>
        apply WP.spec_mono (scalar_i64_geu_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integer_word32_to_nat, integer_word64_to_nat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation

theorem scalar_compare_exact {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Inn) (op : relop_Inn) (a b : U64) :
    runtime.interp.int.scalar floats (compareOpcode ty op) a b ⦃ status => ∃ value, status = .Ok value ∧
      value.val = SourceMachine.Numeric.compare ty op (integerWord ty a) (integerWord ty b) ⦄ := by
  apply WP.spec_mono (scalar_compare_sound floats ty op a b)
  rintro status ⟨value, rfl, relation⟩
  refine ⟨value, rfl, ?_⟩
  have same := Spec.integer_relop_deterministic relation (SourceMachine.Numeric.compare_relation ty op (integerWord ty a) (integerWord ty b))
  simpa only [num_.mk_num__0.injEq, uN.mk_uN.injEq, true_and] using same
end Itasca.Interp

end

/-! ## Integer Conversion -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SourceMachine.Numeric

def conversionOpcode : Conversion → U16
  | .wrap => 167#u16
  | .extendUnsigned => 173#u16
  | .extendSigned => 172#u16

theorem scalar_conversion_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (op : Conversion) (a b : U64) :
    runtime.interp.int.scalar floats (conversionOpcode op) a b ⦃ status => ∃ value, status = .Ok value ∧
      fun_cvtop__ (numtype_Inn op.input) (numtype_Inn op.output) op.operator
        (.mk_num__0 op.input (.mk_uN (integerWord op.input a).toNat))
        (some [.mk_num__0 op.output (.mk_uN value.val)]) ⦄ := by
  cases op with
  | wrap =>
    apply WP.spec_mono (scalar_wrap_sound floats a b)
    rintro status ⟨value, rfl, relation⟩
    refine ⟨value, rfl, ?_⟩
    simp only [Conversion.input, integer_word64_to_nat]
    exact relation
  | extendUnsigned =>
    apply WP.spec_mono (scalar_extendu_sound floats a b)
    rintro status ⟨value, rfl, relation⟩
    refine ⟨value, rfl, ?_⟩
    simp only [Conversion.input, integer_word32_to_nat]
    simpa only [Conversion.output, Conversion.operator, UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn,
      show (2:Nat)^32=4294967296 from rfl] using relation
  | extendSigned =>
    apply WP.spec_mono (scalar_extends_sound floats a b)
    rintro status ⟨value, rfl, relation⟩
    refine ⟨value, rfl, ?_⟩
    simp only [Conversion.input, integer_word32_to_nat]
    simpa only [Conversion.output, Conversion.operator, UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn,
      show (2:Nat)^32=4294967296 from rfl] using relation

theorem scalar_conversion_exact {F : Type} (floats : runtime.platform.FloatOps F)
    (op : Conversion) (a b : U64) :
    runtime.interp.int.scalar floats (conversionOpcode op) a b ⦃ status => ∃ value, status = .Ok value ∧
      value.val = (op.apply (integerWord op.input a)).toNat ⦄ := by
  apply WP.spec_mono (scalar_conversion_sound floats op a b)
  rintro status ⟨value, rfl, relation⟩
  refine ⟨value, rfl, ?_⟩
  have same : [num_.mk_num__0 op.output (.mk_uN value.val)] =
      [num_.mk_num__0 op.output (.mk_uN (op.apply (integerWord op.input a)).toNat)] := by
    cases op <;> exact Spec.integer_cvtop_deterministic relation (Conversion.relation _ _)
  simpa only [List.singleton_inj, num_.mk_num__0.injEq, uN.mk_uN.injEq, true_and] using same

def eqzOpcode : Inn → U16
  | .I32 => 69#u16
  | .I64 => 80#u16

theorem scalar_eqz_exact {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Inn) (a b : U64) :
    runtime.interp.int.scalar floats (eqzOpcode ty) a b ⦃ status => ∃ value, status = .Ok value ∧
      value.val = if (integerWord ty a).toNat = 0 then 1 else 0 ⦄ := by
  cases ty
  · simpa only [eqzOpcode, integer_word32_to_nat] using scalar_i32_eqz floats a b
  · simpa only [eqzOpcode, integer_word64_to_nat] using scalar_i64_eqz floats a b
end Itasca.Interp

end

/-! ## Integer Unary -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SourceMachine.Numeric

def unaryOpcode {ty : Inn} (op : UnaryOperator ty) : U16 :=
  UScalar.ofNat op.opcode (by have := op.opcode_bound; change op.opcode ≤ 65535; omega)

theorem scalar_unary_sound {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Inn) (op : UnaryOperator ty) (a b : U64) :
    runtime.interp.int.scalar floats (unaryOpcode op) a b ⦃ status => ∃ value, status = .Ok value ∧
      fun_unop_ (numtype_Inn ty) (.mk_unop__0 ty op.operation)
        (.mk_num__0 ty (.mk_uN (integerWord ty a).toNat))
        (some [.mk_num__0 ty (.mk_uN value.val)]) ⦄ := by
  cases ty with
  | I32 =>
    cases op with
    | clz =>
      apply WP.spec_mono (scalar_i32_clz_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integer_word32_to_nat, integer_word64_to_nat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | ctz =>
      apply WP.spec_mono (scalar_i32_ctz_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integer_word32_to_nat, integer_word64_to_nat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | popcnt =>
      apply WP.spec_mono (scalar_i32_popcnt_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integer_word32_to_nat, integer_word64_to_nat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | extend8 =>
      apply WP.spec_mono (scalar_i32_extend8_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integer_word32_to_nat, integer_word64_to_nat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | extend16 =>
      apply WP.spec_mono (scalar_i32_extend16_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integer_word32_to_nat, integer_word64_to_nat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
  | I64 =>
    cases op with
    | clz =>
      apply WP.spec_mono (scalar_i64_clz_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integer_word32_to_nat, integer_word64_to_nat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | ctz =>
      apply WP.spec_mono (scalar_i64_ctz_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integer_word32_to_nat, integer_word64_to_nat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | popcnt =>
      apply WP.spec_mono (scalar_i64_popcnt_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integer_word32_to_nat, integer_word64_to_nat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | extend8 =>
      apply WP.spec_mono (scalar_i64_extend8_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integer_word32_to_nat, integer_word64_to_nat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | extend16 =>
      apply WP.spec_mono (scalar_i64_extend16_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integer_word32_to_nat, integer_word64_to_nat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | extend32 =>
      apply WP.spec_mono (scalar_i64_extend32_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integer_word32_to_nat, integer_word64_to_nat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation

theorem scalar_unary_exact {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Inn) (op : UnaryOperator ty) (a b : U64) :
    runtime.interp.int.scalar floats (unaryOpcode op) a b ⦃ status => ∃ value, status = .Ok value ∧
      value.val = (unary ty op.operation (integerWord ty a)).toNat ⦄ := by
  apply WP.spec_mono (scalar_unary_sound floats ty op a b)
  rintro status ⟨value, rfl, relation⟩
  refine ⟨value, rfl, ?_⟩
  have same := Spec.integer_unop_deterministic relation (unary_relation ty op.operation (integerWord ty a))
  simpa only [List.singleton_inj, num_.mk_num__0.injEq, uN.mk_uN.injEq, true_and] using same
end Itasca.Interp

end

/-! ## Integer Dispatch -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SourceMachine.Numeric

theorem integer_opcode_agrees (op : Instruction) : Compiler.integerOpcode op =
    (match op with
    | .binary ty binop => binaryOpcode ty binop
    | .unary _ unop => unaryOpcode unop
    | .compare ty relop => compareOpcode ty relop
    | .eqz ty => eqzOpcode ty
    | .conversion conv => conversionOpcode conv) := by
  cases op with
  | binary ty binop => cases ty <;> cases binop <;> (try casesm* sx) <;> rfl
  | unary ty unop => cases unop <;> (try cases ty) <;> rfl
  | compare ty relop => cases ty <;> cases relop <;> (try casesm* sx) <;> rfl
  | eqz ty => cases ty <;> rfl
  | conversion conv => cases conv <;> rfl

def IntegerExact (op : Instruction) (a b : U64)
    (status : core.result.Result U64 runtime.ExecError) : Prop :=
  match status with
  | .Ok value => ∃ word, op.apply (integerWord op.input a) (integerWord op.input b) = some word ∧ value.val = word.toNat
  | .Err (.Trap trap) => (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
      op.apply (integerWord op.input a) (integerWord op.input b) = none
  | _ => False

/-- All 66 scalar integer instructions agree with their source word semantics. -/
theorem scalar_integer_exact {F : Type} (floats : runtime.platform.FloatOps F)
    (op : Instruction) (a b : U64) :
    runtime.interp.int.scalar floats (Compiler.integerOpcode op) a b ⦃ IntegerExact op a b ⦄ := by
  rw [integer_opcode_agrees]
  cases op with
  | binary ty op => exact scalar_binary_exact floats ty op a b
  | unary ty op =>
    apply WP.spec_mono (scalar_unary_exact floats ty op a b)
    rintro status ⟨value, rfl, same⟩
    exact ⟨_, rfl, same⟩
  | compare ty op =>
    apply WP.spec_mono (scalar_compare_exact floats ty op a b)
    rintro status ⟨value, rfl, same⟩
    refine ⟨_, rfl, ?_⟩
    change value.val = (BitVec.ofNat 32 (SourceMachine.Numeric.compare ty op (integerWord ty a) (integerWord ty b))).toNat
    have bound : SourceMachine.Numeric.compare ty op (integerWord ty a) (integerWord ty b) < 2^32 := compare_bound ty op (integerWord ty a) (integerWord ty b)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    exact same
  | eqz ty =>
    apply WP.spec_mono (scalar_eqz_exact floats ty a b)
    rintro status ⟨value, rfl, same⟩
    refine ⟨_, rfl, ?_⟩
    change value.val = (BitVec.ofNat 32 (if (integerWord ty a).toNat = 0 then 1 else 0)).toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show (if (integerWord ty a).toNat = 0 then 1 else 0) < 2^32 by split <;> decide)]
    exact same
  | conversion op =>
    apply WP.spec_mono (scalar_conversion_exact floats op a b)
    rintro status ⟨value, rfl, same⟩
    exact ⟨_, rfl, same⟩

/-- Actual scalar dispatch exposes both its exact mathematical result and full
slot mutation; a numeric trap leaves every execution field unchanged. -/
theorem execute_integer_effect {F : Type} (floats : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (op : Instruction) (dst left right : U32)
    (hl : base.val + left.val < exec.slots.length)
    (hr : base.val + right.val < exec.slots.length)
    (hd : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_scalar floats exec base (Compiler.integerOpcode op) dst left right ⦃ out =>
      ∃ numeric, IntegerExact op exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]! numeric ∧
        ScalarEffect exec (base.val + dst.val) numeric out ⦄ := by
  obtain ⟨numeric, equation, exactResult⟩ := WP.spec_imp_exists
    (scalar_integer_exact floats op exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]!)
  apply WP.spec_mono (execute_scalar_effect floats exec base (Compiler.integerOpcode op) dst left right hl hr hd numeric equation)
  exact fun _ effect => ⟨numeric, exactResult, effect⟩
end Itasca.Interp

end

end

/-! ## NumericDispatch -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SourceMachine.Numeric
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

 theorem dispatch_integer_eq (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (index inst function base : Usize)
    (op : Instruction) (dst left right : U32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Compiler.integerInstruction op dst left right) = (do
        let (r, next) ← runtime.interp.execute_scalar floats exec base
          (Compiler.integerOpcode op) dst left right
        Result.ok (r, next, store, platform)) := by
  cases op with
  | binary ty binop => cases ty <;> cases binop <;> (try casesm* sx) <;>
    simp [Compiler.integerInstruction, Compiler.integerOpcode, runtime.interp.dispatch,
      runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | unary ty unop => cases unop <;> (try cases ty) <;>
    simp [Compiler.integerInstruction, Compiler.integerOpcode, runtime.interp.dispatch,
      runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | compare ty relop => cases ty <;> cases relop <;> (try casesm* sx) <;>
    simp [Compiler.integerInstruction, Compiler.integerOpcode, runtime.interp.dispatch,
      runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | eqz ty => cases ty <;>
    simp [Compiler.integerInstruction, Compiler.integerOpcode, runtime.interp.dispatch,
      runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | conversion conv => cases conv <;>
    simp [Compiler.integerInstruction, Compiler.integerOpcode, runtime.interp.dispatch,
      runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]

end Itasca.Interp

end

/-! ## NumericWords -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SourceMachine.Numeric

theorem integer_word_of_val (ty : Inn) (raw : U64)
    (word : BitVec (sizenn (numtype_Inn ty))) (same : raw.val = word.toNat) :
    integerWord ty raw = word := by
  apply BitVec.eq_of_toNat_eq
  cases ty with
  | I32 =>
    rw [integer_word32_to_nat, same, Nat.mod_eq_of_lt]
    exact word.isLt
  | I64 => simpa only [integer_word64_to_nat] using same

theorem WordsAt.unary_result {words : List U64} {base : Nat} {front : List Nat} {a : Nat}
    (h : WordsAt words base (front ++ [a])) (value : U64) :
    WordsAt (words.set (base + front.length) value) base (front ++ [value.val]) := by
  simpa using h.set front.length value

def NumericWordsEffect (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (exec : runtime.interp.Execution) (base : Nat) (front : List Nat)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) : Prop :=
  match op.apply a b with
  | some value => out.1 = .Ok () ∧
      WordsAt out.2.slots.val base (front ++ [value.toNat]) ∧
      { out.2 with slots := exec.slots } = exec
  | none => ∃ trap, (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧ out = (.Err (.Trap trap), exec)

theorem integer_binary_words {F : Type} (floats : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (op : Instruction)
    (left right : U32) (front : List Nat)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (words : WordsAt exec.slots.val base.val (front ++ [a.toNat, b.toNat]))
    (hl : left.val = front.length) (hr : right.val = front.length + 1) :
    runtime.interp.execute_scalar floats exec base (Compiler.integerOpcode op) left left right ⦃
      NumericWordsEffect op a b exec base.val front ⦄ := by
  have operand := words.append_right
  have ha : base.val + left.val < exec.slots.length := by simpa [hl] using (operand 0 (by simp)).1
  have hb : base.val + right.val < exec.slots.length := by simpa [hr, Nat.add_assoc] using (operand 1 (by simp)).1
  have va : integerWord op.input exec.slots.val[base.val + left.val]! = a := by
    apply integer_word_of_val
    simpa [hl] using (operand 0 (by simp)).2
  have vb : integerWord op.input exec.slots.val[base.val + right.val]! = b := by
    apply integer_word_of_val
    simpa [hr, Nat.add_assoc] using (operand 1 (by simp)).2
  apply WP.spec_mono (execute_integer_effect floats exec base op left left right ha hb ha)
  rintro out ⟨numeric, exactResult, effect⟩
  cases numeric with
  | Ok value =>
    obtain ⟨word, operation, equal⟩ := exactResult
    rw [va, vb] at operation
    simp only [NumericWordsEffect, operation]
    obtain ⟨success, slots, unchanged⟩ := effect
    refine ⟨success, ?_, unchanged⟩
    rw [slots, hl, ← equal]
    exact words.binary_result value
  | Err error =>
    cases error <;> try contradiction
    rename_i trap
    obtain ⟨allowed, operation⟩ := exactResult
    rw [va, vb] at operation
    simp only [NumericWordsEffect, operation]
    exact ⟨trap, allowed, effect⟩
theorem integer_unary_words {F : Type} (floats : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (op : Instruction)
    (left : U32) (front : List Nat)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (one : op.arity = 1)
    (words : WordsAt exec.slots.val base.val (front ++ [a.toNat]))
    (hl : left.val = front.length) :
    runtime.interp.execute_scalar floats exec base (Compiler.integerOpcode op) left left left ⦃
      NumericWordsEffect op a b exec base.val front ⦄ := by
  have operand := words.append_right
  have ha : base.val + left.val < exec.slots.length := by simpa [hl] using (operand 0 (by simp)).1
  have va : integerWord op.input exec.slots.val[base.val + left.val]! = a := by
    apply integer_word_of_val
    simpa [hl] using (operand 0 (by simp)).2
  apply WP.spec_mono (execute_integer_effect floats exec base op left left left ha ha ha)
  rintro out ⟨numeric, exactResult, effect⟩
  cases numeric with
  | Ok value =>
    obtain ⟨word, operation, equal⟩ := exactResult
    rw [va, op.apply_unary a b one] at operation
    simp only [NumericWordsEffect, operation]
    obtain ⟨success, slots, unchanged⟩ := effect
    refine ⟨success, ?_, unchanged⟩
    rw [slots, hl, ← equal]
    exact words.unary_result value
  | Err error =>
    cases error <;> try contradiction
    rename_i trap
    obtain ⟨allowed, operation⟩ := exactResult
    rw [va, op.apply_unary a b one] at operation
    simp only [NumericWordsEffect, operation]
    exact ⟨trap, allowed, effect⟩
end Itasca.Interp

end

/-! ## NumericFetch -/

section

/-!
Integer instruction execution on decoded values. The value/word relation supplies the fetched instruction step and its concrete result slots.
-/

/-! ## Numeric Values -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SourceMachine.Numeric

def NumericValuesEffect (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (exec : runtime.interp.Execution) (base : Nat) (front : List val)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) : Prop :=
  match op.apply a b with
  | some value => out.1 = .Ok () ∧
      ValuesAt out.2.slots.val base (front ++ [SourceMachine.integerVal op.output value.toNat]) ∧
      { out.2 with slots := exec.slots } = exec
  | none => ∃ trap, (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧ out = (.Err (.Trap trap), exec)

theorem integer_values {F : Type} (floats : runtime.platform.FloatOps F)
    (exec : runtime.interp.Execution) (base : Usize) (op : Instruction)
    (left right : U32) (front : List val)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (values : ValuesAt exec.slots.val base.val (front ++ op.operands a b))
    (hl : left.val = Representation.slots (front.map Representation.valueType))
    (hr : right.val = left.val + (op.arity - 1)) :
    runtime.interp.execute_scalar floats exec base (Compiler.integerOpcode op) left left right ⦃
      NumericValuesEffect op a b exec base.val front ⦄ := by
  have position : left.val = (Representation.encodeValues front).length := by
    simpa only [Representation.encode_values_length] using hl
  have post : ∀ out, NumericWordsEffect op a b exec base.val (Representation.encodeValues front) out →
      NumericValuesEffect op a b exec base.val front out := by
    intro out effect
    cases operation : op.apply a b <;>
      simpa only [NumericWordsEffect, NumericValuesEffect, operation, ValuesAt,
        Representation.encode_values_append, Representation.encodeValues, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        SourceMachine.integerVal, Representation.encodeValue, List.append_nil] using effect
  rcases op.arity_cases with one | two
  · have same : right = left := UScalar.eq_of_val_eq (by simpa [one] using hr)
    subst right
    have words : WordsAt exec.slots.val base.val (Representation.encodeValues front ++ [a.toNat]) := by
      simpa only [ValuesAt, Instruction.operands, one, if_true, Representation.encode_values_append,
        Representation.encodeValues, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, SourceMachine.integerVal, Representation.encodeValue,
        List.append_nil] using values
    exact WP.spec_mono (integer_unary_words floats exec base op left (Representation.encodeValues front) a b one words position) post
  · have words : WordsAt exec.slots.val base.val (Representation.encodeValues front ++ [a.toNat, b.toNat]) := by
      simpa only [ValuesAt, Instruction.operands, two, Nat.reduceEqDiff, if_false, Representation.encode_values_append,
        Representation.encodeValues, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, SourceMachine.integerVal, Representation.encodeValue,
        List.singleton_append, List.append_nil] using values
    have second : right.val = (Representation.encodeValues front).length + 1 := by simpa [two, position] using hr
    exact WP.spec_mono (integer_binary_words floats exec base op left right (Representation.encodeValues front) a b words position second) post
end Itasca.Interp

end

/-! ## Numeric Fetch -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std SourceMachine.Numeric

theorem step_integer_values {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (op : Instruction) (left right : U32) (front : List val)
    (a b : BitVec (sizenn (numtype_Inn op.input)))
    (last : index.val + 1 = exec.frames.length)
    (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Compiler.integerInstruction op left left right))
    (pcBound : raw.pc.val < U32.max)
    (values : ValuesAt exec.slots.val raw.base.val (front ++ op.operands a b))
    (hl : left.val = Representation.slots (front.map Representation.valueType))
    (hr : right.val = left.val + (op.arity - 1)) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ∃ pc : U32, pc.val = raw.pc.val + 1 ∧
        NumericValuesEffect op a b
          { exec with frames := exec.frames.set index { raw with pc := pc } }
          raw.base.val front (out.1, out.2.1) ⦄ := by
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (Compiler.integerInstruction op left left right) last hf hi hc fetched pcBound
  intro pc position
  rw [dispatch_integer_eq]
  obtain ⟨out, equation, effect⟩ := WP.spec_imp_exists (integer_values floats
    { exec with frames := exec.frames.set index { raw with pc := pc } } raw.base op left right front a b values hl hr)
  rw [equation]
  rcases out with ⟨status, changed⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨rfl, rfl, pc, position, effect⟩
end Itasca.Interp

end

end

end

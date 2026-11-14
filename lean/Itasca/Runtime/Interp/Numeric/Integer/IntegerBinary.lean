import Itasca.Runtime.Interp.Numeric.Integer.IntCounts
import Itasca.Runtime.Spec.SegmentInitCases
import Itasca.Runtime.SourceMachine.Numeric.TransitionSafety
import Itasca.Runtime.Spec.FloatTrunc

/-!
Sections, each formerly its own module: IntExtend, IntCompareSigned, IntegerBinary.
-/

/-! ## IntExtend -/

section

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

end

/-! ## IntCompareSigned -/

section

namespace Itasca.Runtime.Interp
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

end Itasca.Runtime.Interp

end

/-! ## IntegerBinary -/

section

namespace Itasca.Runtime.Interp
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

end Itasca.Runtime.Interp

end

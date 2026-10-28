import Exec.Interp.Numeric.Integer.IntExtend
import Exec.Spec.IntegerCompareSigned
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

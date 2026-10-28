import Itasca.Runtime.Equations
import Itasca.Runtime.Abs.Sim.Int
import Itasca.Runtime.Spec.IntegerDiv
import Itasca.Runtime.Spec.IntegerBits

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem scalar_i32_add_eq {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 106#u16 a b = .ok (.Ok (UScalar.cast .U64 (core.num.U32.wrapping_add (UScalar.cast .U32 a) (UScalar.cast .U32 b)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (lift (core.num.U32.wrapping_add (UScalar.cast .U32 a) (UScalar.cast .U32 b))) (fun v =>
    Aeneas.Std.bind (lift (UScalar.cast .U64 v)) (fun out =>
      Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError))) = _
  rw [lift, bind_ok, lift, bind_ok]

@[step] theorem scalar_i32_add {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.int.scalar ops 106#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = (a.val + b.val) % 4294967296 ⦄ := by
  rw [scalar_i32_add_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  simp [U32.size, U32.numBits, Nat.add_mod]

theorem scalar_i64_add_eq {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 124#u16 a b = .ok (.Ok (core.num.U64.wrapping_add a b)) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (lift (core.num.U64.wrapping_add a b)) (fun v =>
    Result.ok (core.result.Result.Ok v : core.result.Result U64 runtime.ExecError)) = _
  rw [lift, bind_ok]

@[step] theorem scalar_i64_add {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.int.scalar ops 124#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = (a.val + b.val) % 18446744073709551616 ⦄ := by
  rw [scalar_i64_add_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  simp [U64.size, U64.numBits]

theorem scalar_i32_sub_eq {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 107#u16 a b = .ok (.Ok (UScalar.cast .U64 (core.num.U32.wrapping_sub (UScalar.cast .U32 a) (UScalar.cast .U32 b)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (lift (core.num.U32.wrapping_sub (UScalar.cast .U32 a) (UScalar.cast .U32 b))) (fun v =>
    Aeneas.Std.bind (lift (UScalar.cast .U64 v)) (fun out =>
      Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError))) = _
  rw [lift, bind_ok, lift, bind_ok]

@[step] theorem scalar_i32_sub {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.int.scalar ops 107#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = (a.val % 4294967296 + 4294967296 - b.val % 4294967296) % 4294967296 ⦄ := by
  rw [scalar_i32_sub_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  have hb : b.val % 4294967296 ≤ 4294967296 := by omega
  rw [U32.cast_U64_val_eq]
  simp only [core.num.U32.wrapping_sub_val_eq, UScalar.cast_val_eq]
  norm_num only [UScalar.size, UScalarTy.numBits]
  congr 1
  omega

theorem scalar_i64_sub_eq {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 125#u16 a b = .ok (.Ok (core.num.U64.wrapping_sub a b)) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (lift (core.num.U64.wrapping_sub a b)) (fun v =>
    Result.ok (core.result.Result.Ok v : core.result.Result U64 runtime.ExecError)) = _
  rw [lift, bind_ok]

@[step] theorem scalar_i64_sub {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.int.scalar ops 125#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = (a.val + 18446744073709551616 - b.val) % 18446744073709551616 ⦄ := by
  rw [scalar_i64_sub_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  have hb : b.val ≤ 18446744073709551616 := by scalar_tac
  simp only [core.num.U64.wrapping_sub_val_eq]
  norm_num only [UScalar.size, UScalarTy.numBits]
  congr 1
  omega

theorem scalar_i32_mul_eq {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 108#u16 a b = .ok (.Ok (UScalar.cast .U64 (core.num.U32.wrapping_mul (UScalar.cast .U32 a) (UScalar.cast .U32 b)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (lift (core.num.U32.wrapping_mul (UScalar.cast .U32 a) (UScalar.cast .U32 b))) (fun v =>
    Aeneas.Std.bind (lift (UScalar.cast .U64 v)) (fun out =>
      Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError))) = _
  rw [lift, bind_ok, lift, bind_ok]

@[step] theorem scalar_i32_mul {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.int.scalar ops 108#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = (a.val * b.val) % 4294967296 ⦄ := by
  rw [scalar_i32_mul_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  simp [U32.size, U32.numBits, Nat.mul_mod]

theorem scalar_i64_mul_eq {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 126#u16 a b = .ok (.Ok (core.num.U64.wrapping_mul a b)) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (lift (core.num.U64.wrapping_mul a b)) (fun v =>
    Result.ok (core.result.Result.Ok v : core.result.Result U64 runtime.ExecError)) = _
  rw [lift, bind_ok]

@[step] theorem scalar_i64_mul {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.int.scalar ops 126#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = (a.val * b.val) % 18446744073709551616 ⦄ := by
  rw [scalar_i64_mul_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  simp [U64.size, U64.numBits]

/-- Multiplication's mathematical result satisfies the pinned numerical rule. -/
theorem integer_mul_relation (ty : Inn) (a b : Nat) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty .MUL)
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some [.mk_num__0 ty (.mk_uN ((a * b) % 2 ^ Abs.integerWidth ty))]) := by
  have hb : (a * b) % 2 ^ Abs.integerWidth ty < 2 ^ Abs.integerWidth ty :=
    Nat.mod_lt _ (by positivity)
  have hn := Abs.integer_num_wf ty _ hb
  have hu := Abs.integer_uN_wf ty _ hb
  cases ty with
  | I32 => exact .fun_binop__case_4 _ _ _ (.fun_imul__case_0 _ _ _ hu) hn
  | I64 => exact .fun_binop__case_5 _ _ _ (.fun_imul__case_0 _ _ _ hu) hn

/-- The extracted scalar handler implements the generated i32.add relation. -/
theorem scalar_i32_add_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.int.scalar ops 106#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_binop_ .I32 (.mk_binop__0 .I32 .ADD)
          (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296)))
          (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296)))
          (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i32_add ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  simpa [numtype_Inn, Abs.integerWidth, Nat.add_mod] using Abs.integer_add_relation .I32 (a.val % 4294967296) (b.val % 4294967296)

/-- The extracted scalar handler implements the generated i64.add relation. -/
theorem scalar_i64_add_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.int.scalar ops 124#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_binop_ .I64 (.mk_binop__0 .I64 .ADD)
          (.mk_num__0 .I64 (.mk_uN (a.val)))
          (.mk_num__0 .I64 (.mk_uN (b.val)))
          (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i64_add ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  simpa [numtype_Inn, Abs.integerWidth] using Abs.integer_add_relation .I64 (a.val) (b.val)

/-- The extracted scalar handler implements the generated i32.sub relation. -/
theorem scalar_i32_sub_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.int.scalar ops 107#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_binop_ .I32 (.mk_binop__0 .I32 .SUB)
          (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296)))
          (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296)))
          (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i32_sub ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  have hb : b.val % 4294967296 < 2 ^ Abs.integerWidth .I32 := by change b.val % 4294967296 < 4294967296; omega
  exact Abs.integer_sub_relation .I32 (a.val % 4294967296) (b.val % 4294967296) hb

/-- The extracted scalar handler implements the generated i64.sub relation. -/
theorem scalar_i64_sub_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.int.scalar ops 125#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_binop_ .I64 (.mk_binop__0 .I64 .SUB)
          (.mk_num__0 .I64 (.mk_uN (a.val)))
          (.mk_num__0 .I64 (.mk_uN (b.val)))
          (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i64_sub ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  have hb : b.val < 2 ^ Abs.integerWidth .I64 := by change b.val < 18446744073709551616; scalar_tac
  exact Abs.integer_sub_relation .I64 (a.val) (b.val) hb

/-- The extracted scalar handler implements the generated i32.mul relation. -/
theorem scalar_i32_mul_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.int.scalar ops 108#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_binop_ .I32 (.mk_binop__0 .I32 .MUL)
          (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296)))
          (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296)))
          (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i32_mul ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  simpa [numtype_Inn, Abs.integerWidth, Nat.mul_mod] using integer_mul_relation .I32 (a.val % 4294967296) (b.val % 4294967296)

/-- The extracted scalar handler implements the generated i64.mul relation. -/
theorem scalar_i64_mul_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) :
    runtime.interp.int.scalar ops 126#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_binop_ .I64 (.mk_binop__0 .I64 .MUL)
          (.mk_num__0 .I64 (.mk_uN (a.val)))
          (.mk_num__0 .I64 (.mk_uN (b.val)))
          (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i64_mul ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  simpa [numtype_Inn, Abs.integerWidth] using integer_mul_relation .I64 (a.val) (b.val)

theorem scalar_i32_eqz_eq {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 69#u16 a b =
      .ok (.Ok (UScalar.cast_fromBool .U64 (decide ((UScalar.cast .U32 a) = 0#u32)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 (decide ((UScalar.cast .U32 a) = 0#u32))))
    (fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) = _
  rw [lift, bind_ok]

@[step] theorem scalar_i32_eqz {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 69#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = if a.val % 4294967296 = 0 then 1 else 0 ⦄ := by
  rw [scalar_i32_eqz_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  simp [UScalar.eq_equiv, Bool.toNat]

theorem scalar_i64_eqz_eq {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 80#u16 a b =
      .ok (.Ok (UScalar.cast_fromBool .U64 (decide ((a) = 0#u64)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 (decide ((a) = 0#u64))))
    (fun out => Result.ok (core.result.Result.Ok out : core.result.Result U64 runtime.ExecError)) = _
  rw [lift, bind_ok]

@[step] theorem scalar_i64_eqz {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 80#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = if a.val = 0 then 1 else 0 ⦄ := by
  rw [scalar_i64_eqz_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  simp [UScalar.eq_equiv, Bool.toNat]

@[step] theorem compare_int_eq (a b : U64) (width : U32)
    (hw : 0 < width.val) (hw' : width.val ≤ 64) :
    runtime.interp.int.compare_int 0#u16 a b width ⦃ result => result = decide (a.val = b.val) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have hs : i.val < 64 := by scalar_tac
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    UScalarTy.numBits, hs, if_true, bind_ok, lift, HShiftRight.hShiftRight,
    IScalar.shiftRight_UScalar, IScalar.shiftRight, IScalarTy.numBits]
  with_unfolding_all change Result.ok (decide (a = b)) ⦃ result => result = decide (a.val = b.val) ⦄
  simp [UScalar.eq_equiv]

@[step] theorem compare_int_ne (a b : U64) (width : U32)
    (hw : 0 < width.val) (hw' : width.val ≤ 64) :
    runtime.interp.int.compare_int 1#u16 a b width ⦃ result => result = decide (a.val ≠ b.val) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have hs : i.val < 64 := by scalar_tac
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    UScalarTy.numBits, hs, if_true, bind_ok, lift, HShiftRight.hShiftRight,
    IScalar.shiftRight_UScalar, IScalar.shiftRight, IScalarTy.numBits]
  with_unfolding_all change Result.ok (a != b) ⦃ result => result = decide (a.val ≠ b.val) ⦄
  simp [bne, BEq.beq]
  constructor
  · intro h; exact congrArg BitVec.toNat h
  · intro h; exact BitVec.eq_of_toNat_eq h

@[step] theorem compare_int_ltu (a b : U64) (width : U32)
    (hw : 0 < width.val) (hw' : width.val ≤ 64) :
    runtime.interp.int.compare_int 3#u16 a b width ⦃ result => result = decide (a.val < b.val) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have hs : i.val < 64 := by scalar_tac
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    UScalarTy.numBits, hs, if_true, bind_ok, lift, HShiftRight.hShiftRight,
    IScalar.shiftRight_UScalar, IScalar.shiftRight, IScalarTy.numBits]
  with_unfolding_all change Result.ok (decide (a < b)) ⦃ result => result = decide (a.val < b.val) ⦄
  simp [UScalar.eq_equiv, UScalar.lt_equiv, UScalar.le_equiv]

@[step] theorem compare_int_gtu (a b : U64) (width : U32)
    (hw : 0 < width.val) (hw' : width.val ≤ 64) :
    runtime.interp.int.compare_int 5#u16 a b width ⦃ result => result = decide (a.val > b.val) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have hs : i.val < 64 := by scalar_tac
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    UScalarTy.numBits, hs, if_true, bind_ok, lift, HShiftRight.hShiftRight,
    IScalar.shiftRight_UScalar, IScalar.shiftRight, IScalarTy.numBits]
  with_unfolding_all change Result.ok (decide (a > b)) ⦃ result => result = decide (a.val > b.val) ⦄
  simp [UScalar.eq_equiv, UScalar.lt_equiv, UScalar.le_equiv]

@[step] theorem compare_int_leu (a b : U64) (width : U32)
    (hw : 0 < width.val) (hw' : width.val ≤ 64) :
    runtime.interp.int.compare_int 7#u16 a b width ⦃ result => result = decide (a.val ≤ b.val) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have hs : i.val < 64 := by scalar_tac
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    UScalarTy.numBits, hs, if_true, bind_ok, lift, HShiftRight.hShiftRight,
    IScalar.shiftRight_UScalar, IScalar.shiftRight, IScalarTy.numBits]
  with_unfolding_all change Result.ok (decide (a ≤ b)) ⦃ result => result = decide (a.val ≤ b.val) ⦄
  simp [UScalar.eq_equiv, UScalar.lt_equiv, UScalar.le_equiv]

@[step] theorem compare_int_geu (a b : U64) (width : U32)
    (hw : 0 < width.val) (hw' : width.val ≤ 64) :
    runtime.interp.int.compare_int 9#u16 a b width ⦃ result => result = decide (a.val ≥ b.val) ⦄ := by
  unfold runtime.interp.int.compare_int
  step as ⟨i, hi⟩
  have hs : i.val < 64 := by scalar_tac
  simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft,
    UScalarTy.numBits, hs, if_true, bind_ok, lift, HShiftRight.hShiftRight,
    IScalar.shiftRight_UScalar, IScalar.shiftRight, IScalarTy.numBits]
  with_unfolding_all change Result.ok (decide (a ≥ b)) ⦃ result => result = decide (a.val ≥ b.val) ⦄
  simp [UScalar.eq_equiv, UScalar.lt_equiv, UScalar.le_equiv]

@[step] theorem scalar_i32_eq {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 70#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = if a.val % 4294967296 = b.val % 4294967296 then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (70#u16 - 70#u16) (fun i =>
    Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 a))) (fun x =>
      Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 b))) (fun y =>
        Aeneas.Std.bind (runtime.interp.int.compare_int i x y 32#u32) (fun answer =>
          Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result =>
            Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have hi' : i = 0#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : a.val % 4294967296 = b.val % 4294967296 <;> simp_all

@[step] theorem scalar_i32_ne {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 71#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = if a.val % 4294967296 ≠ b.val % 4294967296 then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (71#u16 - 70#u16) (fun i =>
    Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 a))) (fun x =>
      Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 b))) (fun y =>
        Aeneas.Std.bind (runtime.interp.int.compare_int i x y 32#u32) (fun answer =>
          Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result =>
            Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have hi' : i = 1#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : a.val % 4294967296 ≠ b.val % 4294967296 <;> simp_all

@[step] theorem scalar_i32_ltu {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 73#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = if a.val % 4294967296 < b.val % 4294967296 then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (73#u16 - 70#u16) (fun i =>
    Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 a))) (fun x =>
      Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 b))) (fun y =>
        Aeneas.Std.bind (runtime.interp.int.compare_int i x y 32#u32) (fun answer =>
          Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result =>
            Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have hi' : i = 3#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : a.val % 4294967296 < b.val % 4294967296 <;> simp_all

@[step] theorem scalar_i32_gtu {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 75#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = if a.val % 4294967296 > b.val % 4294967296 then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (75#u16 - 70#u16) (fun i =>
    Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 a))) (fun x =>
      Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 b))) (fun y =>
        Aeneas.Std.bind (runtime.interp.int.compare_int i x y 32#u32) (fun answer =>
          Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result =>
            Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have hi' : i = 5#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : a.val % 4294967296 > b.val % 4294967296 <;> simp_all

@[step] theorem scalar_i32_leu {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 77#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = if a.val % 4294967296 ≤ b.val % 4294967296 then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (77#u16 - 70#u16) (fun i =>
    Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 a))) (fun x =>
      Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 b))) (fun y =>
        Aeneas.Std.bind (runtime.interp.int.compare_int i x y 32#u32) (fun answer =>
          Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result =>
            Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have hi' : i = 7#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : a.val % 4294967296 ≤ b.val % 4294967296 <;> simp_all

@[step] theorem scalar_i32_geu {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 79#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = if a.val % 4294967296 ≥ b.val % 4294967296 then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (79#u16 - 70#u16) (fun i =>
    Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 a))) (fun x =>
      Aeneas.Std.bind (lift (UScalar.cast .U64 (UScalar.cast .U32 b))) (fun y =>
        Aeneas.Std.bind (runtime.interp.int.compare_int i x y 32#u32) (fun answer =>
          Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result =>
            Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have hi' : i = 9#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : a.val % 4294967296 ≥ b.val % 4294967296 <;> simp_all

@[step] theorem scalar_i64_eq {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 81#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = if a.val = b.val then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (81#u16 - 81#u16) (fun i =>
    Aeneas.Std.bind (runtime.interp.int.compare_int i a b 64#u32) (fun answer =>
      Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result =>
        Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have hi' : i = 0#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : a.val = b.val <;> simp_all

@[step] theorem scalar_i64_ne {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 82#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = if a.val ≠ b.val then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (82#u16 - 81#u16) (fun i =>
    Aeneas.Std.bind (runtime.interp.int.compare_int i a b 64#u32) (fun answer =>
      Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result =>
        Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have hi' : i = 1#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : a.val ≠ b.val <;> simp_all

@[step] theorem scalar_i64_ltu {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 84#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = if a.val < b.val then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (84#u16 - 81#u16) (fun i =>
    Aeneas.Std.bind (runtime.interp.int.compare_int i a b 64#u32) (fun answer =>
      Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result =>
        Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have hi' : i = 3#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : a.val < b.val <;> simp_all

@[step] theorem scalar_i64_gtu {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 86#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = if a.val > b.val then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (86#u16 - 81#u16) (fun i =>
    Aeneas.Std.bind (runtime.interp.int.compare_int i a b 64#u32) (fun answer =>
      Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result =>
        Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have hi' : i = 5#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : a.val > b.val <;> simp_all

@[step] theorem scalar_i64_leu {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 88#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = if a.val ≤ b.val then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (88#u16 - 81#u16) (fun i =>
    Aeneas.Std.bind (runtime.interp.int.compare_int i a b 64#u32) (fun answer =>
      Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result =>
        Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have hi' : i = 7#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : a.val ≤ b.val <;> simp_all

@[step] theorem scalar_i64_geu {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 90#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧ value.val = if a.val ≥ b.val then 1 else 0 ⦄ := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (90#u16 - 81#u16) (fun i =>
    Aeneas.Std.bind (runtime.interp.int.compare_int i a b 64#u32) (fun answer =>
      Aeneas.Std.bind (lift (UScalar.cast_fromBool .U64 answer)) (fun result =>
        Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) ⦃ _ ⦄
  step as ⟨i, hi⟩
  have hi' : i = 9#u16 := by apply (UScalar.eq_equiv _ _).mpr; simpa using hi
  subst i
  step*
  refine ⟨result, rfl, ?_⟩
  by_cases h : a.val ≥ b.val <;> simp_all

/-- The extracted i32.eq handler implements the generated relation. -/
theorem scalar_i32_eq_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 70#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_relop_ .I32 (.mk_relop__0 .I32 .EQ)
          (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296)))
          (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296)))
          (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i32_eq ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  exact Spec.integer_eq_relation .I32 (a.val % 4294967296) (b.val % 4294967296)

/-- The extracted i32.ne handler implements the generated relation. -/
theorem scalar_i32_ne_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 71#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_relop_ .I32 (.mk_relop__0 .I32 .NE)
          (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296)))
          (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296)))
          (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i32_ne ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  exact Spec.integer_ne_relation .I32 (a.val % 4294967296) (b.val % 4294967296)

/-- The extracted i32.ltu handler implements the generated relation. -/
theorem scalar_i32_ltu_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 73#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_relop_ .I32 (.mk_relop__0 .I32 (.LT .U))
          (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296)))
          (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296)))
          (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i32_ltu ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  exact Spec.integer_ltu_relation .I32 (a.val % 4294967296) (b.val % 4294967296)

/-- The extracted i32.gtu handler implements the generated relation. -/
theorem scalar_i32_gtu_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 75#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_relop_ .I32 (.mk_relop__0 .I32 (.GT .U))
          (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296)))
          (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296)))
          (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i32_gtu ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  exact Spec.integer_gtu_relation .I32 (a.val % 4294967296) (b.val % 4294967296)

/-- The extracted i32.leu handler implements the generated relation. -/
theorem scalar_i32_leu_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 77#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_relop_ .I32 (.mk_relop__0 .I32 (.LE .U))
          (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296)))
          (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296)))
          (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i32_leu ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  exact Spec.integer_leu_relation .I32 (a.val % 4294967296) (b.val % 4294967296)

/-- The extracted i32.geu handler implements the generated relation. -/
theorem scalar_i32_geu_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 79#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_relop_ .I32 (.mk_relop__0 .I32 (.GE .U))
          (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296)))
          (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296)))
          (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i32_geu ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  exact Spec.integer_geu_relation .I32 (a.val % 4294967296) (b.val % 4294967296)

/-- The extracted i64.eq handler implements the generated relation. -/
theorem scalar_i64_eq_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 81#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_relop_ .I64 (.mk_relop__0 .I64 .EQ)
          (.mk_num__0 .I64 (.mk_uN a.val))
          (.mk_num__0 .I64 (.mk_uN b.val))
          (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i64_eq ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  exact Spec.integer_eq_relation .I64 a.val b.val

/-- The extracted i64.ne handler implements the generated relation. -/
theorem scalar_i64_ne_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 82#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_relop_ .I64 (.mk_relop__0 .I64 .NE)
          (.mk_num__0 .I64 (.mk_uN a.val))
          (.mk_num__0 .I64 (.mk_uN b.val))
          (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i64_ne ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  exact Spec.integer_ne_relation .I64 a.val b.val

/-- The extracted i64.ltu handler implements the generated relation. -/
theorem scalar_i64_ltu_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 84#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_relop_ .I64 (.mk_relop__0 .I64 (.LT .U))
          (.mk_num__0 .I64 (.mk_uN a.val))
          (.mk_num__0 .I64 (.mk_uN b.val))
          (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i64_ltu ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  exact Spec.integer_ltu_relation .I64 a.val b.val

/-- The extracted i64.gtu handler implements the generated relation. -/
theorem scalar_i64_gtu_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 86#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_relop_ .I64 (.mk_relop__0 .I64 (.GT .U))
          (.mk_num__0 .I64 (.mk_uN a.val))
          (.mk_num__0 .I64 (.mk_uN b.val))
          (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i64_gtu ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  exact Spec.integer_gtu_relation .I64 a.val b.val

/-- The extracted i64.leu handler implements the generated relation. -/
theorem scalar_i64_leu_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 88#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_relop_ .I64 (.mk_relop__0 .I64 (.LE .U))
          (.mk_num__0 .I64 (.mk_uN a.val))
          (.mk_num__0 .I64 (.mk_uN b.val))
          (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i64_leu ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  exact Spec.integer_leu_relation .I64 a.val b.val

/-- The extracted i64.geu handler implements the generated relation. -/
theorem scalar_i64_geu_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 90#u16 a b ⦃ r =>
      ∃ value, r = .Ok value ∧
        fun_relop_ .I64 (.mk_relop__0 .I64 (.GE .U))
          (.mk_num__0 .I64 (.mk_uN a.val))
          (.mk_num__0 .I64 (.mk_uN b.val))
          (some (.mk_num__0 .I32 (.mk_uN value.val))) ⦄ := by
  obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i64_geu ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, rfl, ?_⟩
  rw [hv]
  exact Spec.integer_geu_relation .I64 a.val b.val

/-- i32.divu traps on zero without a machine failure. -/
@[step] theorem scalar_i32_divu_zero {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) (hb : (b.val % 4294967296) = 0) :
    runtime.interp.int.scalar ops 110#u16 a b ⦃ r => r = .Err (.Trap .IntegerDivideByZero) ⦄ := by
  have hz : (UScalar.cast .U32 b) = 0#u32 := by simpa [UScalar.eq_equiv] using hb
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (if (UScalar.cast .U32 b) = 0#u32 then
    Result.ok (core.result.Result.Err (runtime.ExecError.Trap runtime.Trap.IntegerDivideByZero))
    else Aeneas.Std.bind ((UScalar.cast .U32 a) / (UScalar.cast .U32 b)) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value)) (fun result =>
          Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) ⦃ _ ⦄
  rw [if_pos hz]
  simp only [WP.spec_ok]

/-- i32.divu returns the unsigned quotient/remainder without a machine failure. -/
@[step] theorem scalar_i32_divu_nonzero {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) (hb : (b.val % 4294967296) ≠ 0) :
    runtime.interp.int.scalar ops 110#u16 a b ⦃ r => ∃ value, r = .Ok value ∧ value.val = (a.val % 4294967296) / (b.val % 4294967296) ⦄ := by
  have hz : (UScalar.cast .U32 b) ≠ 0#u32 := by simpa [UScalar.eq_equiv] using hb
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (if (UScalar.cast .U32 b) = 0#u32 then
    Result.ok (core.result.Result.Err (runtime.ExecError.Trap runtime.Trap.IntegerDivideByZero))
    else Aeneas.Std.bind ((UScalar.cast .U32 a) / (UScalar.cast .U32 b)) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value)) (fun result =>
          Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) ⦃ _ ⦄
  rw [if_neg hz]
  step as ⟨value, hvalue⟩
  rw [lift, bind_ok]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  rw [U32.cast_U64_val_eq]
  simpa using hvalue

/-- i32.remu traps on zero without a machine failure. -/
@[step] theorem scalar_i32_remu_zero {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) (hb : (b.val % 4294967296) = 0) :
    runtime.interp.int.scalar ops 112#u16 a b ⦃ r => r = .Err (.Trap .IntegerDivideByZero) ⦄ := by
  have hz : (UScalar.cast .U32 b) = 0#u32 := by simpa [UScalar.eq_equiv] using hb
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (if (UScalar.cast .U32 b) = 0#u32 then
    Result.ok (core.result.Result.Err (runtime.ExecError.Trap runtime.Trap.IntegerDivideByZero))
    else Aeneas.Std.bind ((UScalar.cast .U32 a) % (UScalar.cast .U32 b)) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value)) (fun result =>
          Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) ⦃ _ ⦄
  rw [if_pos hz]
  simp only [WP.spec_ok]

/-- i32.remu returns the unsigned quotient/remainder without a machine failure. -/
@[step] theorem scalar_i32_remu_nonzero {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) (hb : (b.val % 4294967296) ≠ 0) :
    runtime.interp.int.scalar ops 112#u16 a b ⦃ r => ∃ value, r = .Ok value ∧ value.val = (a.val % 4294967296) % (b.val % 4294967296) ⦄ := by
  have hz : (UScalar.cast .U32 b) ≠ 0#u32 := by simpa [UScalar.eq_equiv] using hb
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (if (UScalar.cast .U32 b) = 0#u32 then
    Result.ok (core.result.Result.Err (runtime.ExecError.Trap runtime.Trap.IntegerDivideByZero))
    else Aeneas.Std.bind ((UScalar.cast .U32 a) % (UScalar.cast .U32 b)) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value)) (fun result =>
          Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) ⦃ _ ⦄
  rw [if_neg hz]
  step as ⟨value, hvalue⟩
  rw [lift, bind_ok]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  rw [U32.cast_U64_val_eq]
  simpa using hvalue

/-- i64.divu traps on zero without a machine failure. -/
@[step] theorem scalar_i64_divu_zero {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) (hb : b.val = 0) :
    runtime.interp.int.scalar ops 128#u16 a b ⦃ r => r = .Err (.Trap .IntegerDivideByZero) ⦄ := by
  have hz : b = 0#u64 := by simpa [UScalar.eq_equiv] using hb
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (if b = 0#u64 then
    Result.ok (core.result.Result.Err (runtime.ExecError.Trap runtime.Trap.IntegerDivideByZero))
    else Aeneas.Std.bind (a / b) (fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError))) ⦃ _ ⦄
  rw [if_pos hz]
  simp only [WP.spec_ok]

/-- i64.divu returns the unsigned quotient/remainder without a machine failure. -/
@[step] theorem scalar_i64_divu_nonzero {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) (hb : b.val ≠ 0) :
    runtime.interp.int.scalar ops 128#u16 a b ⦃ r => ∃ value, r = .Ok value ∧ value.val = a.val / b.val ⦄ := by
  have hz : b ≠ 0#u64 := by simpa [UScalar.eq_equiv] using hb
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (if b = 0#u64 then
    Result.ok (core.result.Result.Err (runtime.ExecError.Trap runtime.Trap.IntegerDivideByZero))
    else Aeneas.Std.bind (a / b) (fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError))) ⦃ _ ⦄
  rw [if_neg hz]
  step as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

/-- i64.remu traps on zero without a machine failure. -/
@[step] theorem scalar_i64_remu_zero {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) (hb : b.val = 0) :
    runtime.interp.int.scalar ops 130#u16 a b ⦃ r => r = .Err (.Trap .IntegerDivideByZero) ⦄ := by
  have hz : b = 0#u64 := by simpa [UScalar.eq_equiv] using hb
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (if b = 0#u64 then
    Result.ok (core.result.Result.Err (runtime.ExecError.Trap runtime.Trap.IntegerDivideByZero))
    else Aeneas.Std.bind (a % b) (fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError))) ⦃ _ ⦄
  rw [if_pos hz]
  simp only [WP.spec_ok]

/-- i64.remu returns the unsigned quotient/remainder without a machine failure. -/
@[step] theorem scalar_i64_remu_nonzero {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) (hb : b.val ≠ 0) :
    runtime.interp.int.scalar ops 130#u16 a b ⦃ r => ∃ value, r = .Ok value ∧ value.val = a.val % b.val ⦄ := by
  have hz : b ≠ 0#u64 := by simpa [UScalar.eq_equiv] using hb
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change (if b = 0#u64 then
    Result.ok (core.result.Result.Err (runtime.ExecError.Trap runtime.Trap.IntegerDivideByZero))
    else Aeneas.Std.bind (a % b) (fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError))) ⦃ _ ⦄
  rw [if_neg hz]
  step as ⟨value, hvalue⟩
  refine ⟨_, rfl, ?_⟩
  exact hvalue

/-- Both ordinary and trapping results of extracted i32.divu satisfy the generated operator rule. -/
theorem scalar_i32_divu_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 110#u16 a b ⦃ r =>
      (∃ value, r = .Ok value ∧ fun_binop_ .I32 (.mk_binop__0 .I32 (.DIV .U))
          (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296)))
          (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296)))
          (some [.mk_num__0 .I32 (.mk_uN value.val)])) ∨
      (r = .Err (.Trap .IntegerDivideByZero) ∧ fun_binop_ .I32 (.mk_binop__0 .I32 (.DIV .U))
          (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296)))
          (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296))) (some [])) ⦄ := by
  by_cases hb : (b.val % 4294967296) = 0
  · obtain ⟨_, hr, rfl⟩ := WP.spec_imp_exists (scalar_i32_divu_zero ops a b hb)
    rw [hr]
    simp only [WP.spec_ok]
    right
    refine ⟨trivial, ?_⟩
    rw [hb]
    exact Spec.integer_divu_zero_relation .I32 (a.val % 4294967296)
  · obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i32_divu_nonzero ops a b hb)
    rw [hr]
    simp only [WP.spec_ok]
    left
    refine ⟨value, rfl, ?_⟩
    rw [hv]
    apply Spec.integer_divu_relation .I32 (a.val % 4294967296) (b.val % 4294967296) _ hb
    change (a.val % 4294967296) < 4294967296
    omega

/-- Both ordinary and trapping results of extracted i32.remu satisfy the generated operator rule. -/
theorem scalar_i32_remu_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 112#u16 a b ⦃ r =>
      (∃ value, r = .Ok value ∧ fun_binop_ .I32 (.mk_binop__0 .I32 (.REM .U))
          (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296)))
          (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296)))
          (some [.mk_num__0 .I32 (.mk_uN value.val)])) ∨
      (r = .Err (.Trap .IntegerDivideByZero) ∧ fun_binop_ .I32 (.mk_binop__0 .I32 (.REM .U))
          (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296)))
          (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296))) (some [])) ⦄ := by
  by_cases hb : (b.val % 4294967296) = 0
  · obtain ⟨_, hr, rfl⟩ := WP.spec_imp_exists (scalar_i32_remu_zero ops a b hb)
    rw [hr]
    simp only [WP.spec_ok]
    right
    refine ⟨trivial, ?_⟩
    rw [hb]
    exact Spec.integer_remu_zero_relation .I32 (a.val % 4294967296)
  · obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i32_remu_nonzero ops a b hb)
    rw [hr]
    simp only [WP.spec_ok]
    left
    refine ⟨value, rfl, ?_⟩
    rw [hv]
    apply Spec.integer_remu_relation .I32 (a.val % 4294967296) (b.val % 4294967296) _ hb
    change (a.val % 4294967296) < 4294967296
    omega

/-- Both ordinary and trapping results of extracted i64.divu satisfy the generated operator rule. -/
theorem scalar_i64_divu_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 128#u16 a b ⦃ r =>
      (∃ value, r = .Ok value ∧ fun_binop_ .I64 (.mk_binop__0 .I64 (.DIV .U))
          (.mk_num__0 .I64 (.mk_uN a.val))
          (.mk_num__0 .I64 (.mk_uN b.val))
          (some [.mk_num__0 .I64 (.mk_uN value.val)])) ∨
      (r = .Err (.Trap .IntegerDivideByZero) ∧ fun_binop_ .I64 (.mk_binop__0 .I64 (.DIV .U))
          (.mk_num__0 .I64 (.mk_uN a.val))
          (.mk_num__0 .I64 (.mk_uN b.val)) (some [])) ⦄ := by
  by_cases hb : b.val = 0
  · obtain ⟨_, hr, rfl⟩ := WP.spec_imp_exists (scalar_i64_divu_zero ops a b hb)
    rw [hr]
    simp only [WP.spec_ok]
    right
    refine ⟨trivial, ?_⟩
    rw [hb]
    exact Spec.integer_divu_zero_relation .I64 a.val
  · obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i64_divu_nonzero ops a b hb)
    rw [hr]
    simp only [WP.spec_ok]
    left
    refine ⟨value, rfl, ?_⟩
    rw [hv]
    apply Spec.integer_divu_relation .I64 a.val b.val _ hb
    change a.val < 18446744073709551616
    scalar_tac

/-- Both ordinary and trapping results of extracted i64.remu satisfy the generated operator rule. -/
theorem scalar_i64_remu_sound {F : Type} (ops : runtime.platform.FloatOps F)
    (a b : U64) : runtime.interp.int.scalar ops 130#u16 a b ⦃ r =>
      (∃ value, r = .Ok value ∧ fun_binop_ .I64 (.mk_binop__0 .I64 (.REM .U))
          (.mk_num__0 .I64 (.mk_uN a.val))
          (.mk_num__0 .I64 (.mk_uN b.val))
          (some [.mk_num__0 .I64 (.mk_uN value.val)])) ∨
      (r = .Err (.Trap .IntegerDivideByZero) ∧ fun_binop_ .I64 (.mk_binop__0 .I64 (.REM .U))
          (.mk_num__0 .I64 (.mk_uN a.val))
          (.mk_num__0 .I64 (.mk_uN b.val)) (some [])) ⦄ := by
  by_cases hb : b.val = 0
  · obtain ⟨_, hr, rfl⟩ := WP.spec_imp_exists (scalar_i64_remu_zero ops a b hb)
    rw [hr]
    simp only [WP.spec_ok]
    right
    refine ⟨trivial, ?_⟩
    rw [hb]
    exact Spec.integer_remu_zero_relation .I64 a.val
  · obtain ⟨_, hr, value, rfl, hv⟩ := WP.spec_imp_exists (scalar_i64_remu_nonzero ops a b hb)
    rw [hr]
    simp only [WP.spec_ok]
    left
    refine ⟨value, rfl, ?_⟩
    rw [hv]
    apply Spec.integer_remu_relation .I64 a.val b.val _ hb
    change a.val < 18446744073709551616
    scalar_tac

theorem scalar_i32_and_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 113#u16 a b = .ok (.Ok (UScalar.cast .U64 ((UScalar.cast .U32 a) &&& (UScalar.cast .U32 b)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (lift ((UScalar.cast .U32 a) &&& (UScalar.cast .U32 b))) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))) = _
  rw [lift, bind_ok, lift, bind_ok]

theorem scalar_i32_and_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 113#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        fun_binop_ .I32 (.mk_binop__0 .I32 .AND)
          (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val)) (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 b).val))
          (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i32_and_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  have hbound : ((UScalar.cast .U32 a).val &&& (UScalar.cast .U32 b).val) < 2 ^ sizenn (numtype_Inn .I32) := by
    rw [← UScalar.val_and]
    exact ((UScalar.cast .U32 a) &&& (UScalar.cast .U32 b)).hBounds
  have hr := Spec.integer_and_relation .I32 (UScalar.cast .U32 a).val (UScalar.cast .U32 b).val
  rw [SpecExt.Builtins.iand_value, Nat.mod_eq_of_lt hbound] at hr
  simpa only [numtype_Inn, U32.cast_U64_val_eq, UScalar.val_and] using hr

theorem scalar_i32_or_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 114#u16 a b = .ok (.Ok (UScalar.cast .U64 ((UScalar.cast .U32 a) ||| (UScalar.cast .U32 b)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (lift ((UScalar.cast .U32 a) ||| (UScalar.cast .U32 b))) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))) = _
  rw [lift, bind_ok, lift, bind_ok]

theorem scalar_i32_or_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 114#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        fun_binop_ .I32 (.mk_binop__0 .I32 .OR)
          (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val)) (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 b).val))
          (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i32_or_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  have hbound : ((UScalar.cast .U32 a).val ||| (UScalar.cast .U32 b).val) < 2 ^ sizenn (numtype_Inn .I32) := by
    rw [← UScalar.val_or]
    exact ((UScalar.cast .U32 a) ||| (UScalar.cast .U32 b)).hBounds
  have hr := Spec.integer_or_relation .I32 (UScalar.cast .U32 a).val (UScalar.cast .U32 b).val
  rw [SpecExt.Builtins.ior_value, Nat.mod_eq_of_lt hbound] at hr
  simpa only [numtype_Inn, U32.cast_U64_val_eq, UScalar.val_or] using hr

theorem scalar_i32_xor_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 115#u16 a b = .ok (.Ok (UScalar.cast .U64 ((UScalar.cast .U32 a) ^^^ (UScalar.cast .U32 b)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (lift ((UScalar.cast .U32 a) ^^^ (UScalar.cast .U32 b))) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))) = _
  rw [lift, bind_ok, lift, bind_ok]

theorem scalar_i32_xor_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 115#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        fun_binop_ .I32 (.mk_binop__0 .I32 .XOR)
          (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val)) (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 b).val))
          (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i32_xor_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  have hbound : ((UScalar.cast .U32 a).val ^^^ (UScalar.cast .U32 b).val) < 2 ^ sizenn (numtype_Inn .I32) := by
    rw [← UScalar.val_xor]
    exact ((UScalar.cast .U32 a) ^^^ (UScalar.cast .U32 b)).hBounds
  have hr := Spec.integer_xor_relation .I32 (UScalar.cast .U32 a).val (UScalar.cast .U32 b).val
  rw [SpecExt.Builtins.ixor_value, Nat.mod_eq_of_lt hbound] at hr
  simpa only [numtype_Inn, U32.cast_U64_val_eq, UScalar.val_xor] using hr

theorem scalar_i64_and_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 131#u16 a b = .ok (.Ok (a &&& b)) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (lift (a &&& b)) (fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) = _
  rw [lift, bind_ok]

theorem scalar_i64_and_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 131#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        fun_binop_ .I64 (.mk_binop__0 .I64 .AND)
          (.mk_num__0 .I64 (.mk_uN a.val)) (.mk_num__0 .I64 (.mk_uN b.val))
          (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i64_and_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  have hbound : (a.val &&& b.val) < 2 ^ sizenn (numtype_Inn .I64) := by
    rw [← UScalar.val_and]
    exact (a &&& b).hBounds
  have hr := Spec.integer_and_relation .I64 a.val b.val
  rw [SpecExt.Builtins.iand_value, Nat.mod_eq_of_lt hbound] at hr
  simpa only [numtype_Inn, UScalar.val_and] using hr

theorem scalar_i64_or_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 132#u16 a b = .ok (.Ok (a ||| b)) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (lift (a ||| b)) (fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) = _
  rw [lift, bind_ok]

theorem scalar_i64_or_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 132#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        fun_binop_ .I64 (.mk_binop__0 .I64 .OR)
          (.mk_num__0 .I64 (.mk_uN a.val)) (.mk_num__0 .I64 (.mk_uN b.val))
          (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i64_or_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  have hbound : (a.val ||| b.val) < 2 ^ sizenn (numtype_Inn .I64) := by
    rw [← UScalar.val_or]
    exact (a ||| b).hBounds
  have hr := Spec.integer_or_relation .I64 a.val b.val
  rw [SpecExt.Builtins.ior_value, Nat.mod_eq_of_lt hbound] at hr
  simpa only [numtype_Inn, UScalar.val_or] using hr

theorem scalar_i64_xor_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 133#u16 a b = .ok (.Ok (a ^^^ b)) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (lift (a ^^^ b)) (fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError)) = _
  rw [lift, bind_ok]

theorem scalar_i64_xor_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 133#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        fun_binop_ .I64 (.mk_binop__0 .I64 .XOR)
          (.mk_num__0 .I64 (.mk_uN a.val)) (.mk_num__0 .I64 (.mk_uN b.val))
          (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i64_xor_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  have hbound : (a.val ^^^ b.val) < 2 ^ sizenn (numtype_Inn .I64) := by
    rw [← UScalar.val_xor]
    exact (a ^^^ b).hBounds
  have hr := Spec.integer_xor_relation .I64 a.val b.val
  rw [SpecExt.Builtins.ixor_value, Nat.mod_eq_of_lt hbound] at hr
  simpa only [numtype_Inn, UScalar.val_xor] using hr

theorem scalar_i32_shl_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 116#u16 a b = .ok (.Ok (UScalar.cast .U64 (core.num.U32.wrapping_shl (UScalar.cast .U32 a) (UScalar.cast .U32 b)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (lift (core.num.U32.wrapping_shl (UScalar.cast .U32 a) (UScalar.cast .U32 b))) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))) = _
  rw [lift, bind_ok, lift, bind_ok]

@[step] theorem scalar_i32_shl {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 116#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val = ((UScalar.cast .U32 a).val * 2 ^ ((UScalar.cast .U32 b).val % 32)) % 2 ^ 32 ⦄ := by
  rw [scalar_i32_shl_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  rw [U32.cast_U64_val_eq]
  change (core.num.U32.wrapping_shl (UScalar.cast .U32 a) (UScalar.cast .U32 b)).bv.toNat = _
  rw [core.num.U32.wrapping_shl_bv_eq]
  simp [BitVec.shiftLeft, Nat.shiftLeft_eq]

theorem scalar_i32_shru_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 118#u16 a b = .ok (.Ok (UScalar.cast .U64 (core.num.U32.wrapping_shr (UScalar.cast .U32 a) (UScalar.cast .U32 b)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  change Aeneas.Std.bind (lift (core.num.U32.wrapping_shr (UScalar.cast .U32 a) (UScalar.cast .U32 b))) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value)) (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError))) = _
  rw [lift, bind_ok, lift, bind_ok]

@[step] theorem scalar_i32_shru {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 118#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val = (UScalar.cast .U32 a).val / 2 ^ ((UScalar.cast .U32 b).val % 32) ⦄ := by
  rw [scalar_i32_shru_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  rw [U32.cast_U64_val_eq]
  change (core.num.U32.wrapping_shr (UScalar.cast .U32 a) (UScalar.cast .U32 b)).bv.toNat = _
  rw [core.num.U32.wrapping_shr_bv_eq]
  simp [BitVec.ushiftRight, Nat.shiftRight_eq_div_pow]

theorem scalar_i64_shl_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 134#u16 a b = .ok (.Ok (core.num.U64.wrapping_shl a (UScalar.cast .U32 b))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change Aeneas.Std.bind (lift (UScalar.cast .U32 b)) (fun count => Aeneas.Std.bind (lift (core.num.U64.wrapping_shl a count)) (fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError))) = _
  rw [lift, bind_ok, lift, bind_ok]

@[step] theorem scalar_i64_shl {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 134#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val = (a.val * 2 ^ ((UScalar.cast .U32 b).val % 64)) % 2 ^ 64 ⦄ := by
  rw [scalar_i64_shl_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  change (core.num.U64.wrapping_shl a (UScalar.cast .U32 b)).bv.toNat = _
  rw [core.num.U64.wrapping_shl_bv_eq]
  simp [BitVec.shiftLeft, Nat.shiftLeft_eq]

theorem scalar_i64_shru_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 136#u16 a b = .ok (.Ok (core.num.U64.wrapping_shr a (UScalar.cast .U32 b))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change Aeneas.Std.bind (lift (UScalar.cast .U32 b)) (fun count => Aeneas.Std.bind (lift (core.num.U64.wrapping_shr a count)) (fun value => Result.ok (core.result.Result.Ok value : core.result.Result U64 runtime.ExecError))) = _
  rw [lift, bind_ok, lift, bind_ok]

@[step] theorem scalar_i64_shru {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 136#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧ value.val = a.val / 2 ^ ((UScalar.cast .U32 b).val % 64) ⦄ := by
  rw [scalar_i64_shru_eq]
  simp only [WP.spec_ok]
  refine ⟨_, rfl, ?_⟩
  change (core.num.U64.wrapping_shr a (UScalar.cast .U32 b)).bv.toNat = _
  rw [core.num.U64.wrapping_shr_bv_eq]
  simp [BitVec.ushiftRight, Nat.shiftRight_eq_div_pow]

theorem scalar_i32_shl_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 116#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        fun_binop_ .I32 (.mk_binop__0 .I32 .SHL)
          (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val)) (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 b).val))
          (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  obtain ⟨result, hr, value, he, hv⟩ := WP.spec_imp_exists (scalar_i32_shl ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, he, ?_⟩
  rw [hv]
  exact Spec.integer_shl_relation .I32 (UScalar.cast .U32 a).val (UScalar.cast .U32 b).val

theorem scalar_i32_shru_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 118#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        fun_binop_ .I32 (.mk_binop__0 .I32 (.SHR .U))
          (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val)) (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 b).val))
          (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  obtain ⟨result, hr, value, he, hv⟩ := WP.spec_imp_exists (scalar_i32_shru ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, he, ?_⟩
  rw [hv]
  exact Spec.integer_shru_relation .I32 (UScalar.cast .U32 a).val (UScalar.cast .U32 b).val (UScalar.cast .U32 a).hBounds

theorem scalar_i64_shl_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 134#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        fun_binop_ .I64 (.mk_binop__0 .I64 .SHL)
          (.mk_num__0 .I64 (.mk_uN a.val)) (.mk_num__0 .I64 (.mk_uN b.val))
          (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  obtain ⟨result, hr, value, he, hv⟩ := WP.spec_imp_exists (scalar_i64_shl ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, he, ?_⟩
  rw [hv]
  have hc : (UScalar.cast .U32 b).val % 64 = b.val % 64 := by
    simp only [UScalar.cast_val_eq]
    norm_num only [UScalar.size, UScalarTy.numBits]
    omega
  rw [hc]
  exact Spec.integer_shl_relation .I64 a.val b.val

theorem scalar_i64_shru_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 136#u16 a b ⦃ result =>
      ∃ value, result = .Ok value ∧
        fun_binop_ .I64 (.mk_binop__0 .I64 (.SHR .U))
          (.mk_num__0 .I64 (.mk_uN a.val)) (.mk_num__0 .I64 (.mk_uN b.val))
          (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  obtain ⟨result, hr, value, he, hv⟩ := WP.spec_imp_exists (scalar_i64_shru ops a b)
  rw [hr]
  simp only [WP.spec_ok]
  refine ⟨value, he, ?_⟩
  rw [hv]
  have hc : (UScalar.cast .U32 b).val % 64 = b.val % 64 := by
    simp only [UScalar.cast_val_eq]
    norm_num only [UScalar.size, UScalarTy.numBits]
    omega
  rw [hc]
  exact Spec.integer_shru_relation .I64 a.val b.val a.hBounds

end Itasca.Runtime.Interp

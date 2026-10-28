import Exec.Interp.Numeric.Integer.Int
import Exec.Spec.IntegerSigned

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem scalar_i32_divs_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 109#u16 a b =
      (let x := UScalar.cast .U32 a
       let y := UScalar.cast .U32 b
       if y = 0#u32 then Result.ok (core.result.Result.Err (runtime.ExecError.Trap .IntegerDivideByZero))
       else if x = 2147483648#u32 ∧ y = 4294967295#u32 then Result.ok (core.result.Result.Err (runtime.ExecError.Trap .IntegerOverflow))
       else Aeneas.Std.bind (UScalar.hcast .I32 x / UScalar.hcast .I32 y)
         (fun result => Result.ok (core.result.Result.Ok (UScalar.cast .U64 (IScalar.hcast .U32 result))))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change
    (if UScalar.cast .U32 b = 0#u32 then Result.ok (core.result.Result.Err (runtime.ExecError.Trap .IntegerDivideByZero))
     else if UScalar.cast .U32 a = 2147483648#u32 then
       if UScalar.cast .U32 b = core.num.U32.MAX then Result.ok (core.result.Result.Err (runtime.ExecError.Trap .IntegerOverflow))
       else Aeneas.Std.bind (Aeneas.Std.bind (lift (UScalar.hcast .I32 (UScalar.cast .U32 a))) (fun x =>
           Aeneas.Std.bind (lift (UScalar.hcast .I32 (UScalar.cast .U32 b))) (fun y =>
             Aeneas.Std.bind (x / y) (fun value => Result.ok (IScalar.hcast .U32 value))))) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value))
           (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))
     else Aeneas.Std.bind (Aeneas.Std.bind (lift (UScalar.hcast .I32 (UScalar.cast .U32 a))) (fun x =>
           Aeneas.Std.bind (lift (UScalar.hcast .I32 (UScalar.cast .U32 b))) (fun y =>
             Aeneas.Std.bind (x / y) (fun value => Result.ok (IScalar.hcast .U32 value))))) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value))
           (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) = _
  rw [show core.num.U32.MAX = 4294967295#u32 by decide +kernel]
  simp only [lift, bind_ok, Aeneas.Std.bind_assoc]
  by_cases zero : UScalar.cast .U32 b = 0#u32
  · simp only [zero, if_true]
  · by_cases left : UScalar.cast .U32 a = 2147483648#u32 <;>
      by_cases right : UScalar.cast .U32 b = 4294967295#u32 <;>
      simp_all only [if_true, if_false,
        and_true, and_false]

theorem hcast_i32_value_eq (x : U32) (y : I32) :
    (UScalar.hcast .I32 x).val = y.val ↔ x.bv = y.bv := by
  rw [← IScalar.eq_equiv]
  simp [IScalar.eq_equiv_bv_eq]

/-- The ordinary signed quotient branch cannot panic or overflow after its
explicit zero/minimum guards. -/
theorem scalar_i32_divs_success {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64)
    (nonzero : UScalar.cast .U32 b ≠ 0#u32)
    (noOverflow : ¬(UScalar.cast .U32 a = 2147483648#u32 ∧ UScalar.cast .U32 b = 4294967295#u32)) :
    runtime.interp.int.scalar ops 109#u16 a b ⦃ result => ∃ value,
      result = .Ok value ∧ fun_idiv_ 32 .S
        (.mk_uN (a.val % 4294967296)) (.mk_uN (b.val % 4294967296))
        (some (.mk_uN value.val)) ⦄ := by
  have signedNonzero : (UScalar.hcast .I32 (UScalar.cast .U32 b)).val ≠ 0 := by
    intro zero
    have bits := (hcast_i32_value_eq (UScalar.cast .U32 b) 0#i32).mp zero
    exact nonzero (UScalar.eq_equiv_bv_eq _ _ |>.mpr bits)
  have signedNoOverflow : ¬((UScalar.hcast .I32 (UScalar.cast .U32 a)).val = I32.min ∧
      (UScalar.hcast .I32 (UScalar.cast .U32 b)).val = -1) := by
    rintro ⟨left, right⟩
    apply noOverflow
    constructor
    · apply (UScalar.eq_equiv_bv_eq _ _).mpr
      exact (hcast_i32_value_eq (UScalar.cast .U32 a) (-2147483648)#i32).mp (by simpa [I32.min_eq] using left)
    · apply (UScalar.eq_equiv_bv_eq _ _).mpr
      exact (hcast_i32_value_eq (UScalar.cast .U32 b) (-1)#i32).mp (by simpa using right)
  rw [scalar_i32_divs_eq, if_neg nonzero, if_neg noOverflow]
  step with I32.div_spec signedNonzero signedNoOverflow as ⟨quotient, quotientEq⟩
  refine ⟨_, rfl, ?_⟩
  have sound := Spec.signed_div_relation 32 (UScalar.cast .U32 a).bv (UScalar.cast .U32 b).bv quotient.bv
    (by intro zero; exact nonzero (UScalar.eq_of_val_eq zero)) (by
      simpa only [IScalar.val, UScalar.hcast_bv_eq, IScalarTy.numBits, BitVec.setWidth_eq, UScalarTy.U32_numBits_eq] using quotientEq)
  have outBits : (IScalar.hcast .U32 quotient).bv = quotient.bv := by
    exact (IScalar.hcast_bv_eq .U32 quotient).trans (BitVec.signExtend_eq quotient.bv)
  have outValue : (UScalar.cast .U64 (IScalar.hcast .U32 quotient)).val = quotient.bv.toNat := by
    rw [U32.cast_U64_val_eq]
    change (IScalar.hcast .U32 quotient).bv.toNat = _
    rw [outBits]
  rw [outValue]
  simpa only [UScalar.bv_toNat, UScalar.cast_val_eq, UScalarTy.numBits, show (2:Nat)^32=4294967296 from rfl] using sound

theorem scalar_i64_divs_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 127#u16 a b =
      (if b = 0#u64 then Result.ok (core.result.Result.Err (runtime.ExecError.Trap .IntegerDivideByZero))
       else if a = 9223372036854775808#u64 ∧ b = 18446744073709551615#u64 then
         Result.ok (core.result.Result.Err (runtime.ExecError.Trap .IntegerOverflow))
       else Aeneas.Std.bind (UScalar.hcast .I64 a / UScalar.hcast .I64 b)
         (fun result => Result.ok (core.result.Result.Ok (IScalar.hcast .U64 result)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change
    (if b = 0#u64 then Result.ok (core.result.Result.Err (runtime.ExecError.Trap .IntegerDivideByZero))
     else if a = 9223372036854775808#u64 then
       if b = core.num.U64.MAX then Result.ok (core.result.Result.Err (runtime.ExecError.Trap .IntegerOverflow))
       else Aeneas.Std.bind (lift (UScalar.hcast .I64 a)) (fun x =>
         Aeneas.Std.bind (lift (UScalar.hcast .I64 b)) (fun y =>
           Aeneas.Std.bind (x / y) (fun value => Aeneas.Std.bind (lift (IScalar.hcast .U64 value))
             (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))))
     else Aeneas.Std.bind (lift (UScalar.hcast .I64 a)) (fun x =>
         Aeneas.Std.bind (lift (UScalar.hcast .I64 b)) (fun y =>
           Aeneas.Std.bind (x / y) (fun value => Aeneas.Std.bind (lift (IScalar.hcast .U64 value))
             (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))))) = _
  rw [show core.num.U64.MAX = 18446744073709551615#u64 by decide +kernel]
  simp only [lift, bind_ok]
  by_cases zero : b = 0#u64
  · simp only [zero, if_true]
  · by_cases left : a = 9223372036854775808#u64 <;>
      by_cases right : b = 18446744073709551615#u64 <;>
      simp_all only [if_true, if_false, and_true, and_false]

theorem hcast_i64_value_eq (x : U64) (y : I64) :
    (UScalar.hcast .I64 x).val = y.val ↔ x.bv = y.bv := by
  rw [← IScalar.eq_equiv]
  simp [IScalar.eq_equiv_bv_eq]

theorem scalar_i64_divs_success {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64)
    (nonzero : b ≠ 0#u64)
    (noOverflow : ¬(a = 9223372036854775808#u64 ∧ b = 18446744073709551615#u64)) :
    runtime.interp.int.scalar ops 127#u16 a b ⦃ result => ∃ value,
      result = .Ok value ∧ fun_idiv_ 64 .S (.mk_uN a.val) (.mk_uN b.val) (some (.mk_uN value.val)) ⦄ := by
  have signedNonzero : (UScalar.hcast .I64 b).val ≠ 0 := by
    intro zero
    have bits := (hcast_i64_value_eq b 0#i64).mp zero
    exact nonzero (UScalar.eq_equiv_bv_eq _ _ |>.mpr bits)
  have signedNoOverflow : ¬((UScalar.hcast .I64 a).val = I64.min ∧ (UScalar.hcast .I64 b).val = -1) := by
    rintro ⟨left, right⟩
    apply noOverflow
    constructor
    · apply (UScalar.eq_equiv_bv_eq _ _).mpr
      exact (hcast_i64_value_eq a (-9223372036854775808)#i64).mp (by simpa [I64.min_eq] using left)
    · apply (UScalar.eq_equiv_bv_eq _ _).mpr
      exact (hcast_i64_value_eq b (-1)#i64).mp (by simpa using right)
  rw [scalar_i64_divs_eq, if_neg nonzero, if_neg noOverflow]
  step with I64.div_spec signedNonzero signedNoOverflow as ⟨quotient, quotientEq⟩
  refine ⟨_, rfl, ?_⟩
  have sound := Spec.signed_div_relation 64 a.bv b.bv quotient.bv
    (by intro zero; exact nonzero (UScalar.eq_of_val_eq zero)) (by
      simpa only [IScalar.val, UScalar.hcast_bv_eq, IScalarTy.numBits, BitVec.setWidth_eq,
        UScalarTy.U64_numBits_eq] using quotientEq)
  have outBits : (IScalar.hcast .U64 quotient).bv = quotient.bv :=
    (IScalar.hcast_bv_eq .U64 quotient).trans (BitVec.signExtend_eq quotient.bv)
  change fun_idiv_ 64 .S (.mk_uN a.val) (.mk_uN b.val) (some (.mk_uN (IScalar.hcast .U64 quotient).bv.toNat))
  rw [outBits]
  exact sound
theorem scalar_i64_rems_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 129#u16 a b =
      (if b = 0#u64 then Result.ok (core.result.Result.Err (runtime.ExecError.Trap .IntegerDivideByZero))
       else if a = 9223372036854775808#u64 ∧ b = 18446744073709551615#u64 then
         Result.ok (core.result.Result.Ok 0#u64)
       else Aeneas.Std.bind (UScalar.hcast .I64 a % UScalar.hcast .I64 b)
         (fun result => Result.ok (core.result.Result.Ok (IScalar.hcast .U64 result)))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change
    (if b = 0#u64 then Result.ok (core.result.Result.Err (runtime.ExecError.Trap .IntegerDivideByZero))
     else if a = 9223372036854775808#u64 then
       if b = core.num.U64.MAX then Result.ok (core.result.Result.Ok 0#u64)
       else Aeneas.Std.bind (lift (UScalar.hcast .I64 a)) (fun x =>
         Aeneas.Std.bind (lift (UScalar.hcast .I64 b)) (fun y =>
           Aeneas.Std.bind (x % y) (fun value => Aeneas.Std.bind (lift (IScalar.hcast .U64 value))
             (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))))
     else Aeneas.Std.bind (lift (UScalar.hcast .I64 a)) (fun x =>
         Aeneas.Std.bind (lift (UScalar.hcast .I64 b)) (fun y =>
           Aeneas.Std.bind (x % y) (fun value => Aeneas.Std.bind (lift (IScalar.hcast .U64 value))
             (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))))) = _
  rw [show core.num.U64.MAX = 18446744073709551615#u64 by decide +kernel]
  simp only [lift, bind_ok]
  by_cases zero : b = 0#u64
  · simp only [zero, if_true]
  · by_cases left : a = 9223372036854775808#u64 <;>
      by_cases right : b = 18446744073709551615#u64 <;>
      simp_all only [if_true, if_false, and_true, and_false]
theorem scalar_i64_rems_nonoverflow {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64)
    (nonzero : b ≠ 0#u64)
    (noOverflow : ¬(a = 9223372036854775808#u64 ∧ b = 18446744073709551615#u64)) :
    runtime.interp.int.scalar ops 129#u16 a b ⦃ result => ∃ value,
      result = .Ok value ∧ fun_irem_ 64 .S (.mk_uN a.val) (.mk_uN b.val) (some (.mk_uN value.val)) ⦄ := by
  have signedNonzero : (UScalar.hcast .I64 b).val ≠ 0 := by
    intro zero
    have bits := (hcast_i64_value_eq b 0#i64).mp zero
    exact nonzero (UScalar.eq_equiv_bv_eq _ _ |>.mpr bits)
  rw [scalar_i64_rems_eq, if_neg nonzero, if_neg noOverflow]
  step with I64.rem_spec (UScalar.hcast .I64 a) signedNonzero as ⟨quotient, quotientEq⟩
  refine ⟨_, rfl, ?_⟩
  have sound := Spec.signed_rem_relation 64 a.bv b.bv quotient.bv
    (by intro zero; exact nonzero (UScalar.eq_of_val_eq zero)) (by
      simpa only [IScalar.val, UScalar.hcast_bv_eq, IScalarTy.numBits, BitVec.setWidth_eq,
        UScalarTy.U64_numBits_eq] using quotientEq)
  have outBits : (IScalar.hcast .U64 quotient).bv = quotient.bv :=
    (IScalar.hcast_bv_eq .U64 quotient).trans (BitVec.signExtend_eq quotient.bv)
  change fun_irem_ 64 .S (.mk_uN a.val) (.mk_uN b.val) (some (.mk_uN (IScalar.hcast .U64 quotient).bv.toNat))
  rw [outBits]
  exact sound
theorem scalar_i32_rems_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 111#u16 a b =
      (let x := UScalar.cast .U32 a
       let y := UScalar.cast .U32 b
       if y = 0#u32 then Result.ok (core.result.Result.Err (runtime.ExecError.Trap .IntegerDivideByZero))
       else if x = 2147483648#u32 ∧ y = 4294967295#u32 then Result.ok (core.result.Result.Ok 0#u64)
       else Aeneas.Std.bind (UScalar.hcast .I32 x % UScalar.hcast .I32 y)
         (fun result => Result.ok (core.result.Result.Ok (UScalar.cast .U64 (IScalar.hcast .U32 result))))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change
    (if UScalar.cast .U32 b = 0#u32 then Result.ok (core.result.Result.Err (runtime.ExecError.Trap .IntegerDivideByZero))
     else Aeneas.Std.bind
       (if UScalar.cast .U32 a = 2147483648#u32 then
         if UScalar.cast .U32 b = core.num.U32.MAX then Result.ok 0#u32 else (Aeneas.Std.bind (lift (UScalar.hcast .I32 (UScalar.cast .U32 a))) (fun x =>
           Aeneas.Std.bind (lift (UScalar.hcast .I32 (UScalar.cast .U32 b))) (fun y =>
             Aeneas.Std.bind (x % y) (fun value => Result.ok (IScalar.hcast .U32 value)))))
        else (Aeneas.Std.bind (lift (UScalar.hcast .I32 (UScalar.cast .U32 a))) (fun x =>
           Aeneas.Std.bind (lift (UScalar.hcast .I32 (UScalar.cast .U32 b))) (fun y =>
             Aeneas.Std.bind (x % y) (fun value => Result.ok (IScalar.hcast .U32 value))))))
       (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value))
         (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) = _
  rw [show core.num.U32.MAX = 4294967295#u32 by decide +kernel]
  simp only [lift, bind_ok, Aeneas.Std.bind_assoc]
  by_cases zero : UScalar.cast .U32 b = 0#u32
  · simp only [zero, if_true]
  · by_cases left : UScalar.cast .U32 a = 2147483648#u32 <;>
      by_cases right : UScalar.cast .U32 b = 4294967295#u32 <;>
      simp_all only [if_true, if_false, lift, bind_ok, Aeneas.Std.bind_assoc,
        and_true, and_false,
          show UScalar.cast .U64 0#u32 = 0#u64 from rfl]
theorem scalar_i32_rems_nonoverflow {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64)
    (nonzero : UScalar.cast .U32 b ≠ 0#u32)
    (noOverflow : ¬(UScalar.cast .U32 a = 2147483648#u32 ∧ UScalar.cast .U32 b = 4294967295#u32)) :
    runtime.interp.int.scalar ops 111#u16 a b ⦃ result => ∃ value,
      result = .Ok value ∧ fun_irem_ 32 .S
        (.mk_uN (a.val % 4294967296)) (.mk_uN (b.val % 4294967296))
        (some (.mk_uN value.val)) ⦄ := by
  have signedNonzero : (UScalar.hcast .I32 (UScalar.cast .U32 b)).val ≠ 0 := by
    intro zero
    have bits := (hcast_i32_value_eq (UScalar.cast .U32 b) 0#i32).mp zero
    exact nonzero (UScalar.eq_equiv_bv_eq _ _ |>.mpr bits)
  rw [scalar_i32_rems_eq, if_neg nonzero, if_neg noOverflow]
  step with I32.rem_spec (UScalar.hcast .I32 (UScalar.cast .U32 a)) signedNonzero as ⟨quotient, quotientEq⟩
  refine ⟨_, rfl, ?_⟩
  have sound := Spec.signed_rem_relation 32 (UScalar.cast .U32 a).bv (UScalar.cast .U32 b).bv quotient.bv
    (by intro zero; exact nonzero (UScalar.eq_of_val_eq zero)) (by
      simpa only [IScalar.val, UScalar.hcast_bv_eq, IScalarTy.numBits, BitVec.setWidth_eq, UScalarTy.U32_numBits_eq] using quotientEq)
  have outBits : (IScalar.hcast .U32 quotient).bv = quotient.bv := by
    exact (IScalar.hcast_bv_eq .U32 quotient).trans (BitVec.signExtend_eq quotient.bv)
  have outValue : (UScalar.cast .U64 (IScalar.hcast .U32 quotient)).val = quotient.bv.toNat := by
    rw [U32.cast_U64_val_eq]
    change (IScalar.hcast .U32 quotient).bv.toNat = _
    rw [outBits]
  rw [outValue]
  simpa only [UScalar.bv_toNat, UScalar.cast_val_eq, UScalarTy.numBits, show (2:Nat)^32=4294967296 from rfl] using sound

/-- Complete extracted signed division refinement, including both trap cases. -/
theorem scalar_i32_divs_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 109#u16 a b ⦃ result =>
      (∃ value, result = .Ok value ∧ fun_binop_ .I32 (.mk_binop__0 .I32 (.DIV .S))
        (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296))) (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296)))
        (some [.mk_num__0 .I32 (.mk_uN value.val)])) ∨
      (∃ trap, result = .Err (.Trap trap) ∧
        (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
        fun_binop_ .I32 (.mk_binop__0 .I32 (.DIV .S))
          (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296))) (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296))) (some [])) ⦄ := by
  by_cases zero : UScalar.cast .U32 b = 0#u32
  · rw [scalar_i32_divs_eq, if_pos zero]
    apply WP.spec.ret
    have bits : (b.val % 4294967296) = 0 := by simpa using congrArg UScalar.val zero
    refine Or.inr ⟨.IntegerDivideByZero, rfl, Or.inl rfl, ?_⟩
    rw [bits]
    exact Spec.integer_divs_zero_relation .I32 _
  · by_cases overflow : UScalar.cast .U32 a = 2147483648#u32 ∧ UScalar.cast .U32 b = 4294967295#u32
    · rw [scalar_i32_divs_eq, if_neg zero, if_pos overflow]
      apply WP.spec.ret
      have left : (a.val % 4294967296) = 2147483648 := by simpa using congrArg UScalar.val overflow.1
      have right : (b.val % 4294967296) = 4294967295 := by simpa using congrArg UScalar.val overflow.2
      refine Or.inr ⟨.IntegerOverflow, rfl, Or.inr rfl, ?_⟩
      rw [left, right]
      exact Spec.integer_divs_trap_relation .I32 _ _ Spec.signed_div_overflow32
    · apply WP.spec_mono (scalar_i32_divs_success ops a b zero overflow)
      rintro result ⟨value, same, relation⟩
      exact Or.inl ⟨value, same, Spec.integer_divs_result_relation .I32 _ _ _ relation⟩

/-- Complete extracted signed division refinement, including both trap cases. -/
theorem scalar_i64_divs_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 127#u16 a b ⦃ result =>
      (∃ value, result = .Ok value ∧ fun_binop_ .I64 (.mk_binop__0 .I64 (.DIV .S))
        (.mk_num__0 .I64 (.mk_uN a.val)) (.mk_num__0 .I64 (.mk_uN b.val))
        (some [.mk_num__0 .I64 (.mk_uN value.val)])) ∨
      (∃ trap, result = .Err (.Trap trap) ∧
        (trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow) ∧
        fun_binop_ .I64 (.mk_binop__0 .I64 (.DIV .S))
          (.mk_num__0 .I64 (.mk_uN a.val)) (.mk_num__0 .I64 (.mk_uN b.val)) (some [])) ⦄ := by
  by_cases zero : b = 0#u64
  · rw [scalar_i64_divs_eq, if_pos zero]
    apply WP.spec.ret
    have bits : b.val = 0 := by simpa using congrArg UScalar.val zero
    refine Or.inr ⟨.IntegerDivideByZero, rfl, Or.inl rfl, ?_⟩
    rw [bits]
    exact Spec.integer_divs_zero_relation .I64 _
  · by_cases overflow : a = 9223372036854775808#u64 ∧ b = 18446744073709551615#u64
    · rw [scalar_i64_divs_eq, if_neg zero, if_pos overflow]
      apply WP.spec.ret
      have left : a.val = 9223372036854775808 := by simpa using congrArg UScalar.val overflow.1
      have right : b.val = 18446744073709551615 := by simpa using congrArg UScalar.val overflow.2
      refine Or.inr ⟨.IntegerOverflow, rfl, Or.inr rfl, ?_⟩
      rw [left, right]
      exact Spec.integer_divs_trap_relation .I64 _ _ Spec.signed_div_overflow64
    · apply WP.spec_mono (scalar_i64_divs_success ops a b zero overflow)
      rintro result ⟨value, same, relation⟩
      exact Or.inl ⟨value, same, Spec.integer_divs_result_relation .I64 _ _ _ relation⟩

/-- Complete signed remainder refinement; minimum modulo minus one returns zero. -/
theorem scalar_i32_rems_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 111#u16 a b ⦃ result =>
      (∃ value, result = .Ok value ∧ fun_binop_ .I32 (.mk_binop__0 .I32 (.REM .S))
        (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296))) (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296)))
        (some [.mk_num__0 .I32 (.mk_uN value.val)])) ∨
      (result = .Err (.Trap .IntegerDivideByZero) ∧
        fun_binop_ .I32 (.mk_binop__0 .I32 (.REM .S))
          (.mk_num__0 .I32 (.mk_uN (a.val % 4294967296))) (.mk_num__0 .I32 (.mk_uN (b.val % 4294967296))) (some [])) ⦄ := by
  by_cases zero : UScalar.cast .U32 b = 0#u32
  · rw [scalar_i32_rems_eq, if_pos zero]
    apply WP.spec.ret
    have bits : (b.val % 4294967296) = 0 := by simpa using congrArg UScalar.val zero
    refine Or.inr ⟨rfl, ?_⟩
    rw [bits]
    exact Spec.integer_rems_zero_relation .I32 _
  · by_cases overflow : UScalar.cast .U32 a = 2147483648#u32 ∧ UScalar.cast .U32 b = 4294967295#u32
    · rw [scalar_i32_rems_eq, if_neg zero, if_pos overflow]
      apply WP.spec.ret
      have left : (a.val % 4294967296) = 2147483648 := by simpa using congrArg UScalar.val overflow.1
      have right : (b.val % 4294967296) = 4294967295 := by simpa using congrArg UScalar.val overflow.2
      refine Or.inl ⟨0#u64, rfl, ?_⟩
      rw [left, right]
      exact Spec.integer_rems_result_relation .I32 _ _ _ Spec.signed_rem_overflow32
    · apply WP.spec_mono (scalar_i32_rems_nonoverflow ops a b zero overflow)
      rintro result ⟨value, same, relation⟩
      exact Or.inl ⟨value, same, Spec.integer_rems_result_relation .I32 _ _ _ relation⟩

/-- Complete signed remainder refinement; minimum modulo minus one returns zero. -/
theorem scalar_i64_rems_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 129#u16 a b ⦃ result =>
      (∃ value, result = .Ok value ∧ fun_binop_ .I64 (.mk_binop__0 .I64 (.REM .S))
        (.mk_num__0 .I64 (.mk_uN a.val)) (.mk_num__0 .I64 (.mk_uN b.val))
        (some [.mk_num__0 .I64 (.mk_uN value.val)])) ∨
      (result = .Err (.Trap .IntegerDivideByZero) ∧
        fun_binop_ .I64 (.mk_binop__0 .I64 (.REM .S))
          (.mk_num__0 .I64 (.mk_uN a.val)) (.mk_num__0 .I64 (.mk_uN b.val)) (some [])) ⦄ := by
  by_cases zero : b = 0#u64
  · rw [scalar_i64_rems_eq, if_pos zero]
    apply WP.spec.ret
    have bits : b.val = 0 := by simpa using congrArg UScalar.val zero
    refine Or.inr ⟨rfl, ?_⟩
    rw [bits]
    exact Spec.integer_rems_zero_relation .I64 _
  · by_cases overflow : a = 9223372036854775808#u64 ∧ b = 18446744073709551615#u64
    · rw [scalar_i64_rems_eq, if_neg zero, if_pos overflow]
      apply WP.spec.ret
      have left : a.val = 9223372036854775808 := by simpa using congrArg UScalar.val overflow.1
      have right : b.val = 18446744073709551615 := by simpa using congrArg UScalar.val overflow.2
      refine Or.inl ⟨0#u64, rfl, ?_⟩
      rw [left, right]
      exact Spec.integer_rems_result_relation .I64 _ _ _ Spec.signed_rem_overflow64
    · apply WP.spec_mono (scalar_i64_rems_nonoverflow ops a b zero overflow)
      rintro result ⟨value, same, relation⟩
      exact Or.inl ⟨value, same, Spec.integer_rems_result_relation .I64 _ _ _ relation⟩

end Itasca.Runtime.Interp

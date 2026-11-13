import Itasca.Runtime.Equations
import Itasca.Generated.Types
import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.Interp.Numeric.Integer.Int
import Itasca.Runtime.Spec.SegmentInitCases
import SpecExt.Builtins.Examples

/-!
Sections, each formerly its own module: Interrupt, NumericCodePoint, IntSigned, IntShift, IntRotate, IntCounts.
-/

/-! ## Interrupt -/

section

/-! Interrupt polling has no store access. A terminated execution at this
boundary is exactly a terminating hook decision, not an internal escape hatch. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def interruptResult : runtime.platform.InterruptAction → core.result.Result Unit runtime.ExecError
  | .Continue => .Ok ()
  | .Terminate => .Err .Terminated

theorem interrupt_eq {M P : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (platform after : P)
    (decision : runtime.platform.InterruptAction)
    (h : hooks.interrupt platform = .ok (decision, after)) :
    runtime.interp.interrupt memory hooks platform = .ok (interruptResult decision, after) := by
  simp only [runtime.interp.interrupt, h, bind_ok]
  cases decision <;> rfl

end Itasca.Runtime.Interp

end

/-! ## NumericCodePoint -/

section

namespace Itasca.Runtime.Interp
open Aeneas.Std SourceMachine.Numeric

theorem linear_emission_numeric_inv {locals before after : List valtype} {emitted : List Compiler.Bytecode}
    (op : Instruction) (h : Compiler.LinearEmission locals before op.source emitted after) :
    ∃ stack a b,
      before = stack ++ List.replicate op.arity (Compiler.integerType op.input) ∧
      emitted = [Compiler.integerInstruction op a a b] ∧
      after = stack ++ [Compiler.integerType op.output] ∧
      a.val = Compiler.slots locals + Compiler.slots stack ∧ b.val = a.val + (op.arity - 1) := by
  generalize sourceEq : op.source = instruction at h
  have decoded := congrArg decodeInstruction sourceEq
  rw [decode_instruction_source] at decoded
  cases h with
  | numeric stack other a b ha hb =>
    rw [decode_instruction_source] at decoded
    cases Option.some.inj decoded
    exact ⟨stack, a, b, rfl, rfl, rfl, ha, hb⟩
  | binary stack ty binary a b ha hb =>
    cases ty <;> cases binary <;>
      simp only [Compiler.IntegerBinary.source, numtype_Inn, decodeInstruction, Option.some.injEq] at decoded <;>
      subst op
    all_goals exact ⟨stack, a, b, rfl, rfl, rfl, ha, hb⟩
  | eqz32 stack a ha =>
    simp only [decodeInstruction, Option.some.injEq] at decoded
    subst op
    exact ⟨stack, a, a, rfl, rfl, rfl, ha, by simp [Instruction.arity]⟩
  | eqz64 stack a ha =>
    simp only [decodeInstruction, Option.some.injEq] at decoded
    subst op
    exact ⟨stack, a, a, rfl, rfl, rfl, ha, by simp [Instruction.arity]⟩
  | _ => simp [decodeInstruction] at decoded

theorem integer_value_type (ty : Inn) (bits : Nat) :
    Compiler.valueType (SourceMachine.integerVal ty bits) = Compiler.integerType ty := by cases ty <;> rfl

theorem numeric_operand_types (op : Instruction)
    (a b : BitVec (sizenn (numtype_Inn op.input))) :
    (op.operands a b).map Compiler.valueType = List.replicate op.arity (Compiler.integerType op.input) := by
  rcases op.arity_cases with one | two
  · simp [Instruction.operands, one, integer_value_type]
  · simp [Instruction.operands, two, integer_value_type]

end Itasca.Runtime.Interp

end

/-! ## IntSigned -/

section

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

end

/-! ## IntShift -/

section

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

end

/-! ## IntRotate -/

section

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

end

/-! ## IntCounts -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
open SpecExt.Builtins

theorem count_bits_population (width value : Nat) :
    Primitive.countBits width value = population (integerBits width value) := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih =>
    rw [integerBits_lsb, population_append]
    simp [Primitive.countBits, population, ih, Nat.add_comm]

theorem trailing_zeros_bits (width value : Nat) :
    Primitive.trailingZeros width value = leadingZeros (integerBits width value).reverse := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih =>
    rw [integerBits_lsb, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    by_cases low : value % 2 = 0
    · simp [Primitive.trailingZeros, low, leadingZeros, ih]
    · have one : value % 2 = 1 := by have := Nat.mod_lt value (by decide : 0 < 2); omega
      simp [Primitive.trailingZeros, one, leadingZeros]

theorem leading_zeros_bitvec (width : Nat) (bits : BitVec width) :
    Aeneas.Std.BitVec.leadingZeros bits = leadingZeros (integerBits width bits.toNat) := by
  rw [leadingZeros_bits width bits.toNat bits.isLt]
  have zero : bits = 0 ↔ bits.toNat = 0 := by
    constructor
    · intro h; subst bits; rfl
    · intro h; apply BitVec.eq_of_toNat_eq; simpa using h
  simp only [Aeneas.Std.BitVec.leadingZeros, zero]

theorem leading_zeros_le_length (bits : List bit) : leadingZeros bits ≤ bits.length := by
  induction bits with
  | nil => simp [leadingZeros]
  | cons value rest ih =>
    cases value with
    | mk_bit value => cases value <;> simp [leadingZeros] <;> omega

theorem leading_zeros_bitvec_le (width : Nat) (bits : BitVec width) :
    Aeneas.Std.BitVec.leadingZeros bits ≤ width := by
  rw [leading_zeros_bitvec]
  simpa only [integerBits_length] using leading_zeros_le_length (integerBits width bits.toNat)


theorem scalar_i32_clz_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 103#u16 a b = .ok (.Ok (UScalar.cast .U64 (⟨BitVec.ofNat 32 (Aeneas.Std.BitVec.leadingZeros (UScalar.cast .U32 a).bv)⟩ : U32))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change
    (Aeneas.Std.bind (lift (core.num.U32.leading_zeros (UScalar.cast .U32 a))) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value))
      (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) = _
  simp only [core.num.U32.leading_zeros, lift, bind_ok]
  rfl


theorem scalar_i32_ctz_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 104#u16 a b = .ok (.Ok (UScalar.cast .U64 (⟨BitVec.ofNat 32 (Primitive.trailingZeros 32 (UScalar.cast .U32 a).val)⟩ : U32))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change
    (Aeneas.Std.bind (core.num.U32.trailing_zeros (UScalar.cast .U32 a)) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value))
      (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) = _
  simp only [core.num.U32.trailing_zeros, lift, bind_ok]


theorem scalar_i32_popcnt_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 105#u16 a b = .ok (.Ok (UScalar.cast .U64 (⟨BitVec.ofNat 32 (Primitive.countBits 32 (UScalar.cast .U32 a).val)⟩ : U32))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change
    (Aeneas.Std.bind (core.num.U32.count_ones (UScalar.cast .U32 a)) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value))
      (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) = _
  simp only [core.num.U32.count_ones, lift, bind_ok]


theorem scalar_i64_clz_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 121#u16 a b = .ok (.Ok (UScalar.cast .U64 (⟨BitVec.ofNat 32 (Aeneas.Std.BitVec.leadingZeros a.bv)⟩ : U32))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change
    (Aeneas.Std.bind (lift (core.num.U64.leading_zeros a)) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value))
      (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) = _
  simp only [core.num.U64.leading_zeros, lift, bind_ok]
  rfl


theorem scalar_i64_ctz_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 122#u16 a b = .ok (.Ok (UScalar.cast .U64 (⟨BitVec.ofNat 32 (Primitive.trailingZeros 64 a.val)⟩ : U32))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change
    (Aeneas.Std.bind (core.num.U64.trailing_zeros a) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value))
      (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) = _
  simp only [core.num.U64.trailing_zeros, lift, bind_ok]


theorem scalar_i64_popcnt_eq {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 123#u16 a b = .ok (.Ok (UScalar.cast .U64 (⟨BitVec.ofNat 32 (Primitive.countBits 64 a.val)⟩ : U32))) := by
  unfold runtime.interp.int.scalar
  rw [lift, bind_ok, lift, bind_ok]
  with_unfolding_all change
    (Aeneas.Std.bind (core.num.U64.count_ones a) (fun value => Aeneas.Std.bind (lift (UScalar.cast .U64 value))
      (fun result => Result.ok (core.result.Result.Ok result : core.result.Result U64 runtime.ExecError)))) = _
  simp only [core.num.U64.count_ones, lift, bind_ok]


theorem scalar_i32_clz_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 103#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_unop_ .I32 (.mk_unop__0 .I32 .CLZ)
        (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val))
        (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i32_clz_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  rw [U32.cast_U64_val_eq]
  have bound := leading_zeros_bitvec_le 32 (UScalar.cast .U32 a).bv
  have exactValue : (⟨BitVec.ofNat 32 (Aeneas.Std.BitVec.leadingZeros (UScalar.cast .U32 a).bv)⟩ : U32).val = Aeneas.Std.BitVec.leadingZeros (UScalar.cast .U32 a).bv := by
    change (Aeneas.Std.BitVec.leadingZeros (UScalar.cast .U32 a).bv) % 2^32 = _
    apply Nat.mod_eq_of_lt
    omega
  rw [exactValue]
  have same : iclz_ 32 (.mk_uN (UScalar.cast .U32 a).val) = .mk_uN (Aeneas.Std.BitVec.leadingZeros (UScalar.cast .U32 a).bv) := by
    exact congrArg uN.mk_uN (leading_zeros_bitvec _ _).symm
  have wf := Spec.unsigned_num_wf .I32 (Aeneas.Std.BitVec.leadingZeros (UScalar.cast .U32 a).bv) (by change (Aeneas.Std.BitVec.leadingZeros (UScalar.cast .U32 a).bv) < 2^32; omega)
  rw [← same] at wf ⊢
  exact .fun_unop__case_0 _ wf


theorem scalar_i32_ctz_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 104#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_unop_ .I32 (.mk_unop__0 .I32 .CTZ)
        (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val))
        (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i32_ctz_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  rw [U32.cast_U64_val_eq]
  have bound := Primitive.trailingZeros_le 32 (UScalar.cast .U32 a).val
  have exactValue : (⟨BitVec.ofNat 32 (Primitive.trailingZeros 32 (UScalar.cast .U32 a).val)⟩ : U32).val = Primitive.trailingZeros 32 (UScalar.cast .U32 a).val := by
    change (Primitive.trailingZeros 32 (UScalar.cast .U32 a).val) % 2^32 = _
    apply Nat.mod_eq_of_lt
    omega
  rw [exactValue]
  have same : ictz_ 32 (.mk_uN (UScalar.cast .U32 a).val) = .mk_uN (Primitive.trailingZeros 32 (UScalar.cast .U32 a).val) := by
    simp only [ictz_, ibits_, proj_uN_0, ← trailing_zeros_bits]
  have wf := Spec.unsigned_num_wf .I32 (Primitive.trailingZeros 32 (UScalar.cast .U32 a).val) (by change (Primitive.trailingZeros 32 (UScalar.cast .U32 a).val) < 2^32; omega)
  rw [← same] at wf ⊢
  exact .fun_unop__case_2 _ wf


theorem scalar_i32_popcnt_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 105#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_unop_ .I32 (.mk_unop__0 .I32 .POPCNT)
        (.mk_num__0 .I32 (.mk_uN (UScalar.cast .U32 a).val))
        (some [.mk_num__0 .I32 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i32_popcnt_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  rw [U32.cast_U64_val_eq]
  have bound := Primitive.countBits_le 32 (UScalar.cast .U32 a).val
  have exactValue : (⟨BitVec.ofNat 32 (Primitive.countBits 32 (UScalar.cast .U32 a).val)⟩ : U32).val = Primitive.countBits 32 (UScalar.cast .U32 a).val := by
    change (Primitive.countBits 32 (UScalar.cast .U32 a).val) % 2^32 = _
    apply Nat.mod_eq_of_lt
    omega
  rw [exactValue]
  have same : ipopcnt_ 32 (.mk_uN (UScalar.cast .U32 a).val) = .mk_uN (Primitive.countBits 32 (UScalar.cast .U32 a).val) := by
    simp only [ipopcnt_, ibits_, proj_uN_0, ← count_bits_population]
  have wf := Spec.unsigned_num_wf .I32 (Primitive.countBits 32 (UScalar.cast .U32 a).val) (by change (Primitive.countBits 32 (UScalar.cast .U32 a).val) < 2^32; omega)
  rw [← same] at wf ⊢
  exact .fun_unop__case_4 _ wf


theorem scalar_i64_clz_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 121#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_unop_ .I64 (.mk_unop__0 .I64 .CLZ)
        (.mk_num__0 .I64 (.mk_uN a.val))
        (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i64_clz_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  rw [U32.cast_U64_val_eq]
  have bound := leading_zeros_bitvec_le 64 a.bv
  have exactValue : (⟨BitVec.ofNat 32 (Aeneas.Std.BitVec.leadingZeros a.bv)⟩ : U32).val = Aeneas.Std.BitVec.leadingZeros a.bv := by
    change (Aeneas.Std.BitVec.leadingZeros a.bv) % 2^32 = _
    apply Nat.mod_eq_of_lt
    omega
  rw [exactValue]
  have same : iclz_ 64 (.mk_uN a.val) = .mk_uN (Aeneas.Std.BitVec.leadingZeros a.bv) := by
    exact congrArg uN.mk_uN (leading_zeros_bitvec _ _).symm
  have wf := Spec.unsigned_num_wf .I64 (Aeneas.Std.BitVec.leadingZeros a.bv) (by change (Aeneas.Std.BitVec.leadingZeros a.bv) < 2^64; omega)
  rw [← same] at wf ⊢
  exact .fun_unop__case_1 _ wf


theorem scalar_i64_ctz_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 122#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_unop_ .I64 (.mk_unop__0 .I64 .CTZ)
        (.mk_num__0 .I64 (.mk_uN a.val))
        (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i64_ctz_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  rw [U32.cast_U64_val_eq]
  have bound := Primitive.trailingZeros_le 64 a.val
  have exactValue : (⟨BitVec.ofNat 32 (Primitive.trailingZeros 64 a.val)⟩ : U32).val = Primitive.trailingZeros 64 a.val := by
    change (Primitive.trailingZeros 64 a.val) % 2^32 = _
    apply Nat.mod_eq_of_lt
    omega
  rw [exactValue]
  have same : ictz_ 64 (.mk_uN a.val) = .mk_uN (Primitive.trailingZeros 64 a.val) := by
    simp only [ictz_, ibits_, proj_uN_0, ← trailing_zeros_bits]
  have wf := Spec.unsigned_num_wf .I64 (Primitive.trailingZeros 64 a.val) (by change (Primitive.trailingZeros 64 a.val) < 2^64; omega)
  rw [← same] at wf ⊢
  exact .fun_unop__case_3 _ wf


theorem scalar_i64_popcnt_sound {F : Type} (ops : runtime.platform.FloatOps F) (a b : U64) :
    runtime.interp.int.scalar ops 123#u16 a b ⦃ result => ∃ value, result = .Ok value ∧
      fun_unop_ .I64 (.mk_unop__0 .I64 .POPCNT)
        (.mk_num__0 .I64 (.mk_uN a.val))
        (some [.mk_num__0 .I64 (.mk_uN value.val)]) ⦄ := by
  rw [scalar_i64_popcnt_eq]
  apply WP.spec.ret
  refine ⟨_, rfl, ?_⟩
  rw [U32.cast_U64_val_eq]
  have bound := Primitive.countBits_le 64 a.val
  have exactValue : (⟨BitVec.ofNat 32 (Primitive.countBits 64 a.val)⟩ : U32).val = Primitive.countBits 64 a.val := by
    change (Primitive.countBits 64 a.val) % 2^32 = _
    apply Nat.mod_eq_of_lt
    omega
  rw [exactValue]
  have same : ipopcnt_ 64 (.mk_uN a.val) = .mk_uN (Primitive.countBits 64 a.val) := by
    simp only [ipopcnt_, ibits_, proj_uN_0, ← count_bits_population]
  have wf := Spec.unsigned_num_wf .I64 (Primitive.countBits 64 a.val) (by change (Primitive.countBits 64 a.val) < 2^64; omega)
  rw [← same] at wf ⊢
  exact .fun_unop__case_5 _ wf

end Itasca.Runtime.Interp

end

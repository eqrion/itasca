import Exec.Interp.Numeric.Integer.IntegerUnary
import Exec.Interp.Numeric.Integer.IntegerCompare
import Exec.Interp.Numeric.Integer.IntegerConversion
import Exec.Interp.Relations.ScalarDispatch
import Exec.Abs.Numeric.Instruction
import Exec.Code.Local.Lowering.Common.NumericOpcode

namespace Exec.Interp
open Aeneas Aeneas.Std Abs.Numeric

theorem integerOpcode_agrees (op : Instruction) : Code.integerOpcode op =
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
    runtime.interp.int.scalar floats (Code.integerOpcode op) a b ⦃ IntegerExact op a b ⦄ := by
  rw [integerOpcode_agrees]
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
    change value.val = (BitVec.ofNat 32 (Abs.Numeric.compare ty op (integerWord ty a) (integerWord ty b))).toNat
    have bound : Abs.Numeric.compare ty op (integerWord ty a) (integerWord ty b) < 2^32 := compare_bound ty op (integerWord ty a) (integerWord ty b)
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
    runtime.interp.execute_scalar floats exec base (Code.integerOpcode op) dst left right ⦃ out =>
      ∃ numeric, IntegerExact op exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]! numeric ∧
        ScalarEffect exec (base.val + dst.val) numeric out ⦄ := by
  obtain ⟨numeric, equation, exactResult⟩ := WP.spec_imp_exists
    (scalar_integer_exact floats op exec.slots.val[base.val + left.val]! exec.slots.val[base.val + right.val]!)
  apply WP.spec_mono (execute_scalar_effect floats exec base (Code.integerOpcode op) dst left right hl hr hd numeric equation)
  exact fun _ effect => ⟨numeric, exactResult, effect⟩
end Exec.Interp

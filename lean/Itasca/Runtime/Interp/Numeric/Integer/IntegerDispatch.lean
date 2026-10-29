import Itasca.Runtime.Interp.Numeric.Integer.IntegerBinary
import Itasca.Runtime.Interp.Numeric.Integer.IntCompareSigned
import Itasca.Runtime.SourceMachine.Numeric.Instruction
import Itasca.Runtime.Interp.Numeric.Integer.IntExtend
import Itasca.Runtime.Interp.Numeric.Integer.IntCounts
import Itasca.Runtime.Interp.Relations.ScalarDispatch
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericOpcode

/-!
Scalar integer instruction dispatch. Comparison, conversion and unary opcode facts join the separately proved binary arithmetic facts in one exact instruction-effect argument.
-/

/-! ## Integer Compare -/

section

namespace Itasca.Runtime.Interp
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
end Itasca.Runtime.Interp

end

/-! ## Integer Conversion -/

section

namespace Itasca.Runtime.Interp
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
end Itasca.Runtime.Interp

end

/-! ## Integer Unary -/

section

namespace Itasca.Runtime.Interp
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
end Itasca.Runtime.Interp

end

/-! ## Integer Dispatch -/

section

namespace Itasca.Runtime.Interp
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
end Itasca.Runtime.Interp

end

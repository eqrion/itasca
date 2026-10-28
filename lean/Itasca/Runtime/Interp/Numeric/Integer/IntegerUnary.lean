import Itasca.Runtime.Interp.Numeric.Integer.IntegerBinary
import Itasca.Runtime.Interp.Numeric.Integer.IntCounts
import Itasca.Runtime.Interp.Numeric.Integer.IntExtend
import Itasca.Runtime.Abs.Numeric.UnaryOperators

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std Abs.Numeric

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
      simp only [integerWord32_toNat, integerWord64_toNat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | ctz =>
      apply WP.spec_mono (scalar_i32_ctz_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integerWord32_toNat, integerWord64_toNat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | popcnt =>
      apply WP.spec_mono (scalar_i32_popcnt_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integerWord32_toNat, integerWord64_toNat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | extend8 =>
      apply WP.spec_mono (scalar_i32_extend8_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integerWord32_toNat, integerWord64_toNat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | extend16 =>
      apply WP.spec_mono (scalar_i32_extend16_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integerWord32_toNat, integerWord64_toNat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
  | I64 =>
    cases op with
    | clz =>
      apply WP.spec_mono (scalar_i64_clz_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integerWord32_toNat, integerWord64_toNat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | ctz =>
      apply WP.spec_mono (scalar_i64_ctz_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integerWord32_toNat, integerWord64_toNat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | popcnt =>
      apply WP.spec_mono (scalar_i64_popcnt_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integerWord32_toNat, integerWord64_toNat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | extend8 =>
      apply WP.spec_mono (scalar_i64_extend8_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integerWord32_toNat, integerWord64_toNat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | extend16 =>
      apply WP.spec_mono (scalar_i64_extend16_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integerWord32_toNat, integerWord64_toNat]
      simpa only [UnaryOperator.operation, numtype_Inn, UScalar.cast_val_eq, UScalarTy.numBits,
        show (2:Nat)^32=4294967296 from rfl] using relation
    | extend32 =>
      apply WP.spec_mono (scalar_i64_extend32_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integerWord32_toNat, integerWord64_toNat]
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

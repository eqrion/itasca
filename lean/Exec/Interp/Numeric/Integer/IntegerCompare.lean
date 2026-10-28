import Exec.Interp.Numeric.Integer.IntegerBinary
import Exec.Interp.Numeric.Integer.IntCompareSigned
import Exec.Abs.Numeric.Compare

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
      simp only [integerWord32_toNat, integerWord64_toNat]
      simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | NE =>
      apply WP.spec_mono (scalar_i32_ne_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integerWord32_toNat, integerWord64_toNat]
      simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | LT sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i32_lts_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integerWord32_toNat, integerWord64_toNat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
      | U =>
        apply WP.spec_mono (scalar_i32_ltu_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integerWord32_toNat, integerWord64_toNat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | GT sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i32_gts_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integerWord32_toNat, integerWord64_toNat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
      | U =>
        apply WP.spec_mono (scalar_i32_gtu_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integerWord32_toNat, integerWord64_toNat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | LE sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i32_les_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integerWord32_toNat, integerWord64_toNat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
      | U =>
        apply WP.spec_mono (scalar_i32_leu_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integerWord32_toNat, integerWord64_toNat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | GE sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i32_ges_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integerWord32_toNat, integerWord64_toNat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
      | U =>
        apply WP.spec_mono (scalar_i32_geu_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integerWord32_toNat, integerWord64_toNat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
  | I64 =>
    cases op with
    | EQ =>
      apply WP.spec_mono (scalar_i64_eq_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integerWord32_toNat, integerWord64_toNat]
      simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | NE =>
      apply WP.spec_mono (scalar_i64_ne_sound floats a b)
      rintro status ⟨value, rfl, relation⟩
      refine ⟨value, rfl, ?_⟩
      simp only [integerWord32_toNat, integerWord64_toNat]
      simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | LT sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i64_lts_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integerWord32_toNat, integerWord64_toNat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
      | U =>
        apply WP.spec_mono (scalar_i64_ltu_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integerWord32_toNat, integerWord64_toNat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | GT sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i64_gts_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integerWord32_toNat, integerWord64_toNat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
      | U =>
        apply WP.spec_mono (scalar_i64_gtu_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integerWord32_toNat, integerWord64_toNat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | LE sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i64_les_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integerWord32_toNat, integerWord64_toNat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
      | U =>
        apply WP.spec_mono (scalar_i64_leu_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integerWord32_toNat, integerWord64_toNat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
    | GE sign =>
      cases sign with
      | S =>
        apply WP.spec_mono (scalar_i64_ges_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integerWord32_toNat, integerWord64_toNat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation
      | U =>
        apply WP.spec_mono (scalar_i64_geu_sound floats a b)
        rintro status ⟨value, rfl, relation⟩
        refine ⟨value, rfl, ?_⟩
        simp only [integerWord32_toNat, integerWord64_toNat]
        simpa only [UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn, show (2:Nat)^32=4294967296 from rfl] using relation

theorem scalar_compare_exact {F : Type} (floats : runtime.platform.FloatOps F)
    (ty : Inn) (op : relop_Inn) (a b : U64) :
    runtime.interp.int.scalar floats (compareOpcode ty op) a b ⦃ status => ∃ value, status = .Ok value ∧
      value.val = Abs.Numeric.compare ty op (integerWord ty a) (integerWord ty b) ⦄ := by
  apply WP.spec_mono (scalar_compare_sound floats ty op a b)
  rintro status ⟨value, rfl, relation⟩
  refine ⟨value, rfl, ?_⟩
  have same := Spec.integer_relop_deterministic relation (Abs.Numeric.compare_relation ty op (integerWord ty a) (integerWord ty b))
  simpa only [num_.mk_num__0.injEq, uN.mk_uN.injEq, true_and] using same
end Itasca.Runtime.Interp

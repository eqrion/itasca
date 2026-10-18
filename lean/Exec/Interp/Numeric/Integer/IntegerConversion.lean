import Exec.Interp.Numeric.Integer.IntegerBinary
import Exec.Interp.Numeric.Integer.IntExtend
import Exec.Abs.Numeric.Conversion

namespace Exec.Interp
open Aeneas Aeneas.Std Abs.Numeric

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
    simp only [Conversion.input, integerWord64_toNat]
    exact relation
  | extendUnsigned =>
    apply WP.spec_mono (scalar_extendu_sound floats a b)
    rintro status ⟨value, rfl, relation⟩
    refine ⟨value, rfl, ?_⟩
    simp only [Conversion.input, integerWord32_toNat]
    simpa only [Conversion.output, Conversion.operator, UScalar.cast_val_eq, UScalarTy.numBits, numtype_Inn,
      show (2:Nat)^32=4294967296 from rfl] using relation
  | extendSigned =>
    apply WP.spec_mono (scalar_extends_sound floats a b)
    rintro status ⟨value, rfl, relation⟩
    refine ⟨value, rfl, ?_⟩
    simp only [Conversion.input, integerWord32_toNat]
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
  · simpa only [eqzOpcode, integerWord32_toNat] using scalar_i32_eqz floats a b
  · simpa only [eqzOpcode, integerWord64_toNat] using scalar_i64_eqz floats a b
end Exec.Interp

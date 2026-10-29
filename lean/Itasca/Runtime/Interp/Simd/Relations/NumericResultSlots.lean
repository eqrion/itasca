import Itasca.Runtime.Interp.Simd.Relations.InputValues

/-!
Numeric SIMD results represented in runtime slots.

Main declarations: `ValuesAt.simd_numeric_result`. A direct consumer is `Interp.Simd.Execution.LaneValuesExecute`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem ValuesAt.simd_numeric_result {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (ty : valtype) (value : U128)
    (numeric : ty ≠ .FUNCREF ∧ ty ≠ .EXTERNREF ∧ ty ≠ .BOT)
    (small : ty = .I32 ∨ ty = .F32 → value.val < 2^32)
    (capacity : base + Compiler.slots (front.map Compiler.valueType) +
      (Compiler.simdSourceWidth (some ty)).val ≤ words.length) :
    ValuesAt (simdResultSlots words (base+Compiler.slots (front.map Compiler.valueType))
      (Compiler.simdSourceWidth (some ty)) value) base
      (front ++ [Spec.Simd.valueOfBits ty value.bv]) := by
  have cast32 : (UScalar.cast .U64 value).val % 2^32 = value.val % 2^32 := by
    simp only [UScalar.cast_val_eq,UScalarTy.numBits]
    exact Nat.mod_mod_of_dvd _ (by norm_num)
  cases ty
  case V128 => exact represented.simd_vector_result value capacity
  case FUNCREF => exact False.elim (numeric.1 rfl)
  case EXTERNREF => exact False.elim (numeric.2.1 rfl)
  case BOT => exact False.elim (numeric.2.2 rfl)
  case I32 =>
    have bound := small (Or.inl rfl)
    have cast : (UScalar.cast .U64 value).val = value.val := by
      rw [UScalar.cast_val_eq];exact Nat.mod_eq_of_lt (by scalar_tac)
    have result := represented.simd_scalar_result .I32 value (by intro h; cases h)
      (by intro _;rw [cast];exact bound) (by change base + Compiler.slots _ + 1 ≤ words.length at capacity;omega)
    simpa only [Compiler.simdSourceWidth,Store.decodeWords,Spec.Simd.valueOfBits,cast32,BitVec.toNat_setWidth,UScalar.bv_toNat] using result
  case I64 =>
    have result := represented.simd_scalar_result .I64 value (by intro h; cases h)
      (by intro h;rcases h with h|h <;>cases h) (by change base + Compiler.slots _ + 1 ≤ words.length at capacity;omega)
    simpa only [Compiler.simdSourceWidth,Store.decodeWords,Spec.Simd.valueOfBits,UScalar.cast_val_eq,UScalarTy.numBits,
      BitVec.toNat_setWidth,UScalar.bv_toNat] using result
  case F32 =>
    have bound := small (Or.inr rfl)
    have cast : (UScalar.cast .U64 value).val = value.val := by
      rw [UScalar.cast_val_eq];exact Nat.mod_eq_of_lt (by scalar_tac)
    have result := represented.simd_scalar_result .F32 value (by intro h; cases h)
      (by intro _;rw [cast];exact bound) (by change base + Compiler.slots _ + 1 ≤ words.length at capacity;omega)
    simpa only [Compiler.simdSourceWidth,Store.decodeWords,Spec.Simd.valueOfBits,cast32,BitVec.toNat_setWidth,UScalar.bv_toNat] using result
  case F64 =>
    have result := represented.simd_scalar_result .F64 value (by intro h; cases h)
      (by intro h;rcases h with h|h <;>cases h) (by change base + Compiler.slots _ + 1 ≤ words.length at capacity;omega)
    simpa only [Compiler.simdSourceWidth,Store.decodeWords,Spec.Simd.valueOfBits,UScalar.cast_val_eq,UScalarTy.numBits,
      BitVec.toNat_setWidth,UScalar.bv_toNat] using result
end Itasca.Runtime.Interp

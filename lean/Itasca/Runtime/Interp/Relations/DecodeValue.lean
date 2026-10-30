import Itasca.Runtime.Representation.Store

/-! Primitive result decoding, independent of structural store invariants. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
open Itasca.Runtime.Store

theorem cast_usize_exact (n : U64) (h : n.val ≤ Usize.max) :
    (UScalar.cast .Usize n).val = n.val := by
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  have hp : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
  simp only [Usize.max, UScalarTy.numBits, Usize.numBits] at *
  omega

theorem decode_words_code (ty : Itasca.wasm_types.ValueType) (lo hi : U64)
    (hfloat : ty = .F32 → lo.val < 2^32) :
    Compiler.decodeOne (Interp.sourceType ty) (Interp.pairWords ty (lo, hi)) =
      some (decodeWords ty lo hi, []) := by
  cases ty <;> simp only [Interp.sourceType, Interp.pairWords, Compiler.decodeOne, decodeWords,
    decodeRef, decodeElemType, refVal]
  all_goals simp
  case F32 =>
    have hb : lo.val < 4294967296 := hfloat rfl
    rw [Nat.mod_eq_of_lt hb]
  case FuncRef => split <;> rfl
  case ExternRef => split <;> rfl


/-- The actual word decoder returns the value observed by decodeStore. The only
extra bound is on non-null reference encodings, supplied by ReferenceShape. -/
theorem decode_value_boundary (ty : Itasca.wasm_types.ValueType) (lo hi : U64) (store : Usize)
    (href : ty = .FuncRef ∨ ty = .ExternRef → lo.val ≤ Usize.max) :
    runtime.value.decode ty lo hi store ⦃ value =>
      Interp.rawType value = ty ∧ Interp.sourceValue value = decodeWords ty lo hi ⦄ := by
  cases ty <;> simp only [runtime.value.decode, decodeWords]
  all_goals simp [lift, Interp.rawType, Interp.sourceValue]
  case V128 =>
    step as ⟨shifted, hshifted⟩
    congr 2
    have hlow : lo.val < 2^64 := by scalar_tac
    have hhigh : hi.val * 2^64 < 2^128 := by scalar_tac
    have hl128 : lo.val < 2^128 := by scalar_tac
    have hh128 : hi.val < 2^128 := by scalar_tac
    simp only [UScalar.val_or, hshifted, UScalar.cast_val_eq, UScalarTy.numBits]
    rw [Nat.mod_eq_of_lt hl128, Nat.mod_eq_of_lt hh128]
    simp only [U128.size, U128.numBits, UScalarTy.numBits]
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hhigh]
    rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hlow, Nat.shiftLeft_eq]
    omega
  case FuncRef =>
    split
    · rename_i hz
      simp [hz, decodeRef, decodeElemType, refVal]
    · rename_i hn
      have hbound := href (Or.inl rfl)
      have hcast := cast_usize_exact lo hbound
      step as ⟨index, hindex⟩
      simp [decodeRef, decodeElemType, refVal, show lo.val ≠ 0 by scalar_tac]
      scalar_tac
  case ExternRef =>
    split
    · rename_i hz
      simp [hz, decodeRef, decodeElemType, refVal]
    · rename_i hn
      have hbound := href (Or.inr rfl)
      have hcast := cast_usize_exact lo hbound
      step as ⟨index, hindex⟩
      simp [decodeRef, decodeElemType, refVal, show lo.val ≠ 0 by scalar_tac]
      scalar_tac



/-- The extracted primitive decoder recovers any well-formed source value
represented by its exact typed word pair. -/
theorem decode_value_represents (ty : Itasca.wasm_types.ValueType) (lo hi : U64) (store : Usize)
    (value : val) (wellFormed : wf_val value)
    (typed : sourceType ty = Compiler.valueType value)
    (represented : pairWords ty (lo, hi) = Compiler.encodeValue value)
    (floatBound : ty = .F32 → lo.val < 2^32)
    (referenceBound : ty = .FuncRef ∨ ty = .ExternRef → lo.val ≤ Usize.max) :
    runtime.value.decode ty lo hi store ⦃ result =>
      rawType result = ty ∧ sourceValue result = value ⦄ := by
  have roundtrip := Compiler.decode_encode value wellFormed []
  simp only [List.append_nil] at roundtrip
  rw [← typed, ← represented, decode_words_code ty lo hi floatBound] at roundtrip
  have decoded : decodeWords ty lo hi = value := congrArg Prod.fst (Option.some.inj roundtrip)
  step with decode_value_boundary ty lo hi store referenceBound as ⟨result, hty, hvalue⟩
  exact ⟨hty, hvalue.trans decoded⟩

end Itasca.Runtime.Interp


import Exec.Interp.Numeric.Integer.IntRotate
import SpecExt.Builtins.Counts

namespace Exec.Interp
open Aeneas Aeneas.Std
open SpecExt.Builtins

theorem countBits_population (width value : Nat) :
    Primitive.countBits width value = population (integerBits width value) := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih =>
    rw [integerBits_lsb, population_append]
    simp [Primitive.countBits, population, ih, Nat.add_comm]

theorem trailingZeros_bits (width value : Nat) :
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

theorem leadingZeros_bitvec (width : Nat) (bits : BitVec width) :
    Aeneas.Std.BitVec.leadingZeros bits = leadingZeros (integerBits width bits.toNat) := by
  rw [leadingZeros_bits width bits.toNat bits.isLt]
  have zero : bits = 0 ↔ bits.toNat = 0 := by
    constructor
    · intro h; subst bits; rfl
    · intro h; apply BitVec.eq_of_toNat_eq; simpa using h
  simp only [Aeneas.Std.BitVec.leadingZeros, zero]

theorem leadingZeros_le_length (bits : List bit) : leadingZeros bits ≤ bits.length := by
  induction bits with
  | nil => simp [leadingZeros]
  | cons value rest ih =>
    cases value with
    | mk_bit value => cases value <;> simp [leadingZeros] <;> omega

theorem leadingZeros_bitvec_le (width : Nat) (bits : BitVec width) :
    Aeneas.Std.BitVec.leadingZeros bits ≤ width := by
  rw [leadingZeros_bitvec]
  simpa only [integerBits_length] using leadingZeros_le_length (integerBits width bits.toNat)


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
  have bound := leadingZeros_bitvec_le 32 (UScalar.cast .U32 a).bv
  have exactValue : (⟨BitVec.ofNat 32 (Aeneas.Std.BitVec.leadingZeros (UScalar.cast .U32 a).bv)⟩ : U32).val = Aeneas.Std.BitVec.leadingZeros (UScalar.cast .U32 a).bv := by
    change (Aeneas.Std.BitVec.leadingZeros (UScalar.cast .U32 a).bv) % 2^32 = _
    apply Nat.mod_eq_of_lt
    omega
  rw [exactValue]
  have same : iclz_ 32 (.mk_uN (UScalar.cast .U32 a).val) = .mk_uN (Aeneas.Std.BitVec.leadingZeros (UScalar.cast .U32 a).bv) := by
    exact congrArg uN.mk_uN (leadingZeros_bitvec _ _).symm
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
    simp only [ictz_, ibits_, proj_uN_0, ← trailingZeros_bits]
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
    simp only [ipopcnt_, ibits_, proj_uN_0, ← countBits_population]
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
  have bound := leadingZeros_bitvec_le 64 a.bv
  have exactValue : (⟨BitVec.ofNat 32 (Aeneas.Std.BitVec.leadingZeros a.bv)⟩ : U32).val = Aeneas.Std.BitVec.leadingZeros a.bv := by
    change (Aeneas.Std.BitVec.leadingZeros a.bv) % 2^32 = _
    apply Nat.mod_eq_of_lt
    omega
  rw [exactValue]
  have same : iclz_ 64 (.mk_uN a.val) = .mk_uN (Aeneas.Std.BitVec.leadingZeros a.bv) := by
    exact congrArg uN.mk_uN (leadingZeros_bitvec _ _).symm
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
    simp only [ictz_, ibits_, proj_uN_0, ← trailingZeros_bits]
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
    simp only [ipopcnt_, ibits_, proj_uN_0, ← countBits_population]
  have wf := Spec.unsigned_num_wf .I64 (Primitive.countBits 64 a.val) (by change (Primitive.countBits 64 a.val) < 2^64; omega)
  rw [← same] at wf ⊢
  exact .fun_unop__case_5 _ wf

end Exec.Interp

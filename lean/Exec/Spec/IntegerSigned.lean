import Exec.Spec.IntegerDiv

namespace Exec.Spec

@[simp] theorem truncz_neg (value : Rat) : truncz (-value) = -truncz value := by
  simp only [truncz, Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den, Int.neg_tdiv]

theorem truncz_nat_div_int (a b : Nat) :
    truncz ((a : Rat) / (b : Rat)) = ((a / b : Nat) : Int) := by
  have hq : (0 : Rat) ≤ (a : Rat) / (b : Rat) := div_nonneg (by positivity) (by positivity)
  have hn : 0 ≤ ((a : Rat) / (b : Rat)).num := Rat.num_nonneg.mpr hq
  rw [truncz, Int.tdiv_eq_ediv_of_nonneg hn]
  change ((a : Rat) / (b : Rat)).num / (((a : Rat) / (b : Rat)).den : Int) = _
  rw [← Rat.floor_def', Rat.floor_natCast_div_natCast]
  rfl

/-- SpecTec's rational truncation uses the same toward-zero quotient as Rust. -/
theorem truncz_int_div (a b : Int) : truncz ((a : Rat) / (b : Rat)) = a.tdiv b := by
  cases a with
  | ofNat a =>
    cases b with
    | ofNat b => simpa using truncz_nat_div_int a b
    | negSucc b =>
      change truncz ((a : Rat) / ((-(b + 1 : Int) : Int) : Rat)) = (a : Int).tdiv (-(b + 1 : Int))
      simp only [Int.cast_neg, div_neg, truncz_neg, Int.tdiv_neg]
      simpa using congrArg Neg.neg (truncz_nat_div_int a (b + 1))
  | negSucc a =>
    cases b with
    | ofNat b =>
      change truncz (((-(a + 1 : Int) : Int) : Rat) / (b : Rat)) = (-(a + 1 : Int)).tdiv b
      simp only [Int.cast_neg, neg_div, truncz_neg, Int.neg_tdiv]
      rw [Int.tdiv_eq_ediv_of_nonneg (by omega : (0 : Int) ≤ a + 1)]
      simpa using congrArg Neg.neg (truncz_nat_div_int (a + 1) b)
    | negSucc b =>
      change truncz (((-(a + 1 : Int) : Int) : Rat) / ((-(b + 1 : Int) : Int) : Rat)) =
        (-(a + 1 : Int)).tdiv (-(b + 1 : Int))
      simp only [Int.cast_neg, neg_div, div_neg, neg_neg, Int.neg_tdiv_neg]
      rw [Int.tdiv_eq_ediv_of_nonneg (by omega : (0 : Int) ≤ a + 1)]
      simpa using truncz_nat_div_int (a + 1) (b + 1)

/-- The generated signed interpretation agrees with bitvector two's complement. -/
theorem bitvec_signed (width : Nat) (bits : BitVec width) :
    fun_signed_ width bits.toNat bits.toInt := by
  cases width with
  | zero =>
    have zero : bits.toNat = 0 := by have := bits.isLt; omega
    rw [BitVec.toInt_eq_toNat_cond, zero]
    exact .fun_signed__case_0 0 0 (by decide)
  | succ width =>
    have exponent : ((width + 1 : Nat) - (1 : Int)).toNat = width := by omega
    have power : 2 ^ (width + 1) = 2 * 2 ^ width := by rw [pow_succ, Nat.mul_comm]
    rw [BitVec.toInt_eq_toNat_cond]
    split
    · apply fun_signed_.fun_signed__case_0
      simpa only [exponent] using (by omega : bits.toNat < 2 ^ width)
    · apply fun_signed_.fun_signed__case_1
      simpa only [exponent] using And.intro (by omega : 2 ^ width ≤ bits.toNat) bits.isLt

/-- The generated inverse signed interpretation recovers the original bits. -/
theorem bitvec_inv_signed (width : Nat) (bits : BitVec width) :
    fun_inv_signed_ width bits.toInt bits.toNat := by
  cases width with
  | zero =>
    have zero : bits.toNat = 0 := by have := bits.isLt; omega
    rw [BitVec.toInt_eq_toNat_cond, zero]
    exact .fun_inv_signed__case_0 0 0 (by decide)
  | succ width =>
    have exponent : ((width + 1 : Nat) - (1 : Int)).toNat = width := by omega
    have power : 2 ^ (width + 1) = 2 * 2 ^ width := by rw [pow_succ, Nat.mul_comm]
    have bound := bits.isLt
    have powerCast : ((2 : Int) ^ (width + 1)) = ((2 ^ (width + 1) : Nat) : Int) := by simp
    have halfCast : ((2 : Int) ^ width) = ((2 ^ width : Nat) : Int) := by simp
    rw [BitVec.toInt_eq_toNat_cond]
    split
    · exact .fun_inv_signed__case_0 _ _ (by simp only [exponent, halfCast]; omega)
    · have encoded : ((bits.toNat : Int) - ((2 ^ (width + 1) : Nat) : Int) +
          (2 : Int) ^ (width + 1)).toNat = bits.toNat := by rw [powerCast]; simp
      have raw := fun_inv_signed_.fun_inv_signed__case_1 (width + 1)
        ((bits.toNat : Int) - ((2 ^ (width + 1) : Nat) : Int)) (by
          simp only [exponent, halfCast]
          omega)
      simpa only [encoded] using raw

@[simp] theorem truncz_intCast (value : Int) : truncz (value : Rat) = value := by
  simp [truncz]

/-- A representable toward-zero quotient satisfies the signed division rule. -/
theorem signed_div_relation (width : Nat) (a b result : BitVec width)
    (nonzero : b.toNat ≠ 0) (quotient : result.toInt = a.toInt.tdiv b.toInt) :
    fun_idiv_ width .S (.mk_uN a.toNat) (.mk_uN b.toNat) (some (.mk_uN result.toNat)) := by
  have exponent : ((width : Int) - 1).toNat = width - 1 := by omega
  apply fun_idiv_.fun_idiv__case_4 width _ _ b.toInt a.toInt result.toNat
  · exact bitvec_signed width b
  · exact bitvec_signed width a
  · rw [truncz_int_div, ← quotient]
    exact bitvec_inv_signed width result
  · exact nonzero
  · intro overflow
    have truncated := congrArg truncz overflow
    have hp : (2 : Rat) ^ (width - 1) = (((2 : Int) ^ (width - 1) : Int) : Rat) := by simp
    rw [truncz_int_div, ← quotient, exponent, hp, truncz_intCast] at truncated
    have bound := BitVec.toInt_lt (x := result)
    omega
  · exact unsigned_wf_of_lt width result.toNat result.isLt

/-- Signed remainder uses the same toward-zero remainder as Rust, including
zero for the minimum signed integer modulo minus one. -/
theorem signed_rem_relation (width : Nat) (a b result : BitVec width)
    (nonzero : b.toNat ≠ 0) (remainder : result.toInt = a.toInt.tmod b.toInt) :
    fun_irem_ width .S (.mk_uN a.toNat) (.mk_uN b.toNat) (some (.mk_uN result.toNat)) := by
  apply fun_irem_.fun_irem__case_3 width _ _ a.toInt b.toInt b.toInt a.toInt result.toNat
  · exact bitvec_signed width b
  · exact bitvec_signed width a
  · rw [truncz_int_div, ← Int.tmod_def, ← remainder]
    exact bitvec_inv_signed width result
  · exact nonzero
  · exact ⟨rfl, rfl⟩
  · exact unsigned_wf_of_lt width result.toNat result.isLt

/-- Lift the signed div result to the generated scalar instruction relation. -/
theorem integer_divs_relation (ty : Inn)
    (a b result : BitVec (sizenn (numtype_Inn ty)))
    (nonzero : b.toNat ≠ 0) (quotient : result.toInt = a.toInt.tdiv b.toInt) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty (.DIV .S))
      (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat))
      (some [.mk_num__0 ty (.mk_uN result.toNat)]) := by
  have hw := unsigned_wf_of_lt (sizenn (numtype_Inn ty)) result.toNat result.isLt
  have hn := unsigned_num_wf ty result.toNat result.isLt
  have relation := signed_div_relation (sizenn (numtype_Inn ty)) a b result nonzero quotient
  cases ty
  · apply fun_binop_.fun_binop__case_6 .S _ _ (some (.mk_uN result.toNat)) relation
    · simpa [Forall, list_, OMap] using hn
    · decide
    · simpa [Forall, size, valtype_Inn, sizenn, numtype_Inn, valtype_numtype] using hw
    · simpa [Forall] using hn
  · apply fun_binop_.fun_binop__case_7 .S _ _ (some (.mk_uN result.toNat)) relation
    · simpa [Forall, list_, OMap] using hn
    · decide
    · simpa [Forall, size, valtype_Inn, sizenn, numtype_Inn, valtype_numtype] using hw
    · simpa [Forall] using hn

/-- A zero signed divisor yields the generated trapping result. -/
theorem integer_divs_zero_relation (ty : Inn) (a : Nat) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty (.DIV .S))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN 0)) (some []) := by
  cases ty
  · apply fun_binop_.fun_binop__case_6 .S _ _ none (.fun_idiv__case_2 _ _)
    all_goals simp [Forall, list_, OMap, size, valtype_Inn]
  · apply fun_binop_.fun_binop__case_7 .S _ _ none (.fun_idiv__case_2 _ _)
    all_goals simp [Forall, list_, OMap, size, valtype_Inn]

/-- Lift the signed rem result to the generated scalar instruction relation. -/
theorem integer_rems_relation (ty : Inn)
    (a b result : BitVec (sizenn (numtype_Inn ty)))
    (nonzero : b.toNat ≠ 0) (remainder : result.toInt = a.toInt.tmod b.toInt) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty (.REM .S))
      (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat))
      (some [.mk_num__0 ty (.mk_uN result.toNat)]) := by
  have hw := unsigned_wf_of_lt (sizenn (numtype_Inn ty)) result.toNat result.isLt
  have hn := unsigned_num_wf ty result.toNat result.isLt
  have relation := signed_rem_relation (sizenn (numtype_Inn ty)) a b result nonzero remainder
  cases ty
  · apply fun_binop_.fun_binop__case_8 .S _ _ (some (.mk_uN result.toNat)) relation
    · simpa [Forall, list_, OMap] using hn
    · decide
    · simpa [Forall, size, valtype_Inn, sizenn, numtype_Inn, valtype_numtype] using hw
    · simpa [Forall] using hn
  · apply fun_binop_.fun_binop__case_9 .S _ _ (some (.mk_uN result.toNat)) relation
    · simpa [Forall, list_, OMap] using hn
    · decide
    · simpa [Forall, size, valtype_Inn, sizenn, numtype_Inn, valtype_numtype] using hw
    · simpa [Forall] using hn

/-- A zero signed divisor yields the generated trapping result. -/
theorem integer_rems_zero_relation (ty : Inn) (a : Nat) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty (.REM .S))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN 0)) (some []) := by
  cases ty
  · apply fun_binop_.fun_binop__case_8 .S _ _ none (.fun_irem__case_2 _ _)
    all_goals simp [Forall, list_, OMap, size, valtype_Inn]
  · apply fun_binop_.fun_binop__case_9 .S _ _ none (.fun_irem__case_2 _ _)
    all_goals simp [Forall, list_, OMap, size, valtype_Inn]

/-- Lift a generated signed-division trap to the scalar instruction rule. -/
theorem integer_divs_trap_relation (ty : Inn) (a b : Nat)
    (trap : fun_idiv_ (sizenn (numtype_Inn ty)) .S (.mk_uN a) (.mk_uN b) none) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty (.DIV .S))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b)) (some []) := by
  cases ty
  · apply fun_binop_.fun_binop__case_6 .S _ _ none trap
    all_goals simp [Forall, list_, OMap, size, valtype_Inn]
  · apply fun_binop_.fun_binop__case_7 .S _ _ none trap
    all_goals simp [Forall, list_, OMap, size, valtype_Inn]

/-- The minimum signed 32-bit integer divided by minus one traps. -/
theorem signed_div_overflow32 :
    fun_idiv_ 32 .S (.mk_uN 2147483648) (.mk_uN 4294967295) none := by
  apply fun_idiv_.fun_idiv__case_3 32 _ _ (-1) (-2147483648)
  · have relation := fun_signed_.fun_signed__case_1 32 4294967295 (by norm_num [Int.toNat])
    norm_num [Int.toNat] at relation ⊢
    exact relation
  · have relation := fun_signed_.fun_signed__case_1 32 2147483648 (by norm_num [Int.toNat])
    norm_num [Int.toNat] at relation ⊢
    exact relation
  · norm_num [Int.toNat, proj_uN_0]
  · norm_num [Int.toNat]

/-- The minimum signed 64-bit integer divided by minus one traps. -/
theorem signed_div_overflow64 :
    fun_idiv_ 64 .S (.mk_uN 9223372036854775808) (.mk_uN 18446744073709551615) none := by
  apply fun_idiv_.fun_idiv__case_3 64 _ _ (-1) (-9223372036854775808)
  · have relation := fun_signed_.fun_signed__case_1 64 18446744073709551615 (by norm_num [Int.toNat])
    norm_num [Int.toNat] at relation ⊢
    exact relation
  · have relation := fun_signed_.fun_signed__case_1 64 9223372036854775808 (by norm_num [Int.toNat])
    norm_num [Int.toNat] at relation ⊢
    exact relation
  · norm_num [Int.toNat, proj_uN_0]
  · norm_num [Int.toNat]

theorem integer_divs_result_relation (ty : Inn) (a b result : Nat)
    (relation : fun_idiv_ (sizenn (numtype_Inn ty)) .S (.mk_uN a) (.mk_uN b) (some (.mk_uN result))) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty (.DIV .S))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some [.mk_num__0 ty (.mk_uN result)]) := by
  have hw : wf_uN (sizenn (numtype_Inn ty)) (.mk_uN result) := by cases relation <;> assumption
  have hn : wf_num_ (numtype_Inn ty) (.mk_num__0 ty (.mk_uN result)) := by
    cases ty <;> exact .num__case_0 _ _ _ (by decide) hw rfl
  cases ty
  · apply fun_binop_.fun_binop__case_6 .S _ _ (some (.mk_uN result)) relation
    · simpa [Forall, list_, OMap] using hn
    · decide
    · simpa [Forall, size, valtype_Inn, sizenn, numtype_Inn, valtype_numtype] using hw
    · simpa [Forall] using hn
  · apply fun_binop_.fun_binop__case_7 .S _ _ (some (.mk_uN result)) relation
    · simpa [Forall, list_, OMap] using hn
    · decide
    · simpa [Forall, size, valtype_Inn, sizenn, numtype_Inn, valtype_numtype] using hw
    · simpa [Forall] using hn

theorem integer_rems_result_relation (ty : Inn) (a b result : Nat)
    (relation : fun_irem_ (sizenn (numtype_Inn ty)) .S (.mk_uN a) (.mk_uN b) (some (.mk_uN result))) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty (.REM .S))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some [.mk_num__0 ty (.mk_uN result)]) := by
  have hw : wf_uN (sizenn (numtype_Inn ty)) (.mk_uN result) := by cases relation <;> assumption
  have hn : wf_num_ (numtype_Inn ty) (.mk_num__0 ty (.mk_uN result)) := by
    cases ty <;> exact .num__case_0 _ _ _ (by decide) hw rfl
  cases ty
  · apply fun_binop_.fun_binop__case_8 .S _ _ (some (.mk_uN result)) relation
    · simpa [Forall, list_, OMap] using hn
    · decide
    · simpa [Forall, size, valtype_Inn, sizenn, numtype_Inn, valtype_numtype] using hw
    · simpa [Forall] using hn
  · apply fun_binop_.fun_binop__case_9 .S _ _ (some (.mk_uN result)) relation
    · simpa [Forall, list_, OMap] using hn
    · decide
    · simpa [Forall, size, valtype_Inn, sizenn, numtype_Inn, valtype_numtype] using hw
    · simpa [Forall] using hn

/-- The minimum signed integer modulo minus one is the representable zero. -/
theorem signed_rem_overflow32 :
    fun_irem_ 32 .S (.mk_uN 2147483648) (.mk_uN 4294967295) (some (.mk_uN 0)) := by
  exact signed_rem_relation 32 (BitVec.ofNat 32 2147483648)
    (BitVec.ofNat 32 4294967295) (BitVec.ofNat 32 0) (by decide +kernel) (by decide +kernel)

/-- The minimum signed integer modulo minus one is the representable zero. -/
theorem signed_rem_overflow64 :
    fun_irem_ 64 .S (.mk_uN 9223372036854775808) (.mk_uN 18446744073709551615) (some (.mk_uN 0)) := by
  exact signed_rem_relation 64 (BitVec.ofNat 64 9223372036854775808)
    (BitVec.ofNat 64 18446744073709551615) (BitVec.ofNat 64 0) (by decide +kernel) (by decide +kernel)

end Exec.Spec

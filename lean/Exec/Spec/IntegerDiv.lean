import Exec.Spec.Integer
import Mathlib.Data.Rat.Floor

/-! The rational quotient in SpecTec's integer rules agrees with natural
quotient and remainder for unsigned inputs. -/

namespace Exec.Spec

theorem truncz_nat_div (a b : Nat) :
    (truncz ((a : Rat) / (b : Rat))).toNat = a / b := by
  have hq : (0 : Rat) ≤ (a : Rat) / (b : Rat) := div_nonneg (by positivity) (by positivity)
  have hn : 0 ≤ ((a : Rat) / (b : Rat)).num := Rat.num_nonneg.mpr hq
  rw [truncz, Int.tdiv_eq_ediv_of_nonneg hn]
  change (((a : Rat) / (b : Rat)).num / (((a : Rat) / (b : Rat)).den : Int)).toNat = _
  rw [← Rat.floor_def', Rat.floor_natCast_div_natCast]
  rfl

theorem unsigned_wf_of_lt (width bits : Nat) (hb : bits < 2 ^ width) :
    wf_uN width (.mk_uN bits) := by
  apply wf_uN.uN_case_0
  have hp : (2 : Int) ^ width = ((2 ^ width : Nat) : Int) := by simp
  rw [hp]
  omega

/-- Natural quotient is a result permitted by unsigned integer division. -/
theorem unsigned_div_relation (width a b : Nat) (ha : a < 2 ^ width) (hb : b ≠ 0) :
    fun_idiv_ width .U (.mk_uN a) (.mk_uN b) (some (.mk_uN (a / b))) := by
  have hq : a / b < 2 ^ width := lt_of_le_of_lt (Nat.div_le_self a b) ha
  have hw := unsigned_wf_of_lt width (a / b) hq
  have raw := fun_idiv_.fun_idiv__case_1 width (.mk_uN a) (.mk_uN b) hb (by
    simpa only [proj_uN_0, truncz_nat_div] using hw)
  simpa only [proj_uN_0, truncz_nat_div] using raw

/-- The rational remainder formula is the natural remainder for unsigned inputs. -/
theorem unsigned_rem_formula (a b : Nat) :
    ((a : Int) - (b : Int) * ((truncz ((a : Rat) / (b : Rat))).toNat : Int)).toNat = a % b := by
  rw [truncz_nat_div]
  have hle : b * (a / b) ≤ a := Nat.mul_div_le a b
  rw [← Int.natCast_mul, ← Int.ofNat_sub hle, Int.toNat_natCast, Nat.mod_eq_sub_div_mul, Nat.mul_comm]

/-- Natural remainder is a result permitted by unsigned integer remainder. -/
theorem unsigned_rem_relation (width a b : Nat) (ha : a < 2 ^ width) (hb : b ≠ 0) :
    fun_irem_ width .U (.mk_uN a) (.mk_uN b) (some (.mk_uN (a % b))) := by
  have hq : a % b < 2 ^ width := lt_of_le_of_lt (Nat.mod_le a b) ha
  have hw := unsigned_wf_of_lt width (a % b) hq
  have raw := fun_irem_.fun_irem__case_1 width (.mk_uN a) (.mk_uN b) hb (by
    simpa only [proj_uN_0, unsigned_rem_formula] using hw)
  simpa only [proj_uN_0, unsigned_rem_formula] using raw

theorem unsigned_num_wf (ty : Inn) (bits : Nat)
    (hb : bits < 2 ^ sizenn (numtype_Inn ty)) :
    wf_num_ (numtype_Inn ty) (.mk_num__0 ty (.mk_uN bits)) := by
  apply wf_num_.num__case_0 _ _ _ ?_ ?_ rfl
  · cases ty <;> decide
  · cases ty <;> exact unsigned_wf_of_lt _ _ hb

/-- Lift unsigned quotient to the generated scalar-operator relation. -/
theorem integer_divu_relation (ty : Inn) (a b : Nat)
    (ha : a < 2 ^ sizenn (numtype_Inn ty)) (hb : b ≠ 0) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty (.DIV .U))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some [.mk_num__0 ty (.mk_uN (a / b))]) := by
  have hq : a / b < 2 ^ sizenn (numtype_Inn ty) := lt_of_le_of_lt (Nat.div_le_self a b) ha
  have hw := unsigned_wf_of_lt (sizenn (numtype_Inn ty)) (a / b) hq
  have hn := unsigned_num_wf ty (a / b) hq
  have hi := unsigned_div_relation (sizenn (numtype_Inn ty)) a b ha hb
  cases ty
  · apply fun_binop_.fun_binop__case_6 .U _ _ (some (.mk_uN (a / b))) hi
    · simpa [Forall, list_, OMap] using hn
    · decide
    · simpa [Forall, size, valtype_Inn, sizenn, numtype_Inn, valtype_numtype] using hw
    · simpa [Forall] using hn
  · apply fun_binop_.fun_binop__case_7 .U _ _ (some (.mk_uN (a / b))) hi
    · simpa [Forall, list_, OMap] using hn
    · decide
    · simpa [Forall, size, valtype_Inn, sizenn, numtype_Inn, valtype_numtype] using hw
    · simpa [Forall] using hn

/-- Lift unsigned remainder to the generated scalar-operator relation. -/
theorem integer_remu_relation (ty : Inn) (a b : Nat)
    (ha : a < 2 ^ sizenn (numtype_Inn ty)) (hb : b ≠ 0) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty (.REM .U))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some [.mk_num__0 ty (.mk_uN (a % b))]) := by
  have hq : a % b < 2 ^ sizenn (numtype_Inn ty) := lt_of_le_of_lt (Nat.mod_le a b) ha
  have hw := unsigned_wf_of_lt (sizenn (numtype_Inn ty)) (a % b) hq
  have hn := unsigned_num_wf ty (a % b) hq
  have hi := unsigned_rem_relation (sizenn (numtype_Inn ty)) a b ha hb
  cases ty
  · apply fun_binop_.fun_binop__case_8 .U _ _ (some (.mk_uN (a % b))) hi
    · simpa [Forall, list_, OMap] using hn
    · decide
    · simpa [Forall, size, valtype_Inn, sizenn, numtype_Inn, valtype_numtype] using hw
    · simpa [Forall] using hn
  · apply fun_binop_.fun_binop__case_9 .U _ _ (some (.mk_uN (a % b))) hi
    · simpa [Forall, list_, OMap] using hn
    · decide
    · simpa [Forall, size, valtype_Inn, sizenn, numtype_Inn, valtype_numtype] using hw
    · simpa [Forall] using hn

/-- Source guards make division by zero unambiguously trapping, for both signs. -/
theorem division_zero_only (width : Nat) (sign : sx) (a : uN) (result : Option iN)
    (h : fun_idiv_ width sign a (.mk_uN 0) result) : result = none := by
  cases h <;> simp_all [proj_uN_0]

/-- Source guards make remainder by zero unambiguously trapping, for both signs. -/
theorem remainder_zero_only (width : Nat) (sign : sx) (a : uN) (result : Option iN)
    (h : fun_irem_ width sign a (.mk_uN 0) result) : result = none := by
  cases h <;> simp_all [proj_uN_0]


/-- A zero divisor yields the empty result list that triggers the trap rule. -/
theorem integer_divu_zero_relation (ty : Inn) (a : Nat) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty (.DIV .U))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN 0)) (some []) := by
  cases ty
  · apply fun_binop_.fun_binop__case_6 .U _ _ none (.fun_idiv__case_0 _ _)
    all_goals simp [Forall, list_, OMap, size, valtype_Inn]
  · apply fun_binop_.fun_binop__case_7 .U _ _ none (.fun_idiv__case_0 _ _)
    all_goals simp [Forall, list_, OMap, size, valtype_Inn]

/-- A zero divisor yields the empty result list that triggers the trap rule. -/
theorem integer_remu_zero_relation (ty : Inn) (a : Nat) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty (.REM .U))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN 0)) (some []) := by
  cases ty
  · apply fun_binop_.fun_binop__case_8 .U _ _ none (.fun_irem__case_0 _ _)
    all_goals simp [Forall, list_, OMap, size, valtype_Inn]
  · apply fun_binop_.fun_binop__case_9 .U _ _ none (.fun_irem__case_0 _ _)
    all_goals simp [Forall, list_, OMap, size, valtype_Inn]

end Exec.Spec

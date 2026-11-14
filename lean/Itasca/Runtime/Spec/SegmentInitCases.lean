import Itasca.Runtime.Spec.Integer
import Mathlib.Data.Rat.Floor
import SpecExt.Builtins.Examples
import Mathlib.Tactic

/-!
Sections, each formerly its own module: IntegerDiv, IntegerBits, Counted, IntegerSigned, IntegerCompareSigned, IntegerShift, IntegerExtend, IntegerRotate, SegmentCopy, SegmentInitCases.
-/

/-! ## IntegerDiv -/

section

/-! The rational quotient in SpecTec's integer rules agrees with natural
quotient and remainder for unsigned inputs. -/

namespace Itasca.Runtime.Spec

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

end Itasca.Runtime.Spec

end

/-! ## IntegerBits -/

section

namespace Itasca.Runtime.Spec
open SpecExt.Builtins

theorem integer_and_relation (ty : Inn) (a b : Nat) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty .AND) (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some [.mk_num__0 ty (iand_ (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b))]) := by
  cases ty
  · apply fun_binop_.fun_binop__case_10
    rw [iand_value]
    exact unsigned_num_wf .I32 _ (Nat.mod_lt _ (by decide))
  · apply fun_binop_.fun_binop__case_11
    rw [iand_value]
    exact unsigned_num_wf .I64 _ (Nat.mod_lt _ (by decide))

theorem integer_or_relation (ty : Inn) (a b : Nat) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty .OR) (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some [.mk_num__0 ty (ior_ (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b))]) := by
  cases ty
  · apply fun_binop_.fun_binop__case_12
    rw [ior_value]
    exact unsigned_num_wf .I32 _ (Nat.mod_lt _ (by decide))
  · apply fun_binop_.fun_binop__case_13
    rw [ior_value]
    exact unsigned_num_wf .I64 _ (Nat.mod_lt _ (by decide))

theorem integer_xor_relation (ty : Inn) (a b : Nat) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty .XOR) (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some [.mk_num__0 ty (ixor_ (sizenn (numtype_Inn ty)) (.mk_uN a) (.mk_uN b))]) := by
  cases ty
  · apply fun_binop_.fun_binop__case_14
    rw [ixor_value]
    exact unsigned_num_wf .I32 _ (Nat.mod_lt _ (by decide))
  · apply fun_binop_.fun_binop__case_15
    rw [ixor_value]
    exact unsigned_num_wf .I64 _ (Nat.mod_lt _ (by decide))

theorem integer_shl_relation (ty : Inn) (a b : Nat) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty .SHL)
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some [.mk_num__0 ty (.mk_uN ((a * 2 ^ (b % sizenn (numtype_Inn ty))) % 2 ^ sizenn (numtype_Inn ty)))]) := by
  cases ty
  · apply fun_binop_.fun_binop__case_16
    exact unsigned_num_wf .I32 _ (Nat.mod_lt _ (by decide))
  · apply fun_binop_.fun_binop__case_17
    exact unsigned_num_wf .I64 _ (Nat.mod_lt _ (by decide))

theorem integer_shru_relation (ty : Inn) (a b : Nat) (ha : a < 2 ^ sizenn (numtype_Inn ty)) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty (.SHR .U))
      (.mk_num__0 ty (.mk_uN a)) (.mk_num__0 ty (.mk_uN b))
      (some [.mk_num__0 ty (.mk_uN (a / 2 ^ (b % sizenn (numtype_Inn ty))))]) := by
  have hb : a / 2 ^ (b % sizenn (numtype_Inn ty)) < 2 ^ sizenn (numtype_Inn ty) :=
    lt_of_le_of_lt (Nat.div_le_self _ _) ha
  cases ty
  · apply fun_binop_.fun_binop__case_18
    exact unsigned_num_wf .I32 _ hb
  · apply fun_binop_.fun_binop__case_19
    exact unsigned_num_wf .I64 _ hb

end Itasca.Runtime.Spec

end

/-! ## Counted -/

section

/-! Counted extended reductions for quantitative execution simulation. These
lemmas count specification steps, not interpreter dispatches. The generic
simulation theorem below still requires a per-dispatch proof and a bounded
administrative measure; it makes no claim about the Rust interpreter by itself. -/

namespace Itasca.Runtime.Spec
open SpecExt

inductive StepsHN : Nat → config → List HostEvent → config → Prop where
  | refl {c : config} : wf_config c → StepsHN 0 c [] c
  | cons {n : Nat} {c c' c'' : config} {events rest : List HostEvent} :
      StepH c events c' → StepsHN n c' rest c'' →
      StepsHN (n + 1) c (events ++ rest) c''

theorem StepsHN.erase {n : Nat} {c c' : config} {events : List HostEvent}
    (h : StepsHN n c events c') : StepsH c events c' := by
  induction h with
  | refl h => exact .refl h
  | cons h _ ih => exact .cons h ih

theorem StepsHN.trans {n m : Nat} {c c' c'' : config} {events rest : List HostEvent}
    (h : StepsHN n c events c') (h' : StepsHN m c' rest c'') :
    StepsHN (n + m) c (events ++ rest) c'' := by
  induction h with
  | refl _ => simpa using h'
  | cons h _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.append_assoc] using StepsHN.cons h (ih h')

theorem StepsHN.map {wrap : config → config}
    (hw : ∀ c, wf_config c → wf_config (wrap c))
    (hs : ∀ c events c', StepH c events c' → StepH (wrap c) events (wrap c'))
    {n : Nat} {c c' : config} {events : List HostEvent}
    (h : StepsHN n c events c') : StepsHN n (wrap c) events (wrap c') := by
  induction h with
  | refl h => exact .refl (hw _ h)
  | cons h _ ih => exact .cons (hs _ _ _ h) ih

theorem StepsHN.zero {c c' : config} {events : List HostEvent}
    (h : StepsHN 0 c events c') : c = c' ∧ events = [] := by
  cases h
  exact ⟨rfl, rfl⟩

theorem steps_h_count {c c' : config} {events : List HostEvent}
    (h : StepsH c events c') : ∃ n, StepsHN n c events c' := by
  induction h with
  | refl h => exact ⟨0, .refl h⟩
  | cons h _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .cons h hn⟩

/-- A finite machine run carrying the events from each dispatch. -/
inductive Iterations {S : Type} (next : S → List HostEvent → S → Prop) :
    Nat → S → List HostEvent → S → Prop where
  | refl (s : S) : Iterations next 0 s [] s
  | cons {n : Nat} {s s' s'' : S} {events rest : List HostEvent} :
      next s events s' → Iterations next n s' rest s'' →
      Iterations next (n + 1) s (events ++ rest) s''

end Itasca.Runtime.Spec

end

/-! ## IntegerSigned -/

section

namespace Itasca.Runtime.Spec

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

@[simp] theorem truncz_int_cast (value : Int) : truncz (value : Rat) = value := by
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
    rw [truncz_int_div, ← quotient, exponent, hp, truncz_int_cast] at truncated
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

end Itasca.Runtime.Spec

end

/-! ## IntegerCompareSigned -/

section

namespace Itasca.Runtime.Spec

theorem integer_lts_relation (ty : Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty (.LT .S))
      (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat))
      (some (.mk_num__0 .I32 (.mk_uN (if a.toInt < b.toInt then 1 else 0)))) := by
  have wf := predicate_i32_wf (a.toInt < b.toInt)
  have boolean : nat_of_bool (decide (a.toInt < b.toInt)) = (if a.toInt < b.toInt then 1 else 0) := by
    by_cases h : a.toInt < b.toInt <;> simp [h, nat_of_bool]
  have relation : fun_ilt_ (sizenn (numtype_Inn ty)) .S (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (if a.toInt < b.toInt then 1 else 0)) := by
    rw [← boolean]
    exact .fun_ilt__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  cases ty
  · exact .fun_relop__case_4 .S _ _ _ relation wf
  · exact .fun_relop__case_5 .S _ _ _ relation wf

theorem integer_gts_relation (ty : Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty (.GT .S))
      (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat))
      (some (.mk_num__0 .I32 (.mk_uN (if a.toInt > b.toInt then 1 else 0)))) := by
  have wf := predicate_i32_wf (a.toInt > b.toInt)
  have boolean : nat_of_bool (decide (a.toInt > b.toInt)) = (if a.toInt > b.toInt then 1 else 0) := by
    by_cases h : a.toInt > b.toInt <;> simp [h, nat_of_bool]
  have relation : fun_igt_ (sizenn (numtype_Inn ty)) .S (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (if a.toInt > b.toInt then 1 else 0)) := by
    rw [← boolean]
    exact .fun_igt__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  cases ty
  · exact .fun_relop__case_6 .S _ _ _ relation wf
  · exact .fun_relop__case_7 .S _ _ _ relation wf

theorem integer_les_relation (ty : Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty (.LE .S))
      (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat))
      (some (.mk_num__0 .I32 (.mk_uN (if a.toInt ≤ b.toInt then 1 else 0)))) := by
  have wf := predicate_i32_wf (a.toInt ≤ b.toInt)
  have boolean : nat_of_bool (decide (a.toInt ≤ b.toInt)) = (if a.toInt ≤ b.toInt then 1 else 0) := by
    by_cases h : a.toInt ≤ b.toInt <;> simp [h, nat_of_bool]
  have relation : fun_ile_ (sizenn (numtype_Inn ty)) .S (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (if a.toInt ≤ b.toInt then 1 else 0)) := by
    rw [← boolean]
    exact .fun_ile__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  cases ty
  · exact .fun_relop__case_8 .S _ _ _ relation wf
  · exact .fun_relop__case_9 .S _ _ _ relation wf

theorem integer_ges_relation (ty : Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty (.GE .S))
      (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat))
      (some (.mk_num__0 .I32 (.mk_uN (if a.toInt ≥ b.toInt then 1 else 0)))) := by
  have wf := predicate_i32_wf (a.toInt ≥ b.toInt)
  have boolean : nat_of_bool (decide (a.toInt ≥ b.toInt)) = (if a.toInt ≥ b.toInt then 1 else 0) := by
    by_cases h : a.toInt ≥ b.toInt <;> simp [h, nat_of_bool]
  have relation : fun_ige_ (sizenn (numtype_Inn ty)) .S (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (if a.toInt ≥ b.toInt then 1 else 0)) := by
    rw [← boolean]
    exact .fun_ige__case_1 _ _ _ _ _ (bitvec_signed _ b) (bitvec_signed _ a) (boolean_u32_wf _)
  cases ty
  · exact .fun_relop__case_10 .S _ _ _ relation wf
  · exact .fun_relop__case_11 .S _ _ _ relation wf

end Itasca.Runtime.Spec

end

/-! ## IntegerShift -/

section

namespace Itasca.Runtime.Spec

/-- The builtin's signed value is bitvector two's-complement interpretation. -/
theorem signed_value_bitvec (width : Nat) (bits : BitVec width) :
    SpecExt.Builtins.signedValue width bits.toNat = bits.toInt := by
  cases width with
  | zero =>
    have zero : bits.toNat = 0 := by have := bits.isLt; omega
    simp [SpecExt.Builtins.signedValue, BitVec.toInt_eq_toNat_cond, zero]
  | succ width =>
    have power : 2 ^ (width + 1) = 2 * 2 ^ width := by rw [pow_succ, Nat.mul_comm]
    have cast : ((2 : Int) ^ (width + 1)) = ((2 ^ (width + 1) : Nat) : Int) := by simp
    simp only [SpecExt.Builtins.signedValue, Nat.add_sub_cancel, BitVec.toInt_eq_toNat_cond, cast]
    split_ifs <;> omega

theorem encode_signed_bitvec (width : Nat) (bits : BitVec width) :
    SpecExt.Builtins.encodeSigned width bits.toInt = .mk_uN bits.toNat := by
  have same := congrArg BitVec.toNat (BitVec.ofInt_toInt (x := bits))
  simpa only [SpecExt.Builtins.encodeSigned, BitVec.toNat_ofInt, Nat.cast_pow, Nat.cast_ofNat] using congrArg uN.mk_uN same

/-- Arithmetic right shift matches the signed builtin, including negative
odd operands for which floor division differs from truncation toward zero. -/
theorem ishrs_bitvec (width : Nat) (bits : BitVec width) (shift : Nat) :
    ishr_ width .S (.mk_uN bits.toNat) (.mk_uN shift) =
      .mk_uN (bits.sshiftRight (shift % width)).toNat := by
  simp only [ishr_, proj_uN_0, signed_value_bitvec]
  rw [show (2 : Int) ^ (shift % width) = ((2 ^ (shift % width) : Nat) : Int) by simp]
  rw [← Int.shiftRight_eq_div_pow, ← BitVec.toInt_sshiftRight]
  exact encode_signed_bitvec width _

theorem integer_shrs_relation (ty : Inn) (bits : BitVec (sizenn (numtype_Inn ty))) (shift : Nat) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty (.SHR .S))
      (.mk_num__0 ty (.mk_uN bits.toNat)) (.mk_num__0 ty (.mk_uN shift))
      (some [.mk_num__0 ty (.mk_uN (bits.sshiftRight (shift % sizenn (numtype_Inn ty))).toNat)]) := by
  have wf := unsigned_num_wf ty (bits.sshiftRight (shift % sizenn (numtype_Inn ty))).toNat
    (bits.sshiftRight (shift % sizenn (numtype_Inn ty))).isLt
  have same := ishrs_bitvec (sizenn (numtype_Inn ty)) bits shift
  cases ty
  · rw [← same] at wf ⊢
    exact .fun_binop__case_18 .S _ _ wf
  · rw [← same] at wf ⊢
    exact .fun_binop__case_19 .S _ _ wf

end Itasca.Runtime.Spec

end

/-! ## IntegerExtend -/

section

namespace Itasca.Runtime.Spec

theorem extend_signed_bitvec (small large : Nat) (bits : BitVec small) :
    extend__ small large .S (.mk_uN bits.toNat) = .mk_uN (bits.signExtend large).toNat := by
  simp only [extend__, proj_uN_0, signed_value_bitvec, SpecExt.Builtins.encodeSigned,
    BitVec.signExtend, BitVec.toNat_ofInt, Nat.cast_pow, Nat.cast_ofNat]

theorem extend_unary_bitvec (ty : Inn) (small : Nat) (bits : BitVec (sizenn (numtype_Inn ty))) :
    fun_unop_ (numtype_Inn ty) (.mk_unop__0 ty (.EXTEND small))
      (.mk_num__0 ty (.mk_uN bits.toNat))
      (some [.mk_num__0 ty (.mk_uN ((bits.setWidth small).signExtend (sizenn (numtype_Inn ty))).toNat)]) := by
  have same : extend__ small (sizenn (numtype_Inn ty)) .S
      (wrap__ (sizenn (numtype_Inn ty)) small (.mk_uN bits.toNat)) =
      .mk_uN ((bits.setWidth small).signExtend (sizenn (numtype_Inn ty))).toNat := by
    simpa only [wrap__, proj_uN_0, BitVec.toNat_setWidth] using
      extend_signed_bitvec small (sizenn (numtype_Inn ty)) (bits.setWidth small)
  have wf := unsigned_num_wf ty _ ((bits.setWidth small).signExtend (sizenn (numtype_Inn ty))).isLt
  cases ty
  · rw [← same] at wf ⊢; exact .fun_unop__case_6 small _ wf
  · rw [← same] at wf ⊢; exact .fun_unop__case_7 small _ wf

theorem integer_wrap_relation (bits : BitVec 64) :
    fun_cvtop__ .I64 .I32 (.mk_cvtop___0 .I64 .I32 .WRAP)
      (.mk_num__0 .I64 (.mk_uN bits.toNat))
      (some [.mk_num__0 .I32 (.mk_uN (bits.setWidth 32).toNat)]) := by
  have wf := unsigned_num_wf .I32 _ (bits.setWidth 32).isLt
  simpa only [wrap__, proj_uN_0, sizenn1, sizenn2, numtype_Inn, valtype_numtype, size, Option.get!, BitVec.toNat_setWidth] using
    fun_cvtop__.fun_cvtop___case_5 (.mk_uN bits.toNat) wf

theorem integer_extends_relation (bits : BitVec 32) :
    fun_cvtop__ .I32 .I64 (.mk_cvtop___0 .I32 .I64 (.EXTEND .S))
      (.mk_num__0 .I32 (.mk_uN bits.toNat))
      (some [.mk_num__0 .I64 (.mk_uN (bits.signExtend 64).toNat)]) := by
  have wf := unsigned_num_wf .I64 _ (bits.signExtend 64).isLt
  have same := extend_signed_bitvec 32 64 bits
  rw [← same] at wf ⊢
  exact .fun_cvtop___case_2 .S _ wf

theorem integer_extendu_relation (bits : BitVec 32) :
    fun_cvtop__ .I32 .I64 (.mk_cvtop___0 .I32 .I64 (.EXTEND .U))
      (.mk_num__0 .I32 (.mk_uN bits.toNat))
      (some [.mk_num__0 .I64 (.mk_uN bits.toNat)]) := by
  have wf := unsigned_num_wf .I64 bits.toNat (by have := bits.isLt; change bits.toNat < 2^64; omega)
  exact .fun_cvtop___case_2 .U _ wf

end Itasca.Runtime.Spec

end

/-! ## IntegerRotate -/

section

namespace Itasca.Runtime.Spec

theorem integer_rotleft_relation (ty : Inn) (bits : BitVec (sizenn (numtype_Inn ty))) (shift : Nat) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty .ROTL)
      (.mk_num__0 ty (.mk_uN bits.toNat)) (.mk_num__0 ty (.mk_uN shift))
      (some [.mk_num__0 ty (.mk_uN (bits.rotateLeft shift).toNat)]) := by
  have wf := unsigned_num_wf ty (bits.rotateLeft shift).toNat (bits.rotateLeft shift).isLt
  have same := SpecExt.Builtins.irotl_bitvec (sizenn (numtype_Inn ty)) bits shift
  cases ty
  · rw [← same] at wf ⊢
    exact .fun_binop__case_20 _ _ wf
  · rw [← same] at wf ⊢
    exact .fun_binop__case_21 _ _ wf

theorem integer_rotright_relation (ty : Inn) (bits : BitVec (sizenn (numtype_Inn ty))) (shift : Nat) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty .ROTR)
      (.mk_num__0 ty (.mk_uN bits.toNat)) (.mk_num__0 ty (.mk_uN shift))
      (some [.mk_num__0 ty (.mk_uN (bits.rotateRight shift).toNat)]) := by
  have wf := unsigned_num_wf ty (bits.rotateRight shift).toNat (bits.rotateRight shift).isLt
  have same := SpecExt.Builtins.irotr_bitvec (sizenn (numtype_Inn ty)) bits shift
  cases ty
  · rw [← same] at wf ⊢
    exact .fun_binop__case_22 _ _ wf
  · rw [← same] at wf ⊢
    exact .fun_binop__case_23 _ _ wf

end Itasca.Runtime.Spec

end

/-! ## SegmentCopy -/

section

namespace Itasca.Runtime.Spec.Segment

/-- Successive writes from an independent source segment. -/
def copyInto {T : Type} [Inhabited T] (before source : List T) (dst src : Nat) : Nat → List T
  | 0 => before
  | count+1 => copyInto (before.set dst source[src]!) source (dst+1) (src+1) count

theorem copy_into_length {T : Type} [Inhabited T] (before source : List T) (dst src count : Nat) :
    (copyInto before source dst src count).length = before.length := by
  induction count generalizing before dst src with
  | zero => rfl
  | succ count ih => simp only [copyInto,ih,List.length_set]

end Itasca.Runtime.Spec.Segment

end

/-! ## SegmentInitCases -/

section

namespace Itasca.Runtime.Spec.Segment
open SpecExt

def i32 (bits : Nat) : admininstr := .CONST .I32 (.mk_num__0 .I32 (.mk_uN bits))
def operands (destination source count : Nat) : List admininstr := [i32 destination, i32 source, i32 count]

theorem index_wf (bits : Nat) (bound : bits < 2^32) : wf_uN 32 (.mk_uN bits) :=
  .uN_case_0 _ _ (by norm_num; omega)

theorem i32_wf (bits : Nat) (bound : bits < 2^32) : wf_admininstr (i32 bits) := by
  apply wf_admininstr.admininstr_case_13
  exact .num__case_0 .I32 .I32 _ (by decide) (index_wf bits bound) rfl

theorem init_config_wf (s : store) (f : frame) (destination source count : Nat) (instruction : admininstr)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count < 2^32)
    (hw : wf_admininstr instruction) : wf_config ⟨⟨s,f⟩,operands destination source count ++ [instruction]⟩ := by
  apply wf_config_make hs hf
  simpa only [operands, Forall, List.mem_cons, List.mem_singleton, List.cons_append, List.nil_append,
    forall_eq_or_imp, forall_eq, List.not_mem_nil, false_implies, forall_const, and_true] using And.intro (i32_wf destination hd) (And.intro (i32_wf source hi) (And.intro (i32_wf count hn) hw))

theorem table_init_trap (s : store) (f : frame) (destination source count tableIndex elementIndex : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count < 2^32)
    (ht : tableIndex < 2^32) (he : elementIndex < 2^32)
    (outside : source + count > (fun_elem ⟨s,f⟩ (.mk_uN elementIndex)).REFS.length ∨
      destination + count > (fun_table ⟨s,f⟩ (.mk_uN tableIndex)).REFS.length) :
    StepH ⟨⟨s,f⟩,operands destination source count ++ [.TABLE_INIT (.mk_uN tableIndex) (.mk_uN elementIndex)]⟩ []
      ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input := init_config_wf s f destination source count _ hs hf hd hi hn
    (.admininstr_case_54 _ _ (index_wf tableIndex ht) (index_wf elementIndex he))
  have output : wf_config ⟨⟨s,f⟩,[.TRAP]⟩ := wf_config_make hs hf (by simp [Forall]; exact .admininstr_case_73)
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  apply Step_read.table_init_trap
  · simp [proj_num__0]
  · simp [proj_num__0]
  · simpa only [proj_num__0, Option.get!, proj_uN_0] using outside
  · exact input
  · exact .admininstr_case_73

theorem table_init_zero (s : store) (f : frame) (destination source tableIndex elementIndex : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32)
    (ht : tableIndex < 2^32) (he : elementIndex < 2^32)
    (inside : source ≤ (fun_elem ⟨s,f⟩ (.mk_uN elementIndex)).REFS.length ∧
      destination ≤ (fun_table ⟨s,f⟩ (.mk_uN tableIndex)).REFS.length) :
    StepH ⟨⟨s,f⟩,operands destination source 0 ++ [.TABLE_INIT (.mk_uN tableIndex) (.mk_uN elementIndex)]⟩ []
      ⟨⟨s,f⟩,[]⟩ := by
  have input := init_config_wf s f destination source 0 _ hs hf hd hi (by norm_num)
    (.admininstr_case_54 _ _ (index_wf tableIndex ht) (index_wf elementIndex he))
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simp [Forall]))
  apply Step_read.table_init_zero
  · simp [proj_num__0]
  · simp [proj_num__0]
  · simpa only [proj_num__0, Option.get!, proj_uN_0, Nat.add_zero] using inside
  · rfl
  · exact input


theorem memory_init_trap (s : store) (f : frame) (destination source count dataIndex : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32) (hn : count < 2^32)
    (he : dataIndex < 2^32)
    (outside : source + count > (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES.length ∨
      destination + count > (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepH ⟨⟨s,f⟩,operands destination source count ++ [.MEMORY_INIT (.mk_uN dataIndex)]⟩ []
      ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input := init_config_wf s f destination source count _ hs hf hd hi hn
    (.admininstr_case_66 _ (index_wf dataIndex he))
  have output : wf_config ⟨⟨s,f⟩,[.TRAP]⟩ := wf_config_make hs hf (by simp [Forall]; exact .admininstr_case_73)
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  apply Step_read.memory_init_trap
  · simp [proj_num__0]
  · simp [proj_num__0]
  · simpa only [proj_num__0, Option.get!, proj_uN_0] using outside
  · exact input
  · exact .admininstr_case_73

  · exact index_wf 0 (by norm_num)

theorem memory_init_zero (s : store) (f : frame) (destination source dataIndex : Nat)
    (hs : wf_store s) (hf : wf_frame f) (hd : destination < 2^32) (hi : source < 2^32)
    (he : dataIndex < 2^32)
    (inside : source ≤ (fun_data ⟨s,f⟩ (.mk_uN dataIndex)).BYTES.length ∧
      destination ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length) :
    StepH ⟨⟨s,f⟩,operands destination source 0 ++ [.MEMORY_INIT (.mk_uN dataIndex)]⟩ []
      ⟨⟨s,f⟩,[]⟩ := by
  have input := init_config_wf s f destination source 0 _ hs hf hd hi (by norm_num)
    (.admininstr_case_66 _ (index_wf dataIndex he))
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_make hs hf (by simp [Forall]))
  apply Step_read.memory_init_zero
  · simp [proj_num__0]
  · simp [proj_num__0]
  · simpa only [proj_num__0, Option.get!, proj_uN_0, Nat.add_zero] using inside
  · rfl
  · exact input


end Itasca.Runtime.Spec.Segment

end

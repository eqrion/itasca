import Exec.Abs.Numeric.OperandsCore
import Exec.Abs.Sim.Int
import Exec.Spec.IntegerExtend
import SpecExt.Builtins.Counts

namespace Itasca.Runtime.Abs.Numeric
open SpecExt Itasca.Runtime.Spec SpecExt.Builtins

theorem unary_relation (ty : Inn) (op : unop_Inn) (bits : BitVec (sizenn (numtype_Inn ty))) :
    fun_unop_ (numtype_Inn ty) (.mk_unop__0 ty op)
      (.mk_num__0 ty (.mk_uN bits.toNat))
      (some [.mk_num__0 ty (.mk_uN (unary ty op bits).toNat)]) := by
  have wf := unsigned_num_wf ty _ (unary ty op bits).isLt
  cases op with
  | EXTEND small => exact extend_unary_bitvec ty small bits
  | CLZ =>
    have bound : leadingZeros (integerBits (sizenn (numtype_Inn ty)) bits.toNat) ≤ sizenn (numtype_Inn ty) := by
      simpa only [integerBits_length] using leadingZeros_le_length (integerBits (sizenn (numtype_Inn ty)) bits.toNat)
    have small : leadingZeros (integerBits (sizenn (numtype_Inn ty)) bits.toNat) < 2 ^ sizenn (numtype_Inn ty) := by
      exact lt_of_le_of_lt bound (by cases ty <;> decide)
    simp only [unary, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at wf ⊢
    cases ty
    · exact .fun_unop__case_0 _ wf
    · exact .fun_unop__case_1 _ wf
  | CTZ =>
    have bound : leadingZeros (integerBits (sizenn (numtype_Inn ty)) bits.toNat).reverse ≤ sizenn (numtype_Inn ty) := by
      simpa only [List.length_reverse, integerBits_length] using leadingZeros_le_length (integerBits (sizenn (numtype_Inn ty)) bits.toNat).reverse
    have small : leadingZeros (integerBits (sizenn (numtype_Inn ty)) bits.toNat).reverse < 2 ^ sizenn (numtype_Inn ty) := by
      exact lt_of_le_of_lt bound (by cases ty <;> decide)
    simp only [unary, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at wf ⊢
    cases ty
    · exact .fun_unop__case_2 _ wf
    · exact .fun_unop__case_3 _ wf
  | POPCNT =>
    have bound := population_bits_le (sizenn (numtype_Inn ty)) bits.toNat
    have small : population (integerBits (sizenn (numtype_Inn ty)) bits.toNat) < 2 ^ sizenn (numtype_Inn ty) := by
      exact lt_of_le_of_lt bound (by cases ty <;> decide)
    simp only [unary, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at wf ⊢
    cases ty
    · exact .fun_unop__case_4 _ wf
    · exact .fun_unop__case_5 _ wf

theorem unary_pure (ty : Inn) (op : unop_Inn) (bits : BitVec (sizenn (numtype_Inn ty))) :
    Step_pure [admininstr_val (integerVal ty bits.toNat),
      admininstr_instr (.UNOP (numtype_Inn ty) (.mk_unop__0 ty op))]
      [admininstr_val (integerVal ty (unary ty op bits).toNat)] := by
  apply Step_pure.unop_val (numtype_Inn ty) (.mk_num__0 ty (.mk_uN bits.toNat))
    (.mk_unop__0 ty op) (.mk_num__0 ty (.mk_uN (unary ty op bits).toNat))
    (some [.mk_num__0 ty (.mk_uN (unary ty op bits).toNat)])
  · exact unary_relation ty op bits
  · simp
  · simp
  · simp
  · exact wf_admininstr_val (integer_val_wf ty _ (word_bound ty bits))
  · exact wf_admininstr_instr (.instr_case_14 _ _ (.unop__case_0 _ _ _ rfl))
  · exact wf_admininstr_val (integer_val_wf ty _ (word_bound ty (unary ty op bits)))

end Itasca.Runtime.Abs.Numeric

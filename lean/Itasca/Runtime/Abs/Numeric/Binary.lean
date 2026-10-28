import Itasca.Runtime.Abs.Numeric.Unary
import Itasca.Runtime.Spec.IntegerBits
import Itasca.Runtime.Spec.IntegerRotate
import Itasca.Runtime.Spec.IntegerShift

namespace Itasca.Runtime.Abs.Numeric
open SpecExt Itasca.Runtime.Spec

theorem binary_relation (ty : Inn) (op : binop_Inn)
    (a b : BitVec (sizenn (numtype_Inn ty))) :
    fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty op)
      (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat))
      (some (binaryNumbers ty (binary ty op a b))) := by
  have width : integerWidth ty = sizenn (numtype_Inn ty) := by cases ty <;> rfl
  cases op with
  | ADD =>
    simpa only [binary, binaryNumbers, BitVec.toNat_add, width] using integer_add_relation ty a.toNat b.toNat
  | SUB =>
    have reorder : 2 ^ sizenn (numtype_Inn ty) - b.toNat + a.toNat = a.toNat + 2 ^ sizenn (numtype_Inn ty) - b.toNat := by have := b.isLt; omega
    simpa only [binary, binaryNumbers, BitVec.toNat_sub, width, reorder] using integer_sub_relation ty a.toNat b.toNat (word_bound ty b)
  | MUL =>
    have wf := unsigned_num_wf ty (a * b).toNat (a * b).isLt
    simp only [binary, binaryNumbers, BitVec.toNat_mul] at wf ⊢
    cases ty
    · exact .fun_binop__case_4 _ _ _ (.fun_imul__case_0 _ _ _ (unsigned_wf_of_lt _ _ (a * b).isLt)) wf
    · exact .fun_binop__case_5 _ _ _ (.fun_imul__case_0 _ _ _ (unsigned_wf_of_lt _ _ (a * b).isLt)) wf
  | DIV sign =>
    cases sign with
    | U =>
      simp only [binary]
      split
      · rename_i zero; simp only [binaryNumbers]; simpa [zero] using integer_divu_zero_relation ty a.toNat
      · rename_i nonzero
        simpa [binaryNumbers, BitVec.toNat_udiv] using integer_divu_relation ty a.toNat b.toNat a.isLt nonzero
    | S =>
      simp only [binary]
      split
      · rename_i zero; simp only [binaryNumbers]; simpa [zero] using integer_divs_zero_relation ty a.toNat
      · split
        · rename_i overflow
          rcases overflow with ⟨rfl, rfl⟩
          cases ty
          · exact integer_divs_trap_relation .I32 _ _ signed_div_overflow32
          · exact integer_divs_trap_relation .I64 _ _ signed_div_overflow64
        · rename_i nonzero regular
          exact integer_divs_relation ty a b (a.sdiv b) nonzero
            (BitVec.toInt_sdiv_of_ne_or_ne a b (by tauto))
  | REM sign =>
    cases sign with
    | U =>
      simp only [binary]
      split
      · rename_i zero; simp only [binaryNumbers]; simpa [zero] using integer_remu_zero_relation ty a.toNat
      · rename_i nonzero
        simpa [binaryNumbers, BitVec.toNat_umod] using integer_remu_relation ty a.toNat b.toNat a.isLt nonzero
    | S =>
      simp only [binary]
      split
      · rename_i zero; simp only [binaryNumbers]; simpa [zero] using integer_rems_zero_relation ty a.toNat
      · rename_i nonzero
        exact integer_rems_relation ty a b (a.srem b) nonzero (BitVec.toInt_srem a b)
  | AND =>
    have bound : (a.toNat &&& b.toNat) < 2 ^ sizenn (numtype_Inn ty) := by
      simpa only [BitVec.toNat_and] using (a &&& b).isLt
    simpa only [binary, binaryNumbers, SpecExt.Builtins.iand_value, BitVec.toNat_and, Nat.mod_eq_of_lt bound] using integer_and_relation ty a.toNat b.toNat
  | OR =>
    have bound : (a.toNat ||| b.toNat) < 2 ^ sizenn (numtype_Inn ty) := by
      simpa only [BitVec.toNat_or] using (a ||| b).isLt
    simpa only [binary, binaryNumbers, SpecExt.Builtins.ior_value, BitVec.toNat_or, Nat.mod_eq_of_lt bound] using integer_or_relation ty a.toNat b.toNat
  | XOR =>
    have bound : (a.toNat ^^^ b.toNat) < 2 ^ sizenn (numtype_Inn ty) := by
      simpa only [BitVec.toNat_xor] using (a ^^^ b).isLt
    simpa only [binary, binaryNumbers, SpecExt.Builtins.ixor_value, BitVec.toNat_xor, Nat.mod_eq_of_lt bound] using integer_xor_relation ty a.toNat b.toNat
  | SHL => simpa [binary, binaryNumbers, Nat.shiftLeft_eq] using integer_shl_relation ty a.toNat b.toNat
  | SHR sign =>
    cases sign with
    | U => simpa [binary, binaryNumbers, Nat.shiftRight_eq_div_pow] using integer_shru_relation ty a.toNat b.toNat a.isLt
    | S => exact integer_shrs_relation ty a b.toNat
  | ROTL => exact integer_rotleft_relation ty a b.toNat
  | ROTR => exact integer_rotright_relation ty a b.toNat

end Itasca.Runtime.Abs.Numeric

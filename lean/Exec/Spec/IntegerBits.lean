import Exec.Spec.IntegerDiv
import SpecExt.Builtins.Bitwise

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

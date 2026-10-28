import SpecExt.Builtins.Rotations
import Exec.Spec.IntegerDiv

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

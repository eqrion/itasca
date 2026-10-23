import Exec.Abs.Numeric.Unary
import Exec.Spec.IntegerCompareSigned

namespace Exec.Abs.Numeric
open SpecExt Exec.Spec

theorem compare_bound (ty : Inn) (op : relop_Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    compare ty op a b < 2 ^ integerWidth .I32 := by
  unfold compare
  split <;> split <;> decide

theorem compare_relation (ty : Inn) (op : relop_Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty op)
      (.mk_num__0 ty (.mk_uN a.toNat)) (.mk_num__0 ty (.mk_uN b.toNat))
      (some (.mk_num__0 .I32 (.mk_uN (compare ty op a b)))) := by
  cases op with
  | EQ => exact integer_eq_relation ty _ _
  | NE => exact integer_ne_relation ty _ _
  | LT sign => cases sign with
    | U => exact integer_ltu_relation ty _ _
    | S => exact integer_lts_relation ty a b
  | GT sign => cases sign with
    | U => exact integer_gtu_relation ty _ _
    | S => exact integer_gts_relation ty a b
  | LE sign => cases sign with
    | U => exact integer_leu_relation ty _ _
    | S => exact integer_les_relation ty a b
  | GE sign => cases sign with
    | U => exact integer_geu_relation ty _ _
    | S => exact integer_ges_relation ty a b

theorem compare_pure (ty : Inn) (op : relop_Inn) (a b : BitVec (sizenn (numtype_Inn ty))) :
    Step_pure [admininstr_val (integerVal ty a.toNat), admininstr_val (integerVal ty b.toNat),
      admininstr_instr (.RELOP (numtype_Inn ty) (.mk_relop__0 ty op))]
      [admininstr_val (integerVal .I32 (compare ty op a b))] :=
  integer_relop_pure ty op a.toNat b.toNat _ (word_bound ty a) (word_bound ty b)
    (compare_bound ty op a b) (compare_relation ty op a b)

end Exec.Abs.Numeric

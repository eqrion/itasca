import Itasca.Runtime.Spec.IntegerSigned

namespace Itasca.Runtime.Spec

theorem signed_deterministic {width bits : Nat} {left right : Int}
    (first : fun_signed_ width bits left) (second : fun_signed_ width bits right) : left = right := by
  cases first <;> cases second <;> first | rfl | omega

theorem inv_signed_deterministic {width : Nat} {bits : Int} {left right : Nat}
    (first : fun_inv_signed_ width bits left) (second : fun_inv_signed_ width bits right) : left = right := by
  cases first <;> cases second <;> first | rfl | omega

theorem idiv_deterministic {width : Nat} {sign : sx} {a b : uN} {left right : Option uN}
    (first : fun_idiv_ width sign a b left) (second : fun_idiv_ width sign a b right) : left = right := by
  cases first <;> cases second
  all_goals first | rfl | simp_all only [proj_uN_0, ne_eq, not_true_eq_false]
  all_goals grind only [signed_deterministic, inv_signed_deterministic]

theorem irem_deterministic {width : Nat} {sign : sx} {a b : uN} {left right : Option uN}
    (first : fun_irem_ width sign a b left) (second : fun_irem_ width sign a b right) : left = right := by
  cases first <;> cases second
  all_goals first | rfl | simp_all only [proj_uN_0, ne_eq, not_true_eq_false]
  all_goals grind only [signed_deterministic, inv_signed_deterministic]
theorem integer_binop_deterministic {ty : Inn} {op : binop_Inn} {a b : uN}
    {left right : List num_}
    (first : fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty op) (.mk_num__0 ty a) (.mk_num__0 ty b) (some left))
    (second : fun_binop_ (numtype_Inn ty) (.mk_binop__0 ty op) (.mk_num__0 ty a) (.mk_num__0 ty b) (some right)) : left = right := by
  cases ty <;> cases first <;> cases second
  all_goals first | rfl | skip
  all_goals try casesm* fun_iadd_ .., fun_isub_ .., fun_imul_ ..
  all_goals first | rfl | grind only [idiv_deterministic, irem_deterministic]
theorem integer_unop_deterministic {ty : Inn} {op : unop_Inn} {a : uN}
    {left right : List num_}
    (first : fun_unop_ (numtype_Inn ty) (.mk_unop__0 ty op) (.mk_num__0 ty a) (some left))
    (second : fun_unop_ (numtype_Inn ty) (.mk_unop__0 ty op) (.mk_num__0 ty a) (some right)) : left = right := by
  cases ty <;> cases first <;> cases second <;> rfl

theorem integer_relop_deterministic {ty : Inn} {op : relop_Inn} {a b : uN}
    {left right : num_}
    (first : fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty op) (.mk_num__0 ty a) (.mk_num__0 ty b) (some left))
    (second : fun_relop_ (numtype_Inn ty) (.mk_relop__0 ty op) (.mk_num__0 ty a) (.mk_num__0 ty b) (some right)) : left = right := by
  cases ty <;> cases first <;> cases second
  all_goals try casesm* fun_ieq_ .., fun_ine_ .., fun_ilt_ .., fun_igt_ .., fun_ile_ .., fun_ige_ ..
  all_goals first | rfl | grind only [signed_deterministic]

theorem integer_cvtop_deterministic {source target : Inn} {op : cvtop__Inn_1_Inn_2} {a : uN}
    {left right : List num_}
    (first : fun_cvtop__ (numtype_Inn source) (numtype_Inn target) (.mk_cvtop___0 source target op) (.mk_num__0 source a) (some left))
    (second : fun_cvtop__ (numtype_Inn source) (numtype_Inn target) (.mk_cvtop___0 source target op) (.mk_num__0 source a) (some right)) : left = right := by
  cases source <;> cases target <;> cases first <;> cases second <;> rfl
end Itasca.Runtime.Spec

import Exec.Spec.ListRelations
import Exec.Spec.Typing.ValueConfigTyping

/-! Semantic values have unique non-bottom types. Result subtyping retains
actual value typing and cannot change the represented value kinds. -/

namespace Exec.Spec
open SpecExt

def semanticValueType : val → valtype
  | .CONST type _ => valtype_numtype type
  | .VCONST type _ => valtype_vectype type
  | .REF_NULL type => valtype_reftype type
  | .REF_FUNC_ADDR _ => .FUNCREF
  | .REF_HOST_ADDR _ => .EXTERNREF

theorem val_ok_type {s : store} {value : val} {type : valtype} (typed : Val_ok s value type) :
    type = semanticValueType value := by
  cases typed with
  | numtype => rfl
  | vectype => rfl
  | reftype r type typed _ => cases typed <;> rfl

theorem semanticValueType_not_bot (value : val) : semanticValueType value ≠ .BOT := by
  cases value
  all_goals try casesm* numtype, vectype, reftype
  all_goals simp [semanticValueType,valtype_numtype,valtype_vectype,valtype_reftype]

theorem val_ok_type_unique {s : store} {value : val} {left right : valtype}
    (first : Val_ok s value left) (second : Val_ok s value right) : left = right :=
  (val_ok_type first).trans (val_ok_type second).symm

theorem val_ok_subtype {s : store} {value : val} {left right : valtype}
    (typed : Val_ok s value left) (sub : Valtype_sub left right) : Val_ok s value right := by
  cases sub with
  | refl => exact typed
  | bot => exact False.elim (semanticValueType_not_bot value (val_ok_type typed).symm)

theorem resulttype_sub_iff {left right : List valtype} :
    Resulttype_sub (.mk_list left) (.mk_list right) ↔ List.Forall₂ Valtype_sub left right := by
  constructor
  · intro sub
    cases sub with
    | mk_Resulttype_sub _ _ count paired => exact (forall₂_iff_list _ _ _ count).mp paired
  · intro sub
    have count : left.length = right.length := by
      induction sub with
      | nil => rfl
      | cons _ _ ih => simp [ih]
    exact .mk_Resulttype_sub left right count ((forall₂_iff_list _ _ _ count).mpr sub)

theorem valtype_sub_trans {first middle last : valtype}
    (left : Valtype_sub first middle) (right : Valtype_sub middle last) : Valtype_sub first last := by
  cases left with
  | refl => exact right
  | bot => exact .bot _

theorem resulttype_sub_refl (types : List valtype) : Resulttype_sub (.mk_list types) (.mk_list types) := by
  apply resulttype_sub_iff.mpr
  induction types with
  | nil => exact .nil
  | cons type types ih => exact .cons (.refl type) ih

theorem resulttype_sub_trans {first middle last : List valtype}
    (left : Resulttype_sub (.mk_list first) (.mk_list middle))
    (right : Resulttype_sub (.mk_list middle) (.mk_list last)) :
    Resulttype_sub (.mk_list first) (.mk_list last) := by
  have before := resulttype_sub_iff.mp left
  have after := resulttype_sub_iff.mp right
  clear left right
  apply resulttype_sub_iff.mpr
  induction before generalizing last with
  | nil => cases after; exact .nil
  | cons head tail ih =>
    cases after with
    | cons second rest => exact .cons (valtype_sub_trans head second) (ih rest)

theorem resultsTyped_subtype {s : store} {types target : List valtype} {values : List val}
    (typed : ResultsTyped s types values) (sub : Resulttype_sub (.mk_list types) (.mk_list target)) :
    ResultsTyped s target values := by
  have compatible := resulttype_sub_iff.mp sub
  clear sub
  induction typed generalizing target with
  | nil => cases compatible; exact .nil
  | cons head tail ih =>
    cases compatible with
    | cons second rest => exact .cons (val_ok_subtype head second) (ih rest)

theorem resultsTyped_types_unique {s : store} {left right : List valtype} {values : List val}
    (first : ResultsTyped s left values) (second : ResultsTyped s right values) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons other rest => exact congrArg₂ List.cons (val_ok_type_unique head other) (ih rest)

/-- Subtyping of actual returned values cannot introduce bottom types or
change their represented scalar/reference kinds. -/
theorem resultsTyped_subtype_eq {s : store} {types target : List valtype} {values : List val}
    (typed : ResultsTyped s types values) (sub : Resulttype_sub (.mk_list types) (.mk_list target)) : types = target :=
  resultsTyped_types_unique typed (resultsTyped_subtype typed sub)

end Exec.Spec


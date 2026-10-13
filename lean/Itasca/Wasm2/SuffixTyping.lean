import Itasca.Wasm2.Suffix
import Itasca.Spec.TypingInversion
import Itasca.Handler.Select

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- The least types of the top `n` operands, padding implicit unreachable
operands with bottom. This depends on arity alone, never on a target's types. -/
def topTypes : List code.StackType → Nat → List valtype
  | _, 0 => []
  | [], n + 1 => .BOT :: topTypes [] n
  | v :: vs, n + 1 => StackSemantics.selectedType v :: topTypes vs n

@[simp] theorem topTypes.length (vs : List code.StackType) (n : Nat) :
    (topTypes vs n).length = n := by
  induction n generalizing vs with
  | zero => simp [topTypes]
  | succ n ih => cases vs <;> simp [topTypes, ih]

theorem Fits.subtypes {poly : Bool} {vs : List code.StackType} {ts : List types.ValueType}
    (h : Fits poly vs ts) :
    List.Forall₂ Valtype_sub (topTypes vs ts.length) (ts.map Translate.valueType) := by
  induction ts generalizing vs with
  | nil => exact .nil
  | cons t ts ih =>
    cases vs with
    | nil =>
      have hp : poly = true := h
      subst poly
      exact .cons (.bot _) (ih (Fits.unreachable ts))
    | cons v vs =>
      exact .cons (StackSemantics.selectedType_sub h.1) (ih h.2)

theorem Fits.realizes {poly : Bool} {vs : List code.StackType} {ts : List types.ValueType}
    (h : Fits poly vs ts) :
    ∃ front, Sequence.Realizes poly vs.reverse
      (front ++ (topTypes vs ts.length).reverse) := by
  induction ts generalizing vs with
  | nil =>
    refine ⟨Sequence.stackTypes vs.reverse, ?_⟩
    simpa [topTypes] using Sequence.realizes_default poly vs.reverse
  | cons t ts ih =>
    cases vs with
    | nil =>
      have hp : poly = true := h
      subst poly
      exact ⟨[], Sequence.realizes_polymorphic_empty _⟩
    | cons v vs =>
      obtain ⟨front, hf⟩ := ih h.2
      refine ⟨front, ?_⟩
      simpa [topTypes, List.append_assoc] using
        hf.snoc v (StackSemantics.selectedType v) (StackSemantics.selectedType_accepts v)

/-- A declaratively compatible stack implies the independent suffix relation;
the prefix may contain any operands belonging to the current frame. -/
theorem Fits.of_realizes {poly : Bool} {vs : List code.StackType}
    {ts : List types.ValueType} (front : List valtype)
    (h : Sequence.Realizes poly vs.reverse
      (front ++ (ts.map Translate.valueType).reverse)) : Fits poly vs ts := by
  induction ts generalizing vs front with
  | nil => exact Fits.nil _ _
  | cons t ts ih =>
    cases vs with
    | nil =>
      change poly = true
      cases poly with
      | true => rfl
      | false =>
        have hn := (Sequence.realizes_empty _).mp h
        simp at hn
    | cons v vs =>
      have h' : Sequence.Realizes poly (vs.reverse ++ [v])
          ((front ++ (ts.map Translate.valueType).reverse) ++ [Translate.valueType t]) := by
        simpa [List.append_assoc] using h
      obtain ⟨pre, u, he, hp, hv⟩ := h'.snoc_inv
      have he' : front ++ (ts.map Translate.valueType).reverse = pre ∧
          Translate.valueType t = u := by
        simpa only [List.singleton_inj] using (List.append_inj' he (by simp))
      obtain ⟨rfl, rfl⟩ := he'
      exact ⟨hv, ih front hp⟩

/-- All equally sized accepted targets admit the same least operand vector.
This is the common-subtype premise in the generated Wasm 2.0 `br_table` rule. -/
theorem Suffix.common_subtype {st : code.OpIterState} {ts : List types.ValueType}
    (h : Suffix st ts) :
    Resulttype_sub
      (.mk_list (topTypes (st.vals.val.drop (Control.base st).val).reverse ts.length).reverse)
      (.mk_list (ts.map Translate.valueType)) ∧
    ∃ front, Sequence.Realizes (Control.polymorphic st)
      (st.vals.val.drop (Control.base st).val)
      (front ++ (topTypes (st.vals.val.drop (Control.base st).val).reverse ts.length).reverse) := by
  have ht := Fits.subtypes h
  have hr := Fits.realizes h
  constructor
  · apply DeclarativeComplete.result_sub_iff.mpr
    simpa using List.rel_reverse ht
  · simpa using hr

theorem Suffix.of_realizes {st : code.OpIterState} {ts : List types.ValueType}
    (front : List valtype)
    (h : Sequence.Realizes (Control.polymorphic st)
      (st.vals.val.drop (Control.base st).val)
      (front ++ ts.map Translate.valueType)) : Suffix st ts := by
  apply Fits.of_realizes front
  simpa using h

end Itasca.Wasm2

namespace Itasca

/-- Exact declarative contract for the suffix checker. The witnesses use
SpecTec's generated subtyping judgment and the independent stack realization;
they do not mention a validator execution. -/
theorem code.check_suffix.wasm_spec (st : code.OpIterState) (env : module.Env)
    (view : signature.ResultType) (hshape : Control.Shape st) :
    code.check_suffix st env view ⦃ r =>
      r = .Ok () ↔ ∃ ts front common,
        Wasm2.resolve env view = some ts ∧
        Sequence.Realizes (Control.polymorphic st)
          (st.vals.val.drop (Control.base st).val) (front ++ common) ∧
        Resulttype_sub (.mk_list common) (.mk_list (ts.map Translate.valueType)) ⦄ := by
  apply WP.spec_mono (code.check_suffix.spec st env view hshape)
  intro r hr
  constructor
  · intro hok
    obtain ⟨ts, ht, hs⟩ := hr.mp hok
    obtain ⟨hsub, front, hreal⟩ := hs.common_subtype
    exact ⟨ts, front, _, ht, hreal, hsub⟩
  · rintro ⟨ts, front, common, ht, hreal, hsub⟩
    apply hr.mpr
    refine ⟨ts, ht, Wasm2.Suffix.of_realizes front ?_⟩
    exact DeclarativeComplete.realizes_mono hreal
      (DeclarativeComplete.result_sub_append (DeclarativeComplete.result_sub_refl front) hsub)

/-- The generated common-subtype premise of a branch table suffices for each
actual suffix check, without requiring equality of the target signatures. -/
theorem code.check_suffix.complete_of_subtype (st : code.OpIterState) (env : module.Env)
    (view : signature.ResultType) (ts : List types.ValueType) (front common : List valtype)
    (hshape : Control.Shape st) (hts : Wasm2.resolve env view = some ts)
    (hr : Sequence.Realizes (Control.polymorphic st)
      (st.vals.val.drop (Control.base st).val) (front ++ common))
    (hsub : Resulttype_sub (.mk_list common) (.mk_list (ts.map Translate.valueType))) :
    code.check_suffix st env view = .ok (.Ok ()) := by
  apply code.check_suffix.complete st env view ts hshape hts
  apply Wasm2.Suffix.of_realizes front
  exact DeclarativeComplete.realizes_mono hr
    (DeclarativeComplete.result_sub_append (DeclarativeComplete.result_sub_refl front) hsub)

end Itasca

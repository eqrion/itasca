import Itasca.Handler.RawControl
import Itasca.Wasm2.EmptyVisitorLoop
import Itasca.Spec.TypingInversion
import Itasca.Handler.Select

/-!
Sections, each formerly its own module: FixedOperands, SuffixTyping.
-/

/-! ## FixedOperands -/

section

/-!
# Fixed-arity operand checking

`Wasm2.Simd.readFixed` models the pop-then-push operand checking of handlers with a fixed
signature, independently of opcode dispatch. `readFixed.segment` gives its totality and stack
effect (`FixedEffect`), `readFixed.complete` shows that it accepts every stack that fits the
inputs, and `FixedEffect.wasm2_prefix` extends a `TypedPrefix` by a typed instruction.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

/-- Fixed arity operand checking, normalized independently of opcode dispatch.
Inputs are listed in pop order; there is at most one concrete result. -/
def readFixed (st : code.OpIterState) (inputs : List wasm_types.ValueType)
    (output : Option wasm_types.ValueType) :
    Result (core.result.Result Unit error.OpError × code.OpIterState) := do
  match inputs with
  | [] =>
      match output with
      | none => .ok (.Ok (), st)
      | some ty =>
          let s ← code.push_val st (.Val ty)
          .ok (.Ok (), s)
  | ty :: rest =>
      let (r, s) ← code.pop_with_type st ty
      match r with
      | .Err e => .ok (.Err e, s)
      | .Ok _ => readFixed s rest output

/-- The spec input types for pop-order `inputs`, in stack order. -/
def inputTypes (inputs : List wasm_types.ValueType) : List valtype :=
  inputs.reverse.map Translate.valueType

/-- The spec result types of an optional output. -/
def outputTypes (output : Option wasm_types.ValueType) : List valtype :=
  output.toList.map Translate.valueType

/-- Every interpretation of the resulting stack has the declared fixed effect. -/
def FixedEffect (poly : Bool) (before : List code.StackType)
    (inputs : List wasm_types.ValueType) (output : Option wasm_types.ValueType)
    (after : List code.StackType) : Prop :=
  ∀ ts, Sequence.Realizes poly after ts → ∃ front,
    ts = front ++ outputTypes output ∧
    Sequence.Realizes poly before (front ++ inputTypes inputs)

/-- A typed instruction with the fixed effect extends a typed prefix. -/
theorem FixedEffect.wasm2_prefix {poly before inputs output after}
    (h : FixedEffect poly before inputs output after)
    (C : context) (hC : wf_context C) (initial : List valtype) (ops : List instr) (op : instr)
    (hp : TypedPrefix C initial ops poly before) (hw : wf_instr op)
    (ht : Instr_ok C op (.mk_functype (.mk_list (inputTypes inputs)) (.mk_list (outputTypes output)))) :
    TypedPrefix C initial (ops ++ [op]) poly after := by
  apply hp.append hC op hw
  intro ts hs
  obtain ⟨front, rfl, hb⟩ := h ts hs
  exact ⟨front ++ inputTypes inputs, hb,
    .frame C [op] front _ _ (.instr C op _ _ ht hC hw) hC (by simpa [Forall] using hw)⟩

/-- `readFixed` is total, leaves the control frames and cursor unchanged, and on success has the
fixed stack effect. -/
theorem readFixed.segment (st : code.OpIterState) (inputs : List wasm_types.ValueType)
    (output : Option wasm_types.ValueType) (outer segment : List code.StackType)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    readFixed st inputs output ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ after, r.2.vals.val = outer ++ after ∧ after.length ≤ segment.length + 1 ∧
        (r.1 = .Ok () → FixedEffect (Control.polymorphic st) segment inputs output after) ⦄ := by
  induction inputs generalizing st segment with
  | nil =>
      cases output with
      | none =>
          rw [readFixed, WP.spec_ok]
          refine ⟨rfl, rfl, segment, hv, by omega, ?_⟩
          intro _ ts hs
          exact ⟨ts, by simp [outputTypes], by simpa [inputTypes] using hs⟩
      | some ty =>
          obtain ⟨s, hr, hvals, hc, hp⟩ := WP.spec_imp_exists (code.push_val.spec st (.Val ty) hsize)
          rw [readFixed, hr, bind_ok, WP.spec_ok]
          refine ⟨hc, hp, segment ++ [.Val ty], by simpa [hv, List.append_assoc] using hvals,
            by simp, ?_⟩
          intro _ ts hs
          obtain ⟨front, u, rfl, hfront, hu⟩ := hs.snoc_inv
          change u = Translate.valueType ty at hu
          subst u
          exact ⟨front, by simp [outputTypes], by simpa [inputTypes] using hfront⟩
  | cons ty rest ih =>
      obtain ⟨⟨r, s⟩, hr, hc, hp, popped, hpv, hpop⟩ := WP.spec_imp_exists
        (code.pop_with_type.segment st outer segment ty hv hb)
      dsimp only at hc hp hpv hpop
      have hlen := hpop.length
      rw [WP.spec_equiv_exists]
      cases r with
      | Err e =>
          exact ⟨(.Err e, s), by simp [readFixed, hr], hc, hp, popped, hpv, by omega, by simp⟩
      | Ok t =>
          have hb' : (Control.base s).val = outer.length := by simpa [Control.base, hc] using hb
          have hcap : s.vals.val.length < Usize.max := by
            simp only [hv, hpv, List.length_append] at *
            omega
          obtain ⟨⟨res, out⟩, ho, hctrls, hpos, after, hav, hal, heffect⟩ :=
            WP.spec_imp_exists (ih s popped hpv hb' hcap)
          dsimp only at hctrls hpos hav hal heffect
          refine ⟨(res, out), by simp [readFixed, hr, ho],
            hctrls.trans hc, hpos.trans hp, after, hav, by omega, ?_⟩
          intro hok ts hs
          obtain ⟨front, hf, hh⟩ := heffect hok ts (by simpa [Control.polymorphic, hc] using hs)
          refine ⟨front, hf, ?_⟩
          have hbefore := hpop.realizes (front ++ inputTypes rest)
            (by simpa [Control.polymorphic, hc] using hh)
          simpa [inputTypes, List.append_assoc] using hbefore

/-- The fixed checker accepts every stack interpretation with its principal inputs. -/
theorem readFixed.complete (st : code.OpIterState) (inputs : List wasm_types.ValueType)
    (output : Option wasm_types.ValueType) (outer segment : List code.StackType) (front : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st) segment (front ++ inputTypes inputs)) :
    ∃ s after, readFixed st inputs output = .ok (.Ok (), s) ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ s.vals.val = outer ++ after ∧
      after.length ≤ segment.length + 1 ∧
      Sequence.Realizes (Control.polymorphic st) after (front ++ outputTypes output) := by
  induction inputs generalizing st segment with
  | nil =>
      cases output with
      | none => exact ⟨st, segment, rfl, rfl, rfl, hv, by omega, by simpa [inputTypes, outputTypes] using ht⟩
      | some ty =>
          obtain ⟨s, hr, hvals, hc, hp⟩ := WP.spec_imp_exists (code.push_val.spec st (.Val ty) hsize)
          exact ⟨s, segment ++ [.Val ty], by simp [readFixed, hr], hc, hp,
            by simpa [hv, List.append_assoc] using hvals, by simp,
            by simpa [inputTypes, outputTypes] using ht.snoc (.Val ty) (Translate.valueType ty) rfl⟩
  | cons ty rest ih =>
      obtain ⟨_, s, popped, hr, hc, hp, hpv, hlen, _, hpop⟩ := code.pop_with_type.complete
        st outer segment (front ++ inputTypes rest) ty hv hb
          (by simpa [inputTypes, List.append_assoc] using ht)
      have hcap : s.vals.val.length < Usize.max := by
        simp only [hv, hpv, List.length_append] at *
        omega
      obtain ⟨out, after, ho, hoc, hop, hov, hol, hot⟩ := ih s popped hpv
        (by simpa [Control.base, hc] using hb) hcap (by simpa [Control.polymorphic, hc] using hpop)
      exact ⟨out, after, by simp [readFixed, hr, ho], hoc.trans hc, hop.trans hp, hov,
        by omega, by simpa [Control.polymorphic, hc] using hot⟩

end Itasca.Wasm2.Simd

end

/-! ## SuffixTyping -/

section

/-!
# Suffix compatibility and typing

Connects the suffix relation `Wasm2.Suffix` to the typing rules. `Fits.realizes` and
`Fits.of_realizes` relate it to the backward stack interpretation, `Suffix.common_subtype` gives
the common-subtype premise of the generated Wasm 2.0 `br_table` rule, and
`code.check_suffix.wasm_spec` and `.complete_of_subtype` are the declarative contract of
`code.check_suffix`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- The least types of the top `n` operands, padding implicit unreachable
operands with bottom. This depends on arity alone, never on a target's types. -/
def topTypes : List code.StackType → Nat → List valtype
  | _, 0 => []
  | [], n + 1 => .BOT :: topTypes [] n
  | v :: vs, n + 1 => StackSemantics.selectedType v :: topTypes vs n

theorem Fits.subtypes {poly : Bool} {vs : List code.StackType} {ts : List wasm_types.ValueType}
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

theorem Fits.realizes {poly : Bool} {vs : List code.StackType} {ts : List wasm_types.ValueType}
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
    {ts : List wasm_types.ValueType} (front : List valtype)
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
theorem Suffix.common_subtype {st : code.OpIterState} {ts : List wasm_types.ValueType}
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

theorem Suffix.of_realizes {st : code.OpIterState} {ts : List wasm_types.ValueType}
    (front : List valtype)
    (h : Sequence.Realizes (Control.polymorphic st)
      (st.vals.val.drop (Control.base st).val)
      (front ++ ts.map Translate.valueType)) : Suffix st ts := by
  apply Fits.of_realizes front
  simpa using h

end Itasca.Wasm2

namespace Itasca

end Itasca

end

import Itasca.Handler.ScalarComplete
import Itasca.Wasm2.Prefix

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

/-- Fixed arity operand checking, normalized independently of SIMD dispatch.
Inputs are listed in pop order; there is at most one concrete result. -/
def readFixed (st : code.OpIterState) (inputs : List types.ValueType)
    (output : Option types.ValueType) :
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

def inputTypes (inputs : List types.ValueType) : List valtype :=
  inputs.reverse.map Translate.valueType

def outputTypes (output : Option types.ValueType) : List valtype :=
  output.toList.map Translate.valueType

/-- Every interpretation of the resulting stack has the declared fixed effect. -/
def FixedEffect (poly : Bool) (before : List code.StackType)
    (inputs : List types.ValueType) (output : Option types.ValueType)
    (after : List code.StackType) : Prop :=
  ∀ ts, Sequence.Realizes poly after ts → ∃ front,
    ts = front ++ outputTypes output ∧
    Sequence.Realizes poly before (front ++ inputTypes inputs)

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

/-- Totality, unchanged controls/cursor, and the successful fixed stack effect. -/
theorem readFixed.segment (st : code.OpIterState) (inputs : List types.ValueType)
    (output : Option types.ValueType) (outer segment : List code.StackType)
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
theorem readFixed.complete (st : code.OpIterState) (inputs : List types.ValueType)
    (output : Option types.ValueType) (outer segment : List code.StackType) (front : List valtype)
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

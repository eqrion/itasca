import Itasca.Handler.StackSemantics

/-!
# Prefixes for simple instructions

`StackSemantics.NumericEffect` gives the shared stack interpretation of a checked numeric
operation, and `code.read_conversion.segment` and `code.read_binary.segment` describe the operand
handlers on arbitrary frame segments.
-/

open Aeneas Aeneas.Std

namespace Itasca.StackSemantics

/-- The effect of a checked numeric operation: the result is pushed, and a stack realizing the
remainder extends to one with the input types on top. -/
def NumericEffect (poly : Bool) (before : List code.StackType)
    (inputs : List wasm_types.ValueType) (output : wasm_types.ValueType)
    (after : List code.StackType) : Prop :=
  ∃ rest, after = rest ++ [.Val output] ∧
    ∀ ts, Sequence.Realizes poly rest ts →
      Sequence.Realizes poly before (ts ++ inputs.map Translate.valueType)

end Itasca.StackSemantics

namespace Itasca

/-- `code.read_conversion` on an arbitrary frame segment has a `NumericEffect` outcome, or rejects
with `EmptyStack` or `TypeMismatch`. -/
theorem code.read_conversion.segment (st : code.OpIterState)
    (outer segment : List code.StackType) (input output : wasm_types.ValueType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_conversion st input output ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + 1 ∧
        match r.1 with
        | .Ok _ => StackSemantics.NumericEffect (Control.polymorphic st) segment [input] output rest
        | .Err e => e = .EmptyStack ∨ e = .TypeMismatch ⦄ := by
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hlen, hout⟩ :=
    WP.spec_imp_exists (code.pop_with_type.realizes st outer segment input hvals hbase)
  dsimp only at hc hp hv hlen hout
  cases res with
  | Err e =>
    rw [WP.spec_equiv_exists]
    refine ⟨(.Err e, s), ?_, hc, hp, rest, hv, by omega, hout⟩
    simp [code.read_conversion, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok t =>
    have hcap : s.vals.val.length < Usize.max := by
      simp only [hvals, List.length_append] at hsize
      simp only [hv, List.length_append]
      omega
    obtain ⟨s', hpush, hv', hc', hp'⟩ :=
      WP.spec_imp_exists (code.push_val.spec s (.Val output) hcap)
    rw [WP.spec_equiv_exists]
    refine ⟨(.Ok (), s'), ?_, hc'.trans hc, hp'.trans hp, rest ++ [.Val output],
      ?_, by simpa using hlen, rest, rfl, ?_⟩
    · simp [code.read_conversion, hr, core.result.Result.Insts.CoreOpsTry.branch, hpush]
    · simpa [List.append_assoc, hv] using hv'
    · simpa using hout.2

/-- `code.read_binary` on an arbitrary frame segment, with any mix of explicit and polymorphic
operands, has a `NumericEffect` outcome, or rejects with `EmptyStack` or `TypeMismatch`. -/
theorem code.read_binary.segment (st : code.OpIterState)
    (outer segment : List code.StackType) (input output : wasm_types.ValueType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_binary st input output ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length + 1 ∧
        match r.1 with
        | .Ok _ => StackSemantics.NumericEffect (Control.polymorphic st) segment [input, input] output rest
        | .Err e => e = .EmptyStack ∨ e = .TypeMismatch ⦄ := by
  obtain ⟨⟨res, s⟩, hr, hc, hp, middle, hv, hlen, hout⟩ :=
    WP.spec_imp_exists (code.pop_with_type.realizes st outer segment input hvals hbase)
  dsimp only at hc hp hv hlen hout
  cases res with
  | Err e =>
    rw [WP.spec_equiv_exists]
    refine ⟨(.Err e, s), ?_, hc, hp, middle, hv, by omega, hout⟩
    simp [code.read_binary, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok t =>
    have hb : (Control.base s).val = outer.length := by simpa [Control.base, hc] using hbase
    have hpoly : Control.polymorphic s = Control.polymorphic st := by simp [Control.polymorphic, hc]
    obtain ⟨⟨res', s'⟩, hr', hc', hp', rest, hv', hlen', hout'⟩ :=
      WP.spec_imp_exists (code.pop_with_type.realizes s outer middle input hv hb)
    dsimp only at hc' hp' hv' hlen' hout'
    rw [hpoly] at hout'
    cases res' with
    | Err e =>
      rw [WP.spec_equiv_exists]
      refine ⟨(.Err e, s'), ?_, hc'.trans hc, hp'.trans hp, rest, hv', by omega, hout'⟩
      simp [code.read_binary, hr, hr', core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok t' =>
      have hcap : s'.vals.val.length < Usize.max := by
        simp only [hvals, List.length_append] at hsize
        simp only [hv', List.length_append]
        omega
      obtain ⟨s'', hpush, hv'', hc'', hp''⟩ :=
        WP.spec_imp_exists (code.push_val.spec s' (.Val output) hcap)
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok (), s''), ?_, hc''.trans (hc'.trans hc), hp''.trans (hp'.trans hp),
        rest ++ [.Val output], ?_, ?_, rest, rfl, ?_⟩
      · simp [code.read_binary, hr, hr', core.result.Result.Insts.CoreOpsTry.branch, hpush]
      · simpa [List.append_assoc, hv'] using hv''
      · simp only [List.length_append, List.length_singleton]; omega
      · intro ts hs
        simpa [List.append_assoc] using hout.2 _ (hout'.2 ts hs)

end Itasca

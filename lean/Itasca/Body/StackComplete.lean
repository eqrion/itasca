import Itasca.Body.StackSemantics

open Aeneas Aeneas.Std

set_option maxRecDepth 2048

namespace Itasca.StackSemantics

/-- Forward stack interpretation: a pop from a stack realizing a nonempty
declarative stack consumes its last type and realizes the remaining prefix. -/
theorem Popped.complete {poly before t after} (h : Popped poly before t after)
    {ts : List valtype} {u : valtype}
    (hr : Sequence.Realizes poly before (ts ++ [u])) :
    Sequence.Accepts t u ∧ Sequence.Realizes poly after ts := by
  cases h with
  | explicit poly rest t =>
    obtain ⟨front, last, he, hf, ht⟩ := Sequence.Realizes.snoc_inv hr
    have hs : ts = front ∧ u = last := by simpa using he
    rcases hs with ⟨rfl, rfl⟩
    exact ⟨ht, hf⟩
  | implicit => exact ⟨trivial, Sequence.realizes_polymorphic_empty ts⟩

theorem realizes_nonempty {ts : List valtype} {u : valtype} :
    ¬ Sequence.Realizes false [] (ts ++ [u]) := by
  intro h
  have he := (Sequence.realizes_empty _).mp h
  simp at he

end Itasca.StackSemantics

namespace Itasca

/-- An independently compatible operand stack forces the actual untyped pop
to succeed, including an implicit Bot at an unreachable frame base. -/
theorem code.pop_stack_type.complete (st : code.OpIterState)
    (outer segment : List code.StackType) (ts : List valtype) (u : valtype)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (ht : Sequence.Realizes (Control.polymorphic st) segment (ts ++ [u])) :
    ∃ t s rest, code.pop_stack_type st = .ok (.Ok t, s) ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ s.vals.val = outer ++ rest ∧
      rest.length ≤ segment.length ∧ Sequence.Accepts t u ∧
      Sequence.Realizes (Control.polymorphic st) rest ts := by
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hout⟩ :=
    WP.spec_imp_exists (code.pop_stack_type.segment st outer segment hvals hbase)
  dsimp only at hc hp hv hout
  cases res with
  | Ok t =>
    obtain ⟨ha, ht'⟩ := hout.complete ht
    exact ⟨t, s, rest, hr, hc, hp, hv, hout.length, ha, ht'⟩
  | Err e =>
    obtain ⟨_, hpoly, hnil, _⟩ := hout
    rw [hpoly, hnil] at ht
    exact (StackSemantics.realizes_nonempty ht).elim

/-- A typed operand required by a declarative derivation cannot produce
EmptyStack or TypeMismatch in the extracted pop. -/
theorem code.pop_with_type.complete (st : code.OpIterState)
    (outer segment : List code.StackType) (ts : List valtype) (u : types.ValueType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (ht : Sequence.Realizes (Control.polymorphic st) segment
      (ts ++ [Translate.valueType u])) :
    ∃ t s rest, code.pop_with_type st u = .ok (.Ok t, s) ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ s.vals.val = outer ++ rest ∧
      rest.length ≤ segment.length ∧ Sequence.Accepts t (Translate.valueType u) ∧
      Sequence.Realizes (Control.polymorphic st) rest ts := by
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hout⟩ :=
    WP.spec_imp_exists (code.pop_with_type.segment st outer segment u hvals hbase)
  dsimp only at hc hp hv hout
  cases res with
  | Ok t =>
    obtain ⟨ha, ht'⟩ := hout.1.complete ht
    exact ⟨t, s, rest, hr, hc, hp, hv, hout.length, ha, ht'⟩
  | Err e =>
    rcases hout with ⟨_, hpoly, hnil, _⟩ | ⟨_, t, hpop, hbad⟩
    · rw [hpoly, hnil] at ht
      exact (StackSemantics.realizes_nonempty ht).elim
    · exact (hbad (hpop.complete ht).1).elim

/-- Popping a whole declaratively required argument list also succeeds. The
loop consumes it from right to left, preserving the remaining prefix. -/
theorem code.pop_types.complete (st : code.OpIterState)
    (outer segment : List code.StackType) (ts : List valtype)
    (expected : Slice types.ValueType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length)
    (ht : Sequence.Realizes (Control.polymorphic st) segment
      (ts ++ expected.val.map Translate.valueType)) :
    code.pop_types st expected ⦃ r => r.1 = .Ok () ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧
        Sequence.Realizes (Control.polymorphic st) rest ts ⦄ := by
  unfold code.pop_types code.pop_types_loop
  apply loop.spec_decr_nat (fun p => p.2.val)
    (fun p => p.2.val ≤ expected.val.length ∧ p.1.ctrls = st.ctrls ∧ p.1.pos = st.pos ∧
      ∃ current, p.1.vals.val = outer ++ current ∧ current.length ≤ segment.length ∧
        Sequence.Realizes (Control.polymorphic st) current
          (ts ++ (expected.val.take p.2.val).map Translate.valueType))
  · rintro ⟨s, j⟩ ⟨hj, hc, hp, current, hv, hlen, htypes⟩
    dsimp only at hj hc hp hv hlen htypes
    unfold code.pop_types_loop.body
    dsimp only
    split
    · rename_i hzero
      simp only [WP.spec_ok]
      exact ⟨trivial, hc, hp, current, hv, hlen, by simpa [hzero] using htypes⟩
    · rename_i hnz
      step
      have hidx : i1.val < expected.val.length := by scalar_tac
      step
      have hb : (Control.base s).val = outer.length := by
        simpa [Control.base, hc] using hbase
      have hpoly : Control.polymorphic s = Control.polymorphic st := by
        simp [Control.polymorphic, hc]
      have hsucc : j.val = i1.val + 1 := by scalar_tac
      have htake : expected.val.take j.val = expected.val.take i1.val ++ [vt] := by
        rw [hsucc, List.take_succ_eq_append_getElem hidx, vt_post]
      have hpop : Sequence.Realizes (Control.polymorphic s) current
          ((ts ++ (expected.val.take i1.val).map Translate.valueType) ++
            [Translate.valueType vt]) := by
        simpa [hpoly, htake, List.map_append, List.append_assoc] using htypes
      obtain ⟨t, s', rest, hr, hc', hp', hv', hlen', haccept, ht'⟩ :=
        code.pop_with_type.complete s outer current _ vt hv hb hpop
      rw [WP.spec_equiv_exists]
      refine ⟨.cont (s', i1), ?_, ?_⟩
      · simp [hr, core.result.Result.Insts.CoreOpsTry.branch]
      dsimp only
      refine ⟨?_, hc'.trans hc, hp'.trans hp, ⟨rest, hv', hlen'.trans hlen, ?_⟩, ?_⟩
      · exact Nat.le_trans (Nat.le_of_lt hidx) (Nat.le_refl _)
      · rw [hpoly] at ht'; exact ht'
      · omega
  · exact ⟨by simp, rfl, rfl, segment, hvals, Nat.le_refl _, by simpa using ht⟩

end Itasca

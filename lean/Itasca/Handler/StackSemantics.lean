import Itasca.Handler.Stack
import Itasca.Handler.Sequence

/-!
# Stack operation semantics

Describes the observable outcome of the extracted pops on a frame's operand segment
(`StackSemantics.Popped`, `PopResult`, `TypedPopResult`). `code.pop_stack_type.segment`,
`code.pop_with_type.segment`, `code.pop_with_type.realizes` and `code.pop_types.realizes` state
the outcome for the current frame and relate it to `Sequence.Realizes`, and the `.total` theorems
show that the pops terminate and keep `Control.Shape` for every outcome.
-/

open Aeneas Aeneas.Std

namespace Itasca.Sequence

/-- Inverts `Realizes.snoc`: a realization of a stack with a pushed operand splits into a
realization of the rest and the type of the operand. -/
theorem Realizes.snoc_inv {poly : Bool} {vals : List code.StackType}
    {t : code.StackType} {ts : List valtype} (h : Realizes poly (vals ++ [t]) ts) :
    ∃ front u, ts = front ++ [u] ∧ Realizes poly vals front ∧ Accepts t u := by
  obtain ⟨front, suffix, hf, hs, rfl⟩ := h
  rcases List.eq_nil_or_concat' suffix with hnil | ⟨rest, u, hsnoc⟩
  · have hlen := hs.length_eq
    simp [hnil] at hlen
  · subst suffix
    have hr : List.Forall₂ Accepts (t :: vals.reverse) (u :: rest.reverse) := by
      simpa using List.rel_reverse hs
    cases hr with
    | cons ht htail =>
      exact ⟨front ++ rest, u, (List.append_assoc ..).symm,
        ⟨front, rest, hf, List.forall₂_reverse_iff.mp htail, rfl⟩, ht⟩

end Itasca.Sequence

namespace Itasca.Control

/-- Every control frame's value stack base is at most the current frame base. -/
theorem Shape.frame_base_le {st : code.OpIterState} (h : Shape st)
    (c : code.Ctrl) (hc : c ∈ st.ctrls.val) :
    c.value_stack_base.val ≤ (base st).val := by
  rcases List.eq_nil_or_concat' st.ctrls.val with hnil | ⟨cs, last, hlast⟩
  · simp [hnil] at hc
  · have hord := h.ordered
    rw [hlast, List.pairwise_append] at hord
    simp only [base, hlast, List.getLast?_concat]
    rw [hlast, List.mem_append] at hc
    rcases hc with hc | hc
    · exact hord.2.2 c hc last (by simp)
    · have heq : c = last := by simpa using hc
      simp [heq]

/-- Replacing the operands preserves `Shape` when the current frame base is still within them. -/
theorem Shape.replace_operands {st st' : code.OpIterState} (h : Shape st)
    (hctrls : st'.ctrls = st.ctrls)
    (hbase : (base st).val ≤ st'.vals.val.length) : Shape st' := by
  constructor
  · simpa [hctrls] using h.ordered
  · intro c hc
    exact Nat.le_trans (h.frame_base_le c (by simpa [hctrls] using hc)) hbase

end Itasca.Control

namespace Itasca.StackSemantics

/-- A successful pop either removes an explicit operand or, in a polymorphic frame with no
operands, yields `Bot`. -/
inductive Popped : Bool → List code.StackType → code.StackType → List code.StackType → Prop
  | explicit (poly : Bool) (rest : List code.StackType) (t : code.StackType) :
      Popped poly (rest ++ [t]) t rest
  | implicit : Popped true [] .Bot []

theorem Popped.length {poly before t after} (h : Popped poly before t after) :
    after.length ≤ before.length := by
  cases h <;> simp

theorem Popped.realizes {poly before t after} (h : Popped poly before t after)
    (ts : List valtype) (u : valtype) (ht : Sequence.Accepts t u)
    (hs : Sequence.Realizes poly after ts) :
    Sequence.Realizes poly before (ts ++ [u]) := by
  cases h with
  | explicit => exact hs.snoc _ _ ht
  | implicit => exact Sequence.realizes_polymorphic_empty _

/-- The outcome of the untyped pop: a `Popped` step on success, and `EmptyStack` only for an empty
reachable frame. -/
def PopResult (poly : Bool) (before : List code.StackType)
    (r : core.result.Result code.StackType error.OpError) (after : List code.StackType) : Prop :=
  match r with
  | .Ok t => Popped poly before t after
  | .Err e => e = .EmptyStack ∧ poly = false ∧ before = [] ∧ after = []

theorem PopResult.length {poly before r after} (h : PopResult poly before r after) :
    after.length ≤ before.length := by
  cases r with
  | Ok t => exact Popped.length h
  | Err e => rcases h with ⟨_, _, rfl, rfl⟩; simp

/-- The outcome of the typed pop: it rejects only an empty reachable frame (`EmptyStack`) or an
incompatible operand (`TypeMismatch`). -/
def TypedPopResult (poly : Bool) (before : List code.StackType) (expected : types.ValueType)
    (r : core.result.Result code.StackType error.OpError) (after : List code.StackType) : Prop :=
  match r with
  | .Ok t => Popped poly before t after ∧ Sequence.Accepts t (Translate.valueType expected)
  | .Err e =>
      (e = .EmptyStack ∧ poly = false ∧ before = [] ∧ after = []) ∨
      (e = .TypeMismatch ∧ ∃ t, Popped poly before t after ∧
        ¬ Sequence.Accepts t (Translate.valueType expected))

theorem TypedPopResult.length {poly before expected r after}
    (h : TypedPopResult poly before expected r after) : after.length ≤ before.length := by
  cases r with
  | Ok t => exact h.1.length
  | Err e =>
    rcases h with ⟨_, _, rfl, rfl⟩ | ⟨_, t, hp, _⟩
    · simp
    · exact hp.length

/-- A successful typed pop turns a realization of the remaining stack into one of the original
stack with the expected type pushed. -/
theorem TypedPopResult.realizes {poly before expected t after}
    (h : TypedPopResult poly before expected (.Ok t) after)
    (ts : List valtype) (hs : Sequence.Realizes poly after ts) :
    Sequence.Realizes poly before (ts ++ [Translate.valueType expected]) :=
  h.1.realizes ts _ h.2 hs

end Itasca.StackSemantics

namespace Itasca

/-- `code.pop_stack_type` on the current frame's operand segment has a `PopResult` outcome, for any
mix of concrete and `Bot` operands. -/
@[step]
theorem code.pop_stack_type.segment (st : code.OpIterState)
    (outer segment : List code.StackType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length) :
    code.pop_stack_type st ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧
        StackSemantics.PopResult (Control.polymorphic st) segment r.1 rest ⦄ := by
  rcases List.eq_nil_or_concat' segment with hnil | ⟨rest, t, hsnoc⟩
  · subst segment
    have hb : alloc.vec.Vec.len st.vals = Control.base st := by scalar_tac
    rw [code.pop_stack_type.at_base st hb]
    cases hp : Control.polymorphic st
    · simp only [WP.spec_ok]
      exact ⟨rfl, rfl, [], hvals, rfl, rfl, rfl, rfl⟩
    · simp only [↓reduceIte, WP.spec_ok]
      exact ⟨trivial, trivial, [], hvals, .implicit⟩
  · have hv : st.vals.val = (outer ++ rest) ++ [t] := by
      simpa [hsnoc, List.append_assoc] using hvals
    obtain ⟨⟨res, st'⟩, hr, hok, hv', hc, hp⟩ :=
      WP.spec_imp_exists (code.pop_stack_type.above_base st (outer ++ rest) t hv
        (by simp [hbase]))
    dsimp only at hok hv' hc hp
    rw [hr, WP.spec_ok]
    exact ⟨hc, hp, rest, hv', by simpa [hok, hsnoc, StackSemantics.PopResult] using
      StackSemantics.Popped.explicit (Control.polymorphic st) rest t⟩

/-- `code.pop_with_type` on the current frame's operand segment has a `TypedPopResult` outcome. -/
@[step]
theorem code.pop_with_type.segment (st : code.OpIterState)
    (outer segment : List code.StackType) (expected : types.ValueType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length) :
    code.pop_with_type st expected ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧
        StackSemantics.TypedPopResult (Control.polymorphic st) segment expected r.1 rest ⦄ := by
  obtain ⟨⟨res, st'⟩, hr, hc, hp, rest, hv, hout⟩ :=
    WP.spec_imp_exists (code.pop_stack_type.segment st outer segment hvals hbase)
  dsimp only at hc hp hv hout
  cases res with
  | Err e =>
    simp only [StackSemantics.PopResult] at hout
    rw [WP.spec_equiv_exists]
    refine ⟨(.Err e, st'), ?_, hc, hp, rest, hv, Or.inl hout⟩
    simp [code.pop_with_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok t =>
    cases t with
    | Bot =>
      rw [WP.spec_equiv_exists]
      refine ⟨(.Ok .Bot, st'), ?_, hc, hp, rest, hv, hout, trivial⟩
      simp [code.pop_with_type, hr, core.result.Result.Insts.CoreOpsTry.branch]
    | Val actual =>
      by_cases heq : Translate.valueType actual = Translate.valueType expected
      · rw [WP.spec_equiv_exists]
        refine ⟨(.Ok (.Val actual), st'), ?_, hc, hp, rest, hv, hout, heq.symm⟩
        simp [code.pop_with_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
          Translate.valueType_eq, heq]
      · rw [WP.spec_equiv_exists]
        refine ⟨(.Err .TypeMismatch, st'), ?_, hc, hp, rest, hv,
          Or.inr ⟨rfl, .Val actual, hout, ?_⟩⟩
        · simp [code.pop_with_type, hr, core.result.Result.Insts.CoreOpsTry.branch,
            Translate.valueType_eq, heq]
        · exact fun h => heq h.symm

/-- `code.pop_with_type` shrinks the segment, and on success its operand is accepted and
realizations of the remainder extend to the original segment. Errors are `EmptyStack` or
`TypeMismatch`. -/
theorem code.pop_with_type.realizes (st : code.OpIterState)
    (outer segment : List code.StackType) (expected : types.ValueType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length) :
    code.pop_with_type st expected ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧
        match r.1 with
        | .Ok t => Sequence.Accepts t (Translate.valueType expected) ∧
          ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
            Sequence.Realizes (Control.polymorphic st) segment (ts ++ [Translate.valueType expected])
        | .Err e => e = .EmptyStack ∨ e = .TypeMismatch ⦄ := by
  obtain ⟨⟨res, st'⟩, hr, hc, hp, rest, hv, hout⟩ :=
    WP.spec_imp_exists (code.pop_with_type.segment st outer segment expected hvals hbase)
  dsimp only at hc hp hv hout
  rw [hr, WP.spec_ok]
  refine ⟨hc, hp, rest, hv, hout.length, ?_⟩
  cases res with
  | Ok t => exact ⟨hout.2, fun ts hs => hout.realizes ts hs⟩
  | Err e =>
    rcases hout with h | h
    · exact .inl h.1
    · exact .inr h.1

/-- `code.pop_types` shrinks the segment, and on success realizations of the remainder extend to
the original segment with the expected types appended. Errors are `EmptyStack` or
`TypeMismatch`. -/
theorem code.pop_types.realizes (st : code.OpIterState)
    (outer segment : List code.StackType) (expected : Slice types.ValueType)
    (hvals : st.vals.val = outer ++ segment)
    (hbase : (Control.base st).val = outer.length) :
    code.pop_types st expected ⦃ r =>
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ rest, r.2.vals.val = outer ++ rest ∧ rest.length ≤ segment.length ∧
        match r.1 with
        | .Ok _ => ∀ ts, Sequence.Realizes (Control.polymorphic st) rest ts →
            Sequence.Realizes (Control.polymorphic st) segment
              (ts ++ expected.val.map Translate.valueType)
        | .Err e => e = .EmptyStack ∨ e = .TypeMismatch ⦄ := by
  unfold code.pop_types code.pop_types_loop
  apply loop.spec_decr_nat (fun p => p.2.val)
    (fun p => p.2.val ≤ expected.val.length ∧ p.1.ctrls = st.ctrls ∧ p.1.pos = st.pos ∧
      ∃ current, p.1.vals.val = outer ++ current ∧ current.length ≤ segment.length ∧
        ∀ ts, Sequence.Realizes (Control.polymorphic st) current ts →
          Sequence.Realizes (Control.polymorphic st) segment
            (ts ++ (expected.val.drop p.2.val).map Translate.valueType))
  · rintro ⟨s, j⟩ ⟨hj, hc, hp, current, hv, hlen, htransfer⟩
    dsimp only at hj hc hp hv hlen htransfer
    unfold code.pop_types_loop.body
    dsimp only
    split
    · rename_i hzero
      simp only [WP.spec_ok]
      refine ⟨hc, hp, current, hv, hlen, ?_⟩
      simpa [hzero] using htransfer
    · rename_i hnz
      step
      have hidx : i1.val < expected.val.length := by scalar_tac
      step
      have hb : (Control.base s).val = outer.length := by
        simpa [Control.base, hc] using hbase
      have hpoly : Control.polymorphic s = Control.polymorphic st := by
        simp [Control.polymorphic, hc]
      obtain ⟨⟨res, s'⟩, hr, hcout, hpout, rest, hvout, hlenout, hresult⟩ :=
        WP.spec_imp_exists (code.pop_with_type.realizes s outer current vt hv hb)
      dsimp only at hcout hpout hvout hlenout hresult
      rw [hpoly] at hresult
      cases res with
      | Err e =>
        rw [WP.spec_equiv_exists]
        refine ⟨.done (.Err e, s'), ?_, hcout.trans hc, hpout.trans hp,
          rest, hvout, Nat.le_trans hlenout hlen, hresult⟩
        simp [hr, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok t =>
        rw [WP.spec_equiv_exists]
        refine ⟨.cont (s', i1), ?_, ?_⟩
        · simp [hr, core.result.Result.Insts.CoreOpsTry.branch]
        dsimp only
        refine ⟨?_, hcout.trans hc, hpout.trans hp, ⟨rest, hvout,
          Nat.le_trans hlenout hlen, ?_⟩, ?_⟩
        · scalar_tac
        · intro ts hs
          have hs' := htransfer (ts ++ [Translate.valueType vt]) (hresult.2 ts hs)
          have hsucc : j.val = i1.val + 1 := by scalar_tac
          rw [List.drop_eq_getElem_cons hidx, List.map_cons, ← hsucc]
          simpa only [List.append_assoc, List.singleton_append, vt_post] using hs'
        · scalar_tac
  · refine ⟨by simp, rfl, rfl, segment, hvals, Nat.le_refl _, ?_⟩
    intro ts hs
    simpa using hs

/-- `code.pop_stack_type` terminates and preserves `Control.Shape`, and fails only with
`EmptyStack`. -/
theorem code.pop_stack_type.total (st : code.OpIterState) (hshape : Control.Shape st) :
    code.pop_stack_type st ⦃ r =>
      Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      r.2.vals.val.length ≤ st.vals.val.length ∧
      (∀ e, r.1 = .Err e → e = .EmptyStack) ⦄ := by
  let n := (Control.base st).val
  have hn : n ≤ st.vals.val.length := hshape.base_le
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hout⟩ :=
    WP.spec_imp_exists (code.pop_stack_type.segment st (st.vals.val.take n) (st.vals.val.drop n)
      (List.take_append_drop ..).symm (by simp [n, Nat.min_eq_left hn]))
  dsimp only at hc hp hv hout
  have hb : (Control.base st).val ≤ s.vals.val.length := by simp [hv, n, Nat.min_eq_left hn]
  have hlen := hout.length
  rw [hr, WP.spec_ok]
  refine ⟨hshape.replace_operands hc hb, hc, hp, ?_, ?_⟩
  · simp only [hv, List.length_append, List.length_take, List.length_drop] at *
    omega
  · intro e he
    cases res with
    | Ok t => simp at he
    | Err e' => cases he; exact hout.1

/-- `code.pop_with_type` terminates and preserves `Control.Shape`, including for `Bot` and
mismatched operands. -/
theorem code.pop_with_type.total (st : code.OpIterState) (expected : types.ValueType)
    (hshape : Control.Shape st) :
    code.pop_with_type st expected ⦃ r =>
      Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      r.2.vals.val.length ≤ st.vals.val.length ∧
      (∀ e, r.1 = .Err e → e = .EmptyStack ∨ e = .TypeMismatch) ⦄ := by
  let n := (Control.base st).val
  have hn : n ≤ st.vals.val.length := hshape.base_le
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hlen, hout⟩ :=
    WP.spec_imp_exists (code.pop_with_type.realizes st (st.vals.val.take n) (st.vals.val.drop n)
      expected (List.take_append_drop ..).symm (by simp [n, Nat.min_eq_left hn]))
  dsimp only at hc hp hv hlen hout
  have hb : (Control.base st).val ≤ s.vals.val.length := by simp [hv, n, Nat.min_eq_left hn]
  rw [hr, WP.spec_ok]
  refine ⟨hshape.replace_operands hc hb, hc, hp, ?_, ?_⟩
  · simp only [hv, List.length_append, List.length_take, List.length_drop] at *
    omega
  · intro e he
    cases res with
    | Ok t => simp at he
    | Err e' => cases he; exact hout

/-- `code.pop_types` terminates and preserves `Control.Shape` on acceptance and rejection. -/
theorem code.pop_types.total (st : code.OpIterState) (expected : Slice types.ValueType)
    (hshape : Control.Shape st) :
    code.pop_types st expected ⦃ r =>
      Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      r.2.vals.val.length ≤ st.vals.val.length ∧
      (∀ e, r.1 = .Err e → e = .EmptyStack ∨ e = .TypeMismatch) ⦄ := by
  let n := (Control.base st).val
  have hn : n ≤ st.vals.val.length := hshape.base_le
  obtain ⟨⟨res, s⟩, hr, hc, hp, rest, hv, hlen, hout⟩ :=
    WP.spec_imp_exists (code.pop_types.realizes st (st.vals.val.take n) (st.vals.val.drop n)
      expected (List.take_append_drop ..).symm (by simp [n, Nat.min_eq_left hn]))
  dsimp only at hc hp hv hlen hout
  have hb : (Control.base st).val ≤ s.vals.val.length := by simp [hv, n, Nat.min_eq_left hn]
  rw [hr, WP.spec_ok]
  refine ⟨hshape.replace_operands hc hb, hc, hp, ?_, ?_⟩
  · simp only [hv, List.length_append, List.length_take, List.length_drop] at *
    omega
  · intro e he
    cases res with
    | Ok t => simp at he
    | Err e' => cases he; exact hout

end Itasca

import Itasca.Wasm2.Trace.Basic
import Itasca.Wasm2.Trace.Refinement
import Itasca.Wasm2.References.Step
import Itasca.Wasm2.Bulk.Step

/-! Concrete byte provenance for Core 2.0 callback leaves. Reader failures are
silent; successful reads retain the precise decoded arguments even when the
callback itself rejects. No accepting-visitor premise is used. -/
open Aeneas Aeneas.Std

namespace Itasca.MultiValue.CallbackBytes

open VisitorTrace CallbackTrace

/-- Exact observed Core 2.0 leaf trace under the independent pending-byte cursor. -/
def StepRecords {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (ctx : code.Context) (opcode : U8) : Prop :=
  ∀ v result final v', code.step_wasm2 visitor st.core data env ctx opcode v =
      .ok (result, final, v') →
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final

/-- Metadata survives the fixed checker, whose stack operations cannot move the
byte cursor. This applies to ordinary successful returns without visitor premises. -/
theorem metadata_post {A B : Type} (st : code.OpIterState)
    (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (capacity : st.vals.val.length < Usize.max)
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List types.ValueType) (output : A → Option types.ValueType)
    (metadata : A → B) (P : B → Usize → Prop)
    (decoded : decode ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ a, r.1 = .Ok a → P (metadata a) r.2.pos ⦄)
    (value : B) (final : code.OpIterState)
    (run : metadataOperands decode pops output metadata = .ok (.Ok value, final)) :
    P value final.pos := by
  obtain ⟨⟨res, middle⟩, hr, hv, hc, hp⟩ := WP.spec_imp_exists decoded
  dsimp only at hv hc hp
  cases res with
  | Err e => simp [metadataOperands, hr] at run
  | Ok a =>
    obtain ⟨⟨res, out⟩, hout, _, hpos, _⟩ := WP.spec_imp_exists
      (Simd.readFixed.segment middle (pops a) (output a) outer segment
        (by simpa [hv] using values) (by simpa [Control.base, hc] using base)
        (by simpa [hv] using capacity))
    dsimp only at hpos
    cases res with
    | Err e => simp [metadataOperands, hr, hout] at run
    | Ok u =>
      cases u
      simp only [metadataOperands, hr, bind_ok, Std.uncurry] at run
      rw [hout] at run
      simp only [bind_ok, Std.uncurry, Result.ok.injEq,
        Prod.mk.injEq, core.result.Result.Ok.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      simpa [hpos] using hp a rfl

theorem metadata_bytes {data env locals index st} (p : Pending data env locals index st)
    {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List types.ValueType) (output : A → Option types.ValueType)
    (metadata : A → B) (P : B → Usize → Prop)
    (decoded : decode ⦃ r => r.2.vals = st.core.vals ∧ r.2.ctrls = st.core.ctrls ∧
      ∀ a, r.1 = .Ok a → P (metadata a) r.2.pos ⦄)
    (capacity : st.core.vals.val.length < Usize.max)
    (value : B) (final : code.OpIterState)
    (run : metadataOperands decode pops output metadata = .ok (.Ok value, final)) :
    P value final.pos := by
  obtain ⟨_, outer, _, _, base, _, ctrls, _, stack⟩ := p.opened
  exact metadata_post st.core outer p.current.vals stack
    (by simp [Control.base, ctrls, base]) capacity decode pops output metadata P decoded value final run

theorem metadata_bytes_at {data env locals index st} (p : Pending data env locals index st)
    (next : Usize) {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List types.ValueType) (output : A → Option types.ValueType)
    (metadata : A → B) (P : B → Usize → Prop)
    (decoded : decode ⦃ r => r.2.vals = st.core.vals ∧ r.2.ctrls = st.core.ctrls ∧
      ∀ a, r.1 = .Ok a → P (metadata a) r.2.pos ⦄)
    (capacity : st.core.vals.val.length < Usize.max)
    (value : B) (final : code.OpIterState)
    (run : metadataOperands decode pops output metadata = .ok (.Ok value, final)) :
    P value final.pos := by
  obtain ⟨_, outer, _, _, base, _, ctrls, _, stack⟩ := p.opened
  exact metadata_post {st.core with pos := next} outer p.current.vals stack
    (by simp [Control.base, ctrls, base]) capacity decode pops output metadata P decoded value final run

/-- A single accepted metadata reader supplies an independent token and span. -/
def ReadBytes {A : Type} (data : Slice U8) (start : Usize)
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (action : A → Action) : Prop :=
  ∀ s a, read = .ok (.Ok a, s) → ∃ token,
    actionToken (action a) [] = some token ∧ (action a).opcode ≠ some 0x0E#u8 ∧
    At data start token s.pos

end Itasca.MultiValue.CallbackBytes

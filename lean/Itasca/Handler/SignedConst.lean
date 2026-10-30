import Itasca.Binary.SignedLeb32
import Itasca.Spec.Instr
import Itasca.Handler.Sequence
import Itasca.Handler.Stack

/-!
# `i32.const` handler

Lemmas about `code.read_i32_const` (decoding the signed LEB128 immediate and pushing an `i32`
operand) and `code.step` on `i32.const`: `code.step_i32_const`, `.failed_read`, `.visitor_rejected`
and `.total`. `Sequence.TypedPrefix.i32Const` extends a typed prefix by the constant.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- If the LEB128 read succeeds, `code.read_i32_const` advances the cursor and appends one `i32`
operand. -/
@[step]
theorem code.read_i32_const.from_read (st : code.OpIterState) (data : Slice U8)
    (value : I32) (next : Usize)
    (hread : reader.read_s32_leb data st.pos = .ok (.Ok (value, next)))
    (hsize : st.vals.val.length < Usize.max) :
    code.read_i32_const st data ⦃ r => r.1 = .Ok value ∧
      r.2.vals.val = st.vals.val ++ [.Val .I32] ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = next ⦄ := by
  rw [code.read_i32_const, hread]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*

/-- A malformed immediate makes `code.read_i32_const` fail and leave the validator state
unchanged. -/
theorem code.read_i32_const.failed_read (st : code.OpIterState) (data : Slice U8)
    (e : error.OpError) (hread : reader.read_s32_leb data st.pos = .ok (.Err e)) :
    code.read_i32_const st data = .ok (.Err e, st) := by
  simp [code.read_i32_const, hread, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `code.read_i32_const` terminates, with exact byte provenance for the decoded value or the
rejection, when the push fits. -/
@[step]
theorem code.read_i32_const.spec (st : code.OpIterState) (data : Slice U8)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_i32_const st data ⦃ r => r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok value => SignedLeb32.Decoded data st.pos value.val r.2.pos ∧
          r.2.vals.val = st.vals.val ++ [.Val .I32]
      | .Err e => SignedLeb32.Rejected data st.pos e ∧ r.2 = st ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_s32_leb.spec data st.pos)
  cases r with
  | Err e =>
    rw [code.read_i32_const.failed_read st data e hr]
    simp only [WP.spec_ok]
    exact ⟨trivial, hp, trivial⟩
  | Ok r =>
    rcases r with ⟨value, next⟩
    obtain ⟨r, hresult, hok, hv, hc, hpos⟩ := WP.spec_imp_exists
      (code.read_i32_const.from_read st data value next hr hsize)
    rw [hresult]
    simp only [WP.spec_ok, hok, hpos]
    exact ⟨hc, hp, hv⟩

end Itasca

namespace Itasca.Sequence

private theorem forall₂_snoc {vals : List code.StackType} {t : code.StackType}
    {out : List valtype} (h : List.Forall₂ Accepts (vals ++ [t]) out) :
    ∃ before u, out = before ++ [u] ∧ List.Forall₂ Accepts vals before ∧ Accepts t u := by
  induction vals generalizing out with
  | nil =>
    cases h with
    | cons ht hs =>
      cases hs
      exact ⟨[], _, rfl, .nil, ht⟩
  | cons x xs ih =>
    cases h with
    | cons hx hs =>
      obtain ⟨before, u, rfl, hb, hu⟩ := ih hs
      exact ⟨_ :: before, u, rfl, .cons hx hb, hu⟩

/-- If a stack with a concrete operand appended is realized, the last type is that operand's type
and the rest realizes the remainder. -/
theorem Realizes.snoc_val {poly : Bool} {vals : List code.StackType} {ts : List valtype}
    (valueType : wasm_types.ValueType) (h : Realizes poly (vals ++ [.Val valueType]) ts) :
    ∃ before, ts = before ++ [Translate.valueType valueType] ∧ Realizes poly vals before := by
  rcases h with ⟨front, suffix, hf, hs, rfl⟩
  obtain ⟨before, u, rfl, hb, hu⟩ := forall₂_snoc hs
  change u = Translate.valueType valueType at hu
  subst u
  exact ⟨front ++ before, (List.append_assoc ..).symm, front, before, hf, hb, rfl⟩

/-- Pushing an `i32` operand extends a typed prefix by `i32.const`. -/
theorem TypedPrefix.i32Const {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C ops poly vals)
    (hC : wf_context C) (value : I32) :
    TypedPrefix C (ops ++ [Spec.i32Const value]) poly (vals ++ [.Val .I32]) := by
  apply h.append hC _ (Spec.i32Const_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .I32 hout
  exact ⟨before, hb, Spec.i32Const_framed C hC value before⟩

end Itasca.Sequence

namespace Itasca

end Itasca

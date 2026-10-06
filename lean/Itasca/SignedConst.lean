import Itasca.SignedLeb
import Itasca.CoreSyntax
import Itasca.Sequence

open Aeneas Aeneas.Std

namespace Itasca.Core

/-- An I32 constant's generated typing uses its unsigned bit pattern. -/
theorem i32Const_typed (C : context) (hC : wf_context C) (value : I32) :
    Instr_ok C (i32Const value) (.mk_functype (.mk_list []) (.mk_list [.I32])) :=
  .const C .I32 _ hC (i32Const_wf value)

theorem i32Const_framed (C : context) (hC : wf_context C) (value : I32) (ts : List valtype) :
    Instrs_ok C [i32Const value] (.mk_functype (.mk_list ts) (.mk_list (ts ++ [.I32]))) := by
  simpa using Instrs_ok.frame C [i32Const value] ts [] [.I32]
    (.instr C _ [] [.I32] (i32Const_typed C hC value) hC (i32Const_wf value))
    hC (by simpa [Forall] using i32Const_wf value)

end Itasca.Core

namespace Itasca

/-- A successfully decoded constant advances the cursor and appends one I32 operand. -/
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

/-- A malformed constant leaves the entire validator state unchanged. -/
theorem code.read_i32_const.failed_read (st : code.OpIterState) (data : Slice U8)
    (e : error.OpError) (hread : reader.read_s32_leb data st.pos = .ok (.Err e)) :
    code.read_i32_const st data = .ok (.Err e, st) := by
  simp [code.read_i32_const, hread, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Total constant decoding under the single push's capacity bound. -/
@[step]
theorem code.read_i32_const.spec (st : code.OpIterState) (data : Slice U8)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_i32_const st data ⦃ r => r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok value => SignedLeb.Decoded data st.pos value.val r.2.pos ∧
          r.2.vals.val = st.vals.val ++ [.Val .I32]
      | .Err e => SignedLeb.Rejected data st.pos e ∧ r.2 = st ⦄ := by
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

/-- Dispatch calls the I32 visitor with the signed value and the updated state. -/
theorem code.step_i32_const {V : Type} (visitor : code.OpVisitor V)
    (st st' : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (value : I32) (v v' : V)
    (hread : code.read_i32_const st data = .ok (.Ok value, st'))
    (hvisit : visitor.on_i32_const v st' value = .ok (.Ok (), v')) :
    code.step visitor st data env ctx code.OP_I32_CONST v = .ok (.Ok (), st', v') := by
  simp [code.step, code.OP_I32_CONST, code.OP_NOP, code.OP_UNREACHABLE,
    hread, hvisit, code.visit, core.result.Result.Insts.CoreOpsTry.branch]

/-- An invalid immediate fails before invoking the visitor. -/
theorem code.step_i32_const.failed_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (e : error.OpError) (v : V)
    (hread : reader.read_s32_leb data st.pos = .ok (.Err e)) :
    code.step visitor st data env ctx code.OP_I32_CONST v = .ok (.Err e, st, v) := by
  have hr := code.read_i32_const.failed_read st data e hread
  simp [code.step, code.OP_I32_CONST, code.OP_NOP, code.OP_UNREACHABLE, hr,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

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

/-- A concrete appended value is the final type of every represented stack. -/
theorem Realizes.snoc_val {poly : Bool} {vals : List code.StackType} {ts : List valtype}
    (valueType : types.ValueType) (h : Realizes poly (vals ++ [.Val valueType]) ts) :
    ∃ before, ts = before ++ [Translate.valueType valueType] ∧ Realizes poly vals before := by
  rcases h with ⟨front, suffix, hf, hs, rfl⟩
  obtain ⟨before, u, rfl, hb, hu⟩ := forall₂_snoc hs
  change u = Translate.valueType valueType at hu
  subst u
  exact ⟨front ++ before, (List.append_assoc ..).symm, front, before, hf, hb, rfl⟩

/-- The exact constant stack effect preserves the per-frame declarative invariant. -/
theorem TypedPrefix.i32Const {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C ops poly vals)
    (hC : wf_context C) (value : I32) :
    TypedPrefix C (ops ++ [Core.i32Const value]) poly (vals ++ [.Val .I32]) := by
  apply h.append hC _ (Core.i32Const_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .I32 hout
  exact ⟨before, hb, Core.i32Const_framed C hC value before⟩

end Itasca.Sequence

namespace Itasca

/-- A rejecting visitor keeps the decoded constant's stack/cursor effects and its own state. -/
theorem code.step_i32_const.visitor_rejected {V : Type} (visitor : code.OpVisitor V)
    (st st' : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (value : I32) (v v' : V) (e : error.VisitError)
    (hread : code.read_i32_const st data = .ok (.Ok value, st'))
    (hvisit : visitor.on_i32_const v st' value = .ok (.Err e, v')) :
    code.step visitor st data env ctx code.OP_I32_CONST v = .ok (.Err (.Visitor e), st', v') := by
  simp [code.step, code.OP_I32_CONST, code.OP_NOP, code.OP_UNREACHABLE,
    hread, hvisit, code.visit, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Constant dispatch is total whenever its push fits and the selected visitor hook returns. -/
theorem code.step_i32_const.total {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (hsize : st.vals.val.length < Usize.max)
    (hvisit : ∀ s value, ∃ r, visitor.on_i32_const v s value = .ok r) :
    ∃ r, code.step visitor st data env ctx code.OP_I32_CONST v = .ok r := by
  obtain ⟨⟨r, st'⟩, hr, _⟩ := WP.spec_imp_exists (code.read_i32_const.spec st data hsize)
  cases r with
  | Err e =>
    refine ⟨(.Err e, st', v), ?_⟩
    simp [code.step, code.OP_I32_CONST, code.OP_NOP, code.OP_UNREACHABLE, hr,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    obtain ⟨⟨r, v'⟩, hv⟩ := hvisit st' value
    cases r with
    | Ok u =>
      cases u
      exact ⟨_, code.step_i32_const visitor st st' data env ctx value v v' hr hv⟩
    | Err e =>
      exact ⟨_, code.step_i32_const.visitor_rejected visitor st st' data env ctx value v v' e hr hv⟩

end Itasca

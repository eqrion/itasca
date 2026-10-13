import Itasca.Handler.SignedConst
import Itasca.Binary.SignedLeb64
import Itasca.Binary.FloatBits
import Itasca.Visitor.Basic
import Itasca.Spec.ScalarConst

/-!
# `i64`, `f32` and `f64` constant handlers

Lemmas about `code.read_i64_const`, `code.read_f32_const` and `code.read_f64_const`: the effect
on the operand stack, the exact byte provenance of the decoded immediate or its rejection, and
`code.step_*_const.of_read`, which lifts these facts through `code.step` and the visitor hook.
`Sequence.TypedPrefix.i64Const`, `.f32Const` and `.f64Const` extend a typed prefix by the constant.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- If the immediate read succeeds, `code.read_i64_const advances the cursor and appends one `i64`
operand. -/
@[step]
theorem code.read_i64_const.from_read (st : code.OpIterState) (data : Slice U8)
    (value : I64) (next : Usize)
    (hread : reader.read_s64_leb data st.pos = .ok (.Ok (value, next)))
    (hsize : st.vals.val.length < Usize.max) :
    code.read_i64_const st data ⦃ r => r.1 = .Ok value ∧
      r.2.vals.val = st.vals.val ++ [.Val .I64] ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = next ⦄ := by
  rw [code.read_i64_const, hread]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*

/-- A malformed immediate makes `code.read_i64_const` fail and leave the validator state
unchanged. -/
theorem code.read_i64_const.failed_read (st : code.OpIterState) (data : Slice U8)
    (e : error.OpError) (hread : reader.read_s64_leb data st.pos = .ok (.Err e)) :
    code.read_i64_const st data = .ok (.Err e, st) := by
  simp [code.read_i64_const, hread, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `code.read_i64_const` terminates, with exact byte provenance for the decoded value or the
rejection, when the push fits. -/
@[step]
theorem code.read_i64_const.spec (st : code.OpIterState) (data : Slice U8)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_i64_const st data ⦃ r => r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok value => SignedLeb64.Decoded data st.pos value.val r.2.pos ∧
          r.2.vals.val = st.vals.val ++ [.Val .I64]
      | .Err e => SignedLeb64.Rejected data st.pos e ∧ r.2 = st ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_s64_leb.spec data st.pos)
  cases r with
  | Err e =>
    rw [code.read_i64_const.failed_read st data e hr]
    simp only [WP.spec_ok]
    exact ⟨trivial, hp, trivial⟩
  | Ok r =>
    rcases r with ⟨value, next⟩
    obtain ⟨r, hresult, hok, hv, hc, hpos⟩ := WP.spec_imp_exists
      (code.read_i64_const.from_read st data value next hr hsize)
    rw [hresult]
    simp only [WP.spec_ok, hok, hpos]
    exact ⟨hc, hp, hv⟩

/-- If the immediate read succeeds, `code.read_f32_const` advances the cursor and appends one `f32`
operand. -/
@[step]
theorem code.read_f32_const.from_read (st : code.OpIterState) (data : Slice U8)
    (value : U32) (next : Usize)
    (hread : reader.read_f32_bits data st.pos = .ok (.Ok (value, next)))
    (hsize : st.vals.val.length < Usize.max) :
    code.read_f32_const st data ⦃ r => r.1 = .Ok value ∧
      r.2.vals.val = st.vals.val ++ [.Val .F32] ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = next ⦄ := by
  rw [code.read_f32_const, hread]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*

/-- A malformed immediate makes `code.read_f32_const` fail and leave the validator state
unchanged. -/
theorem code.read_f32_const.failed_read (st : code.OpIterState) (data : Slice U8)
    (e : error.OpError) (hread : reader.read_f32_bits data st.pos = .ok (.Err e)) :
    code.read_f32_const st data = .ok (.Err e, st) := by
  simp [code.read_f32_const, hread, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `code.read_f32_const` terminates, with exact byte provenance for the decoded value or the
rejection, when the push fits. -/
@[step]
theorem code.read_f32_const.spec (st : code.OpIterState) (data : Slice U8)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_f32_const st data ⦃ r => r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok value => FloatBits.Decoded 4 data st.pos value.val r.2.pos ∧
          r.2.vals.val = st.vals.val ++ [.Val .F32]
      | .Err e => FloatBits.Rejected 4 data st.pos e ∧ r.2 = st ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_f32_bits.spec data st.pos)
  cases r with
  | Err e =>
    rw [code.read_f32_const.failed_read st data e hr]
    simp only [WP.spec_ok]
    exact ⟨trivial, hp, trivial⟩
  | Ok r =>
    rcases r with ⟨value, next⟩
    obtain ⟨r, hresult, hok, hv, hc, hpos⟩ := WP.spec_imp_exists
      (code.read_f32_const.from_read st data value next hr hsize)
    rw [hresult]
    simp only [WP.spec_ok, hok, hpos]
    exact ⟨hc, hp, hv⟩

/-- If the immediate read succeeds, `code.read_f64_const` advances the cursor and appends one `f64`
operand. -/
@[step]
theorem code.read_f64_const.from_read (st : code.OpIterState) (data : Slice U8)
    (value : U64) (next : Usize)
    (hread : reader.read_f64_bits data st.pos = .ok (.Ok (value, next)))
    (hsize : st.vals.val.length < Usize.max) :
    code.read_f64_const st data ⦃ r => r.1 = .Ok value ∧
      r.2.vals.val = st.vals.val ++ [.Val .F64] ∧ r.2.ctrls = st.ctrls ∧ r.2.pos = next ⦄ := by
  rw [code.read_f64_const, hread]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step*

/-- A malformed immediate makes `code.read_f64_const` fail and leave the validator state
unchanged. -/
theorem code.read_f64_const.failed_read (st : code.OpIterState) (data : Slice U8)
    (e : error.OpError) (hread : reader.read_f64_bits data st.pos = .ok (.Err e)) :
    code.read_f64_const st data = .ok (.Err e, st) := by
  simp [code.read_f64_const, hread, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `code.read_f64_const` terminates, with exact byte provenance for the decoded value or the
rejection, when the push fits. -/
@[step]
theorem code.read_f64_const.spec (st : code.OpIterState) (data : Slice U8)
    (hsize : st.vals.val.length < Usize.max) :
    code.read_f64_const st data ⦃ r => r.2.ctrls = st.ctrls ∧
      match r.1 with
      | .Ok value => FloatBits.Decoded 8 data st.pos value.val r.2.pos ∧
          r.2.vals.val = st.vals.val ++ [.Val .F64]
      | .Err e => FloatBits.Rejected 8 data st.pos e ∧ r.2 = st ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_f64_bits.spec data st.pos)
  cases r with
  | Err e =>
    rw [code.read_f64_const.failed_read st data e hr]
    simp only [WP.spec_ok]
    exact ⟨trivial, hp, trivial⟩
  | Ok r =>
    rcases r with ⟨value, next⟩
    obtain ⟨r, hresult, hok, hv, hc, hpos⟩ := WP.spec_imp_exists
      (code.read_f64_const.from_read st data value next hr hsize)
    rw [hresult]
    simp only [WP.spec_ok, hok, hpos]
    exact ⟨hc, hp, hv⟩


end Itasca

namespace Itasca.Sequence

/-- Pushing a `i64` operand extends a typed prefix by `i64.const`. -/
theorem TypedPrefix.i64Const {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C ops poly vals)
    (hC : wf_context C) (value : I64) :
    TypedPrefix C (ops ++ [ScalarConst.i64 value]) poly (vals ++ [.Val .I64]) := by
  apply h.append hC _ (ScalarConst.i64_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .I64 hout
  exact ⟨before, hb, ScalarConst.i64_framed C hC value before⟩

/-- Pushing a `f32` operand extends a typed prefix by `f32.const`. -/
theorem TypedPrefix.f32Const {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C ops poly vals)
    (hC : wf_context C) (value : U32) :
    TypedPrefix C (ops ++ [ScalarConst.f32 value]) poly (vals ++ [.Val .F32]) := by
  apply h.append hC _ (ScalarConst.f32_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .F32 hout
  exact ⟨before, hb, ScalarConst.f32_framed C hC value before⟩

/-- Pushing a `f64` operand extends a typed prefix by `f64.const`. -/
theorem TypedPrefix.f64Const {C : context} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C ops poly vals)
    (hC : wf_context C) (value : U64) :
    TypedPrefix C (ops ++ [ScalarConst.f64 value]) poly (vals ++ [.Val .F64]) := by
  apply h.append hC _ (ScalarConst.f64_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .F64 hout
  exact ⟨before, hb, ScalarConst.f64_framed C hC value before⟩

end Itasca.Sequence

namespace Itasca
private theorem i64_const_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I64_CONST v =
      CoreVisitor.run (code.read_i64_const st data) visitor.on_i64_const v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- A property of `code.read_i64_const` that holds on every outcome lifts through `code.step` on
`i64.const` and the visitor hook, given that the hook terminates. -/
theorem code.step_i64_const.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : I64 → code.OpIterState → Prop)
    (hread : code.read_i64_const st data ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : ∀ s a, ∃ result v', visitor.on_i64_const v s a = .ok (result, v')) :
    code.step visitor st data env ctx code.OP_I64_CONST v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [i64_const_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread hvisitor

private theorem f32_const_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F32_CONST v =
      CoreVisitor.run (code.read_f32_const st data) visitor.on_f32_const v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- A property of `code.read_f32_const` that holds on every outcome lifts through `code.step` on
`f32.const` and the visitor hook, given that the hook terminates. -/
theorem code.step_f32_const.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : U32 → code.OpIterState → Prop)
    (hread : code.read_f32_const st data ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : ∀ s a, ∃ result v', visitor.on_f32_const v s a = .ok (result, v')) :
    code.step visitor st data env ctx code.OP_F32_CONST v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [f32_const_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread hvisitor

private theorem f64_const_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_F64_CONST v =
      CoreVisitor.run (code.read_f64_const st data) visitor.on_f64_const v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- A property of `code.read_f64_const` that holds on every outcome lifts through `code.step` on
`f64.const` and the visitor hook, given that the hook terminates. -/
theorem code.step_f64_const.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : U64 → code.OpIterState → Prop)
    (hread : code.read_f64_const st data ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : ∀ s a, ∃ result v', visitor.on_f64_const v s a = .ok (result, v')) :
    code.step visitor st data env ctx code.OP_F64_CONST v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [f64_const_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread hvisitor


end Itasca

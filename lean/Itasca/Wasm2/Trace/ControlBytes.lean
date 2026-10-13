import Itasca.Wasm2.Trace.BodyRefinement
import Itasca.Wasm2.Trace.Basic
import Itasca.Wasm2.Control.EnterStep

open Aeneas Aeneas.Std

namespace Itasca

attribute [local step] code.pop_with_type.total code.check_suffix.spec

set_option maxHeartbeats 2000000 in
/-- The signature returned to an entry callback is exactly the independently
decoded block signature, and stack processing preserves its ending cursor. -/
theorem code.enter_info.bytes (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (kind : code.LabelKind) (hs : Control.Shape st.core)
    (hcap : st.blocks.val.length < Usize.max) :
    code.enter_info st data env kind ⦃ r => ∀ bt, r.1 = .Ok bt →
      Wasm2.BlockDecoded data st.core.pos bt r.2.core.pos ⦄ := by
  unfold code.enter_info
  obtain ⟨res, hr, hdecoded⟩ := WP.spec_imp_exists (signature.read_block_type.spec data st.core.pos)
  rw [hr]
  cases res with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨bt, next⟩ := pair
    simp only [bind_ok]
    have hbranch : core.result.Result.Insts.CoreOpsTry.branch
        (.Ok (bt, next) : core.result.Result (signature.BlockType × Usize) error.OpError) =
        .ok (.Continue (bt, next)) := rfl
    rw [hbranch]
    simp only [bind_ok]
    have hspos : Control.Shape { st.core with pos := next } := ⟨hs.ordered, hs.bounded⟩
    simp only [signature.BlockType.params.spec]
    cases bt <;> cases kind <;> step* <;> simp_all

/-- A label callback receives exactly the depth encoded at the current cursor. -/
theorem code.read_label_info.bytes (st : code.BodyState) (data : Slice U8)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.read_label_info st data ⦃ r =>
      r.2.core.vals = st.core.vals ∧ r.2.core.ctrls = st.core.ctrls ∧
      (∀ depth types, r.1 = .Ok (depth, types) →
        Leb128.Decoded data st.core.pos depth r.2.core.pos) ⦄ := by
  obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  cases r with
  | Err e => simp [code.read_label_info, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨depth, next⟩ := pair
    obtain ⟨r, hl, _⟩ := WP.spec_imp_exists
      (code.label.spec {st with core := {st.core with pos := next}} depth ha)
    cases r <;> simp [code.read_label_info, hr, hl,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Leb128.Post] at *
    all_goals assumption

set_option maxHeartbeats 1000000 in
/-- Branch operand adjustment preserves the decoded depth and cursor. -/
theorem code.branch_info.bytes (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (conditional : Bool) (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.branch_info st data env conditional ⦃ r => ∀ depth types,
      r.1 = .Ok (depth, types) → Leb128.Decoded data st.core.pos depth r.2.core.pos ⦄ := by
  unfold code.branch_info
  step with code.read_label_info.bytes st data ha as ⟨r, st1, hv, hc, hbytes⟩
  have hs' : Control.Shape st1.core :=
    ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨depth, types⟩ := pair
    have hd := hbytes depth types rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    cases conditional with
    | false =>
      simp only [Std.uncurry, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨⟨r, s⟩, hr, hshape, hc, hp, _⟩ := WP.spec_imp_exists
        (code.pop_results.total st1.core env types hs')
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
        simp only [bind_ok, Std.uncurry]
        obtain ⟨final, hf, _, _, hpos, _⟩ := WP.spec_imp_exists
          (code.mark_unreachable_total s hshape)
        change s.pos = st1.core.pos at hp
        simp [hf, hp, hpos, hd]
    | true =>
      simp only [Std.uncurry, ↓reduceIte]
      obtain ⟨⟨r, s⟩, hr, hshape, hc, hp, _⟩ := WP.spec_imp_exists
        (code.pop_with_type.total st1.core .I32 hs')
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
        simp only [bind_ok, Std.uncurry]
        obtain ⟨⟨r, s'⟩, hr, hshape', hc', hp', _⟩ := WP.spec_imp_exists
          (code.pop_results.total s env types hshape)
        rw [hr]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok u =>
          simp only [bind_ok, Std.uncurry]
          obtain ⟨⟨r, s''⟩, hr, _, hc'', hp'', _⟩ := WP.spec_imp_exists
            (code.push_results.total s' env types hshape')
          rw [hr]
          change s.pos = st1.core.pos at hp
          change s'.pos = s.pos at hp'
          change s''.pos = s'.pos at hp''
          cases r <;> simp [
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            hp, hp', hp'', hd]


end Itasca

namespace Itasca.Wasm2.CallbackTrace

open VisitorTrace

/-- A metadata-producing control handler followed by its one named callback. -/
def bodyRun {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.BodyState))
    (visitor : code.OpVisitor V) (action : A → Action) (v : V) :
    Result (BodyResult × code.BodyState × V) := do
  let (result, state) ← read
  match result with
  | .Err error => .ok (.Err error, state, v)
  | .Ok a =>
    let (reply, v') ← invoke visitor v (.op state.core (action a))
    .ok (hookResult reply, state, v')

/-- Exact independent byte provenance for any factored control handler. -/
theorem bodyRun.trace {A V : Type} (data : Slice U8) (start : Usize)
    (read : Result (core.result.Result A error.OpError × code.BodyState))
    (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (action : A → Action)
    (hbytes : ∀ s a, read = .ok (.Ok a, s) → ∃ token,
      actionToken (action a) [] = some token ∧ (action a).opcode ≠ some 0x0E#u8 ∧
      At data start token s.core.pos)
    (v : V) (result : BodyResult) (final : code.BodyState) (v' : V)
    (h : bodyRun read visitor action v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      StepTrace data start observations result final.core := by
  unfold bodyRun at h
  obtain ⟨⟨r, s⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases r with
  | Err e =>
    simp only [Std.uncurry, Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨[], by simp, .silent e s.core (.empty _)⟩
  | Ok a =>
    obtain ⟨⟨reply, w⟩, hv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    simp only [Std.uncurry, Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨token, ht, hn, hb⟩ := hbytes s a hr
    exact ⟨[⟨.op s.core (action a), reply⟩], hrecords v _ reply w hv,
      .complete (.single s.core (action a) reply token ht hn hb)
        (by cases reply <;> exact Outcomes.single _ _)⟩

end Itasca.Wasm2.CallbackTrace

namespace Itasca.Wasm2.CallbackTrace

open VisitorTrace

theorem dispatch_block {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index .Wasm2 0x02#u8 v =
      bodyRun (code.enter_info st data env .Block) visitor (Action.block) v := by
  simp [code.step_profile, global_simps, bodyRun, invoke,
    core.result.Result.Insts.CoreOpsTry.branch, code.visit,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp
  congr 1
  funext pair
  obtain ⟨reply, w⟩ := pair
  cases reply <;> simp [hookResult]


theorem dispatch_loop {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index .Wasm2 0x03#u8 v =
      bodyRun (code.enter_info st data env .Loop) visitor (Action.loop) v := by
  simp [code.step_profile, global_simps, bodyRun, invoke,
    core.result.Result.Insts.CoreOpsTry.branch, code.visit,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp
  congr 1
  funext pair
  obtain ⟨reply, w⟩ := pair
  cases reply <;> simp [hookResult]


theorem dispatch_if {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index .Wasm2 0x04#u8 v =
      bodyRun (code.enter_info st data env .Then) visitor (Action.if_) v := by
  simp [code.step_profile, global_simps, bodyRun, invoke,
    core.result.Result.Insts.CoreOpsTry.branch, code.visit,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp
  congr 1
  funext pair
  obtain ⟨reply, w⟩ := pair
  cases reply <;> simp [hookResult]


theorem dispatch_else {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index .Wasm2 0x05#u8 v =
      bodyRun (code.end_frame_info st env true) visitor (fun a => Action.else_ a.2) v := by
  simp [code.step_profile, global_simps, bodyRun, invoke,
    core.result.Result.Insts.CoreOpsTry.branch, code.visit,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp
  rename_i a
  obtain ⟨a, b⟩ := a
  simp only [Std.uncurry]
  congr 1
  funext pair
  obtain ⟨reply, w⟩ := pair
  cases reply <;> simp [hookResult]


theorem dispatch_end {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index .Wasm2 0x0b#u8 v =
      bodyRun (code.end_frame_info st env false) visitor (fun a => Action.end_ a.1 a.2) v := by
  simp [code.step_profile, global_simps, bodyRun, invoke,
    core.result.Result.Insts.CoreOpsTry.branch, code.visit,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp
  rename_i a
  obtain ⟨a, b⟩ := a
  simp only [Std.uncurry]
  congr 1
  funext pair
  obtain ⟨reply, w⟩ := pair
  cases reply <;> simp [hookResult]


theorem dispatch_br {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index .Wasm2 0x0c#u8 v =
      bodyRun (code.branch_info st data env false) visitor (fun a => Action.br a.1 a.2) v := by
  simp [code.step_profile, global_simps, bodyRun, invoke,
    core.result.Result.Insts.CoreOpsTry.branch, code.visit,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp
  rename_i a
  obtain ⟨a, b⟩ := a
  simp only [Std.uncurry]
  congr 1
  funext pair
  obtain ⟨reply, w⟩ := pair
  cases reply <;> simp [hookResult]


theorem dispatch_br_if {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index .Wasm2 0x0d#u8 v =
      bodyRun (code.branch_info st data env true) visitor (fun a => Action.br_if a.1 a.2) v := by
  simp [code.step_profile, global_simps, bodyRun, invoke,
    core.result.Result.Insts.CoreOpsTry.branch, code.visit,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp
  rename_i a
  obtain ⟨a, b⟩ := a
  simp only [Std.uncurry]
  congr 1
  funext pair
  obtain ⟨reply, w⟩ := pair
  cases reply <;> simp [hookResult]


theorem dispatch_call {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index .Wasm2 0x10#u8 v =
      bodyRun (code.call_info st data env) visitor (Action.call) v := by
  simp [code.step_profile, global_simps, bodyRun, invoke,
    core.result.Result.Insts.CoreOpsTry.branch, code.visit,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp
  congr 1
  funext pair
  obtain ⟨reply, w⟩ := pair
  cases reply <;> simp [hookResult]


theorem dispatch_call_indirect {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index .Wasm2 0x11#u8 v =
      bodyRun (code.call_indirect_info st data env) visitor (fun a => Action.call_indirect a.1 a.2) v := by
  simp [code.step_profile, global_simps, bodyRun, invoke,
    core.result.Result.Insts.CoreOpsTry.branch, code.visit,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp
  rename_i a
  obtain ⟨a, b⟩ := a
  simp only [Std.uncurry]
  congr 1
  funext pair
  obtain ⟨reply, w⟩ := pair
  cases reply <;> simp [hookResult]


end Itasca.Wasm2.CallbackTrace

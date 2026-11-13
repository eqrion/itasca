import Itasca.Wasm2.Trace.BytesReferences
import Itasca.Wasm2.Visitor.Transfer
import Itasca.Wasm2.Control.EnterStep
import Itasca.Wasm2.Control.Return

/-!
Sections, each formerly its own module: BodyRefinement, ControlBytes, ControlRecords.
-/

/-! ## BodyRefinement -/

section

/-!
# Exact refinement of the body loop

Lifts exact callback refinement to one body iteration (`body.refines`), the body loop
(`code.body_loop_loop.refines`) and `code.validate_body_with.refines`, which preserves
every ordinary outcome including rejection. `instrument_forward` and
`instrument_backward` show that wrapping a visitor with `instrument` leaves the outcome and
visitor state unchanged and appends exactly the observed callbacks.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca.Wasm2.Visitor

open VisitorTrace

/-- The visitor state of one body iteration result. -/
def bodyVisitor {V : Type} :
    ControlFlow (V × code.BodyState) (core.result.Result Unit error.OpError × V) → V
  | .cont (v, _) => v
  | .done (_, v) => v

/-- Exact callback refinement of one body iteration preserves both validator and
visitor state, regardless of whether the iteration accepts or rejects. -/
theorem body.refines {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (related : V → W → Prop)
    (hrefines : Refines visitor replacement related)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
     (st : code.BodyState) (v : V) (w : W) (hrelated : related v w) (cf)
    (h : body visitor data env ctx index v st = .ok cf) :
    ∃ cf', body replacement data env ctx index w st = .ok cf' ∧
      bodyObserve cf' = bodyObserve cf ∧ related (bodyVisitor cf) (bodyVisitor cf') := by
  unfold body code.body_loop_loop.body at h ⊢
  simp only [alloc.vec.Vec.is_empty, bind_ok] at h ⊢
  split at h
  · rename_i he
    simp only [he, if_true]
    split at h
    · rename_i hp
      simp only [ok.injEq] at h
      subst cf
      exact ⟨.done (.Err .TrailingBytes, w), by simp [hp], rfl, hrelated⟩
    · rename_i hp
      simp only [ok.injEq] at h
      subst cf
      exact ⟨.done (.Ok (), w), by simp [hp], rfl, hrelated⟩
  · rename_i he
    simp only [he]
    obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
      subst cf
      exact ⟨rfl, hrelated⟩
    | Ok pair =>
      obtain ⟨opcode, pos⟩ := pair
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
      obtain ⟨⟨r, s, v1⟩, hs, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      obtain ⟨w1, hw, hr1⟩ := code.step_profile.refines visitor replacement related hrefines
        { core := {st.core with pos} } data env ctx index opcode v w hrelated r s v1 hs
      rw [hw]
      cases r <;> simp [
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
      all_goals subst cf; exact ⟨rfl, hr1⟩

end Itasca.Wasm2.Visitor

namespace Itasca

open VisitorTrace Wasm2.Visitor

/-- The body loop preserves every ordinary result under exact callback refinement. The empty
visitor supplies structural progress only. -/
theorem code.body_loop_loop.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
     (st : code.BodyState) (v : V) (w : W) (hrelated : related v w)
    (hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val) (hs : Control.Shape st.core)
    (halign : st.blocks.val.length = st.core.ctrls.val.length)
    (hbound : st.blocks.val.length ≤ st.core.pos.val + 1)
    (res : core.result.Result Unit error.OpError) (v' : V)
    (h : code.body_loop_loop visitor data env ctx index v st = .ok (res, v')) :
    ∃ w', code.body_loop_loop replacement data env ctx index w st = .ok (res, w') ∧
      related v' w' := by
  generalize hn : Usize.max - st.core.pos.val = n
  induction n using Nat.strong_induction_on generalizing st v w with
  | h n ih =>
    unfold code.body_loop_loop at h ⊢
    rw [loop] at h ⊢
    simp only at h ⊢
    obtain ⟨cf, hb, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
    obtain ⟨cf', hw, ho, hr⟩ := body.refines visitor replacement related hrefines
      data env ctx index st v w hrelated cf hb
    simp only [Wasm2.Visitor.body] at hw
    rw [hw]
    cases cf with
    | done pair =>
      obtain ⟨r, v1⟩ := pair
      simp only [ok.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      cases cf' with
      | cont p => simp [bodyObserve] at ho
      | done p =>
        obtain ⟨r, w'⟩ := p
        simp only [bodyObserve, ControlFlow.done.injEq] at ho
        subst r
        exact ⟨w', by simp, hr⟩
    | cont pair =>
      obtain ⟨v1, s⟩ := pair
      obtain ⟨emptyCf, he, heo⟩ := body.transfer visitor code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
        FullVisitor.empty_accepts data env ctx ctx rfl index st v () _ hb trivial
      have hp := code.body_loop_loop.body.total
        code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total
        data env ctx index st () hdata hs halign hbound
      simp only [Wasm2.Visitor.body] at he
      rw [he, WP.spec_ok] at hp
      cases emptyCf with
      | done p => simp [bodyObserve] at heo
      | cont p =>
        obtain ⟨ev, es⟩ := p
        simp only [bodyObserve, ControlFlow.cont.injEq] at heo
        subst es
        obtain ⟨hinv, hdecr⟩ := hp
        dsimp only at hinv hdecr
        cases cf' with
        | done p => simp [bodyObserve] at ho
        | cont p =>
          obtain ⟨w1, s'⟩ := p
          simp only [bodyObserve, ControlFlow.cont.injEq] at ho
          subst s'
          obtain ⟨w', hw', hr'⟩ := ih (Usize.max - s.core.pos.val) (by omega) s v1 w1 hr
            hinv.1 hinv.2.1 hinv.2.2 ht rfl
          exact ⟨w', by simpa only [bind_ok, code.body_loop_loop, Std.uncurry] using hw', hr'⟩

/-- Callback refinement preserves every ordinary public body outcome.
No valid-byte, well-typed-context, or total-callback premise is assumed. -/
theorem code.validate_body_with.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
     (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (v' : V)
    (h : code.validate_body_with visitor data env ctx index v = .ok (res, v')) :
    ∃ w', code.validate_body_with replacement data env ctx index w =
      .ok (res, w') ∧ related v' w' := by
  unfold code.validate_body_with at h ⊢
  by_cases hsize : Slice.len data > limits.MAX_FUNCTION_BYTES
  · simp [hsize] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hrelated⟩
  · simp only [hsize, if_false] at h ⊢
    obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hrelated⟩
    | Ok st =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, code.body_loop] at h ⊢
      have hp := code.initial_state.total env index
      rw [hr, WP.spec_ok] at hp
      exact code.body_loop_loop.refines visitor replacement related hrefines
        data env ctx index st v w hrelated (by scalar_tac) hp.1 hp.2.1 hp.2.2 res v' h

/-- Instrumenting body validation preserves its exact outcome and underlying visitor state and
appends the actual callbacks, including rejection. -/
theorem code.validate_body_with.instrument_forward {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (v : V)
    (log : List Observation) (res : core.result.Result Unit error.OpError) (v' : V)
    (h : code.validate_body_with visitor data env ctx index v = .ok (res, v')) :
    ∃ added, code.validate_body_with (instrument visitor) data env ctx index
      (v, log) = .ok (res, (v', log ++ added)) := by
  obtain ⟨⟨w, out⟩, hw, he, added, hl⟩ := code.validate_body_with.refines
    visitor (instrument visitor) _ (instrument_refines visitor log)
    data env ctx index v (v, log) ⟨rfl, [], by simp⟩ res v' h
  dsimp only at he hl
  subst w
  subst out
  exact ⟨added, hw⟩

end Itasca

end

/-! ## ControlBytes -/

section

/-!
# Byte provenance for control handlers

Byte lemmas for the extracted control helpers (`code.enter_info.bytes`,
`code.read_label_info.bytes`, `code.branch_info.bytes`), and `bodyRun.trace`, which gives an exact `StepTrace` for any control
handler followed by one named callback. `dispatch_block`, `dispatch_loop`, `dispatch_if`,
`dispatch_else`, `dispatch_end`, `dispatch_br`, `dispatch_br_if`, `dispatch_call` and
`dispatch_call_indirect` factor the profile dispatcher into such handlers.
-/

open Aeneas Aeneas.Std

namespace Itasca

attribute [local step] code.pop_with_type.total code.check_suffix.spec

set_option maxHeartbeats 2000000 in
/-- The signature returned to an entry callback is exactly the independently
decoded block signature, and stack processing preserves its ending cursor. -/
theorem code.enter_info.bytes (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (kind : code.LabelKind)
    (hs : Control.Shape st.core) (hcap : st.blocks.val.length < Usize.max) :
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
    (env : metadata.Env) (conditional : Bool) (hs : Control.Shape st.core)
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
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index 0x02#u8 v =
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
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index 0x03#u8 v =
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
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index 0x04#u8 v =
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
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index 0x05#u8 v =
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
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index 0x0b#u8 v =
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
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index 0x0c#u8 v =
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
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index 0x0d#u8 v =
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
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index 0x10#u8 v =
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
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index 0x11#u8 v =
      bodyRun (code.call_indirect_info st data env ) visitor (fun a => Action.call_indirect a.1 a.2) v := by
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

end

/-! ## ControlRecords -/

section

/-!
# Callback byte provenance for control instructions

`ProfileStepRecords` states the exact callback trace of one control step of `code.step_profile`. `step_block`, `step_loop`, `step_if`, `step_else`, `step_end`, `step_br`,
`step_br_if`, `step_return`, `step_call` and `step_call_indirect` prove it for each control
opcode except `br_table`, which is in `Wasm2/Trace/TableBytes`.
-/

open Aeneas Aeneas.Std

namespace Itasca

attribute [local step] code.pop_with_type.total code.check_suffix.spec

/-- Call stack adjustment returns the exact encoded function index. -/
theorem code.call_info.bytes (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (hs : Control.Shape st.core) :
    code.call_info st data env ⦃ r => ∀ index, r.1 = .Ok index →
      Leb128.Decoded data st.core.pos index r.2.core.pos ⦄ := by
  unfold code.call_info
  step with code.take_index.spec st.core data as ⟨r, s, hv, hc, hd⟩
  have hs' : Control.Shape s :=
    ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩
  cases r <;> step*; simp_all

/-- Indirect-call callbacks receive both independently decoded indices. -/
theorem code.call_indirect_info.bytes (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (hs : Control.Shape st.core) :
    code.call_indirect_info st data env ⦃ r => ∀ index table, r.1 = .Ok (index, table) →
      ∃ middle, Leb128.Decoded data st.core.pos index middle ∧
        Leb128.Decoded data middle table r.2.core.pos ⦄ := by
  unfold code.call_indirect_info
  step with code.take_index.spec st.core data as ⟨r, s, hv, hc, hd⟩
  have hs' : Control.Shape s :=
    ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok index =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with code.take_index.spec s data as ⟨r, s', hv', hc', hd'⟩
    have hs'' : Control.Shape s' :=
      ⟨by simpa [hc'] using hs'.ordered, by simpa [hc', hv'] using hs'.bounded⟩
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok table =>
      simp only [bind_ok]
      step*
      simp_all
      cases ‹core.result.Result code.StackType error.OpError› with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok value =>
        simp only [bind_ok]
        step*
        simp_all
        cases ‹core.result.Result Unit error.OpError› with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok value =>
          simp only [bind_ok, WP.spec_ok]
          intro idx tab equal
          obtain ⟨rfl, rfl⟩ := (core.result.Result.Ok.inj equal)
          exact ⟨s.pos, hd, by simpa [*] using hd'⟩

end Itasca

namespace Itasca.Wasm2.CallbackTrace

open VisitorTrace

/-- Exact bytes for an actual profile-dispatched control step. -/
def ProfileStepRecords {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (ctx : code.Context) (opcode : U8) : Prop :=
  ∀ v result final v', code.step_profile visitor st data env ctx index opcode v =
      .ok (result, final, v') →
    ∃ observations, observe v' = observe v ++ observations ∧
      StepTrace data p.start observations result final.core

theorem step_block {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x02#u8) :
    ProfileStepRecords p visitor observe ctx 0x02#u8 := by
  intro v result final v' run
  rw [dispatch_block] at run
  apply bodyRun.trace data p.start _ visitor observe records .block ?_ v result final v' run
  intro state bt hr
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  have spec := code.enter_info.bytes st data env .Block p.opened.shape.core capacity
  rw [hr, WP.spec_ok] at spec
  exact ⟨.block bt, rfl, by simp [Action.opcode],
    At.of_block_type bt p.inbounds byte p.pos (fun _ h => .block h) (spec bt rfl)⟩

theorem step_loop {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x03#u8) :
    ProfileStepRecords p visitor observe ctx 0x03#u8 := by
  intro v result final v' run
  rw [dispatch_loop] at run
  apply bodyRun.trace data p.start _ visitor observe records .loop ?_ v result final v' run
  intro state bt hr
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  have spec := code.enter_info.bytes st data env .Loop p.opened.shape.core capacity
  rw [hr, WP.spec_ok] at spec
  exact ⟨.loop bt, rfl, by simp [Action.opcode],
    At.of_block_type bt p.inbounds byte p.pos (fun _ h => .loop h) (spec bt rfl)⟩

theorem step_if {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x04#u8) :
    ProfileStepRecords p visitor observe ctx 0x04#u8 := by
  intro v result final v' run
  rw [dispatch_if] at run
  apply bodyRun.trace data p.start _ visitor observe records .if_ ?_ v result final v' run
  intro state bt hr
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  have spec := code.enter_info.bytes st data env .Then p.opened.shape.core capacity
  rw [hr, WP.spec_ok] at spec
  exact ⟨.if_ bt, rfl, by simp [Action.opcode],
    At.of_block_type bt p.inbounds byte p.pos (fun _ h => .if_ h) (spec bt rfl)⟩

theorem step_else {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x05#u8) :
    ProfileStepRecords p visitor observe ctx 0x05#u8 := by
  intro v result final v' run
  rw [dispatch_else] at run
  apply bodyRun.trace data p.start _ visitor observe records (fun a : code.LabelKind × signature.BlockType => .else_ a.2) ?_ v result final v' run
  intro state pair hr
  have spec := code.end_frame_info.total st env true p.opened.shape.core p.opened.shape.aligned
  rw [hr, WP.spec_ok] at spec
  have pos : state.core.pos = st.core.pos := spec.2.2.2
  refine ⟨.else_, rfl, by simp [Action.opcode], ?_⟩
  apply At.of_immediate p.inbounds byte p.pos .else_
  simpa [pos] using Wasm1.BytesAt.nil data st.core.pos (by have := p.pos; have := p.inbounds; omega)

theorem step_end {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0b#u8) :
    ProfileStepRecords p visitor observe ctx 0x0b#u8 := by
  intro v result final v' run
  rw [dispatch_end] at run
  apply bodyRun.trace data p.start _ visitor observe records (fun a : code.LabelKind × signature.BlockType => .end_ a.1 a.2) ?_ v result final v' run
  intro state pair hr
  have spec := code.end_frame_info.total st env false p.opened.shape.core p.opened.shape.aligned
  rw [hr, WP.spec_ok] at spec
  have pos : state.core.pos = st.core.pos := spec.2.2.2
  refine ⟨.end_, rfl, by simp [Action.opcode], ?_⟩
  apply At.of_immediate p.inbounds byte p.pos .end_
  simpa [pos] using Wasm1.BytesAt.nil data st.core.pos (by have := p.pos; have := p.inbounds; omega)

theorem step_br {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0c#u8) :
    ProfileStepRecords p visitor observe ctx 0x0c#u8 := by
  intro v result final v' run
  rw [dispatch_br] at run
  apply bodyRun.trace data p.start _ visitor observe records
    (fun a : U32 × signature.ResultType => .br a.1 a.2) ?_ v result final v' run
  rintro state ⟨depth, types⟩ hr
  have spec := code.branch_info.bytes st data env false p.opened.shape.core p.opened.shape.aligned
  rw [hr, WP.spec_ok] at spec
  exact ⟨.plain (.BR (.mk_uN depth.val)), rfl, by simp [Action.opcode],
    At.plain (Wasm1.At.of_u32 depth p.inbounds byte p.pos (fun _ => .br depth) (spec depth types rfl))⟩

theorem step_br_if {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0d#u8) :
    ProfileStepRecords p visitor observe ctx 0x0d#u8 := by
  intro v result final v' run
  rw [dispatch_br_if] at run
  apply bodyRun.trace data p.start _ visitor observe records
    (fun a : U32 × signature.ResultType => .br_if a.1 a.2) ?_ v result final v' run
  rintro state ⟨depth, types⟩ hr
  have spec := code.branch_info.bytes st data env true p.opened.shape.core p.opened.shape.aligned
  rw [hr, WP.spec_ok] at spec
  exact ⟨.plain (.BR_IF (.mk_uN depth.val)), rfl, by simp [Action.opcode],
    At.plain (Wasm1.At.of_u32 depth p.inbounds byte p.pos (fun _ => .brIf depth) (spec depth types rfl))⟩

theorem step_call {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x10#u8) :
    ProfileStepRecords p visitor observe ctx 0x10#u8 := by
  intro v result final v' run
  rw [dispatch_call] at run
  apply bodyRun.trace data p.start _ visitor observe records .call ?_ v result final v' run
  intro state idx hr
  have spec := code.call_info.bytes st data env p.opened.shape.core
  rw [hr, WP.spec_ok] at spec
  exact ⟨.plain (.CALL (.mk_uN idx.val)), rfl, by simp [Action.opcode],
    At.plain (Wasm1.At.of_u32 idx p.inbounds byte p.pos (fun _ => .call idx) (spec idx rfl))⟩

theorem step_call_indirect {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x11#u8) :
    ProfileStepRecords p visitor observe ctx 0x11#u8 := by
  intro v result final v' run
  rw [dispatch_call_indirect] at run
  apply bodyRun.trace data p.start _ visitor observe records
    (fun a : U32 × U32 => .call_indirect a.1 a.2) ?_ v result final v' run
  rintro state ⟨idx, table⟩ hr
  have spec := code.call_indirect_info.bytes st data env p.opened.shape.core
  rw [hr, WP.spec_ok] at spec
  obtain ⟨middle, hidx, htable⟩ := spec idx table rfl
  obtain ⟨typeBytes, hs, hl, hb, he⟩ := hidx
  obtain ⟨tableBytes, hs', hl', hb', he'⟩ := htable
  exact ⟨.plain (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val)), rfl,
    by simp [Action.opcode], At.of_immediate p.inbounds byte p.pos
      (.reference (.callIndirect idx table he he'))
      ((show Wasm1.BytesAt data st.core.pos typeBytes middle from ⟨hs, hl, hb⟩).append ⟨hs', hl', hb'⟩)⟩

end Itasca.Wasm2.CallbackTrace

open Aeneas Aeneas.Std
namespace Itasca.Wasm2.CallbackTrace
open VisitorTrace

/-- Factor the actual return callback after result checking and stack erasure. -/
theorem dispatch_return {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index 0x0f#u8 v =
      bodyRun (returnStep st env index) visitor (fun _ => .return_) v := by
  simp [code.step_profile, global_simps, bodyRun, returnStep, Std.bind_assoc, Std.uncurry,
    core.result.Result.Insts.CoreOpsTry.branch, code.visit,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r with
  | Err e => simp
  | Ok u =>
    cases u
    simp only [bind_ok, Std.bind_assoc, Std.uncurry]
    congr 1
    funext state
    simp only [invoke]
    congr 1
    funext pair
    obtain ⟨reply, w⟩ := pair
    cases reply <;> simp [hookResult]

/-- Return reads no immediate bytes; checking results and erasing the active
stack segment preserve its post-opcode cursor. -/
theorem return_position (st : code.BodyState) (env : metadata.Env) (index : U32)
    (shape : Control.Shape st.core) :
    returnStep st env index ⦃ r => r.2.core.pos = st.core.pos ⦄ := by
  obtain ⟨⟨res, popped⟩, hp, hs, _, hpos, _⟩ := WP.spec_imp_exists
    (code.pop_results.total st.core env (.Type index .Results) shape)
  dsimp only at hs hpos
  cases res with
  | Err e => simpa [returnStep, hp] using hpos
  | Ok u =>
    cases u
    obtain ⟨marked, hm, _, _, hmark, _⟩ := WP.spec_imp_exists
      (code.mark_unreachable_total popped hs)
    simpa [returnStep, hp, hm] using hmark.trans hpos

theorem step_return {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0f#u8) :
    ProfileStepRecords p visitor observe ctx 0x0f#u8 := by
  intro v result final v' run
  rw [dispatch_return] at run
  apply bodyRun.trace data p.start _ visitor observe records (fun _ => .return_) ?_ v result final v' run
  intro state _ hr
  have spec := return_position st env index p.opened.shape.core
  rw [hr, WP.spec_ok] at spec
  dsimp only at spec
  refine ⟨.plain .RETURN, rfl, by simp [Action.opcode], ?_⟩
  exact At.plain (.no_immediate p.inbounds byte (by simpa [spec] using p.pos) .return_)

end Itasca.Wasm2.CallbackTrace

end

import Itasca.Wasm2.Trace.ControlRefinement
import Itasca.Wasm2.Visitor.Transfer

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
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (profile : ValidationProfile) (st : code.BodyState) (v : V) (w : W) (hrelated : related v w) (cf)
    (h : body visitor data env ctx index profile v st = .ok cf) :
    ∃ cf', body replacement data env ctx index profile w st = .ok cf' ∧
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
        { core := {st.core with pos} } data env ctx index profile opcode v w hrelated r s v1 hs
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
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (profile : ValidationProfile) (st : code.BodyState) (v : V) (w : W) (hrelated : related v w)
    (hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val) (hs : Control.Shape st.core)
    (halign : st.blocks.val.length = st.core.ctrls.val.length)
    (hbound : st.blocks.val.length ≤ st.core.pos.val + 1)
    (res : core.result.Result Unit error.OpError) (v' : V)
    (h : code.body_loop_loop visitor data env ctx index profile v st = .ok (res, v')) :
    ∃ w', code.body_loop_loop replacement data env ctx index profile w st = .ok (res, w') ∧
      related v' w' := by
  generalize hn : Usize.max - st.core.pos.val = n
  induction n using Nat.strong_induction_on generalizing st v w with
  | h n ih =>
    unfold code.body_loop_loop at h ⊢
    rw [loop] at h ⊢
    simp only at h ⊢
    obtain ⟨cf, hb, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
    obtain ⟨cf', hw, ho, hr⟩ := body.refines visitor replacement related hrefines
      data env ctx index profile st v w hrelated cf hb
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
        FullVisitor.empty_accepts data env ctx ctx rfl index profile st v () _ hb trivial
      have hp := code.body_loop_loop.body.total
        code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total
        data env ctx index profile st () hdata hs halign hbound
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
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (profile : ValidationProfile) (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (v' : V)
    (h : code.validate_body_with visitor data env ctx index profile v = .ok (res, v')) :
    ∃ w', code.validate_body_with replacement data env ctx index profile w =
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
        data env ctx index profile st v w hrelated (by scalar_tac) hp.1 hp.2.1 hp.2.2 res v' h

/-- Instrumenting body validation preserves its exact outcome and underlying visitor state and
appends the actual callbacks, including rejection. -/
theorem code.validate_body_with.instrument_forward {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (profile : ValidationProfile) (v : V)
    (log : List Observation) (res : core.result.Result Unit error.OpError) (v' : V)
    (h : code.validate_body_with visitor data env ctx index profile v = .ok (res, v')) :
    ∃ added, code.validate_body_with (instrument visitor) data env ctx index profile
      (v, log) = .ok (res, (v', log ++ added)) := by
  obtain ⟨⟨w, out⟩, hw, he, added, hl⟩ := code.validate_body_with.refines
    visitor (instrument visitor) _ (instrument_refines visitor log)
    data env ctx index profile v (v, log) ⟨rfl, [], by simp⟩ res v' h
  dsimp only at he hl
  subst w
  subst out
  exact ⟨added, hw⟩

end Itasca

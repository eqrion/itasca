import Itasca.Wasm2.Visitor.Step
import Itasca.Wasm2.Visitor.Total
import Itasca.Wasm2.Scalar.Complete
import Itasca.Wasm2.Soundness
import Itasca.Wasm2.Completeness

/-!
# Visitor transfer for the body loop

`body.transfer` shows that one successful iteration of the extracted body loop transfers to a
replacement visitor with accepting callbacks, with the same validator state. This lifts to the
whole loop (`code.body_loop_loop.wasm2_accepted_transfer`) and to
`code.validate_multi_value_body_with.accepted_transfer`, which includes the size guard and
initialization.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca.Wasm2.Visitor

/-- Drops the visitor state from the result of one body iteration. -/
def bodyObserve {V : Type} :
    ControlFlow (V × code.BodyState) (core.result.Result Unit error.OpError × V) →
    ControlFlow code.BodyState (core.result.Result Unit error.OpError)
  | .cont (_, s) => .cont s
  | .done (r, _) => .done r

/-- A body iteration result that continues or returns `Ok ()`. -/
def bodyGood {V : Type} (cf :
    ControlFlow (V × code.BodyState) (core.result.Result Unit error.OpError × V)) : Prop :=
  match cf with
  | .cont _ => True
  | .done (r, _) => r = .Ok ()

/-- One iteration of the extracted body loop at `.Wasm2`. -/
abbrev body {V : Type} (visitor : code.OpVisitor V) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) (st : code.BodyState) :=
  code.body_loop_loop.body visitor data env ctx index .Wasm2 v st

set_option maxHeartbeats 2000000 in
/-- Each successful body iteration transfers to an accepting visitor with the
same validator state. Only the locals component of the scalar context matters. -/
theorem body.transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : FullVisitor.Accepts replacement)
    (data : Slice U8) (env : module.Env) (ctx ctx' : code.Context)
    (hlocals : ctx.locals = ctx'.locals) (index : U32) (st : code.BodyState)
    (v : V) (w : W) (cf)
    (h : body visitor data env ctx index v st = .ok cf) (hg : bodyGood cf) :
    ∃ cf', body replacement data env ctx' index w st = .ok cf' ∧
      bodyObserve cf' = bodyObserve cf := by
  unfold body code.body_loop_loop.body at h ⊢
  simp only [alloc.vec.Vec.is_empty, bind_ok] at h ⊢
  split at h
  · rename_i he
    simp only [he, if_true]
    split at h
    · simp only [ok.injEq] at h
      subst cf
      simp [bodyGood] at hg
    · rename_i hp
      simp only [ok.injEq] at h
      subst cf
      exact ⟨.done (.Ok (), w), by simp [hp], rfl⟩
  · rename_i he
    simp only [he]
    obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      subst cf
      simp [bodyGood] at hg
    | Ok pair =>
      obtain ⟨opcode, pos⟩ := pair
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
      obtain ⟨⟨r, s, v'⟩, hs, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
        subst cf
        simp [bodyGood] at hg
      | Ok u =>
        cases u
        simp at h
        subst cf
        obtain ⟨w', hw⟩ := step_transfer visitor replacement ha data env ctx ctx'
          hlocals index opcode { core := { st.core with pos } } s v w v' hs
        exact ⟨.cont (w', s), by simp [hw], rfl⟩

end Itasca.Wasm2.Visitor

namespace Itasca

open Wasm2.Visitor

/-- Visitor replacement preserves an accepted body loop. Structural progress is
obtained from the accepting replacement, so the source needs no totality premise. -/
theorem code.body_loop_loop.wasm2_accepted_transfer {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (ha : FullVisitor.Accepts replacement) (data : Slice U8) (env : module.Env)
    (ctx ctx' : code.Context) (hlocals : ctx.locals = ctx'.locals) (index : U32)
    (st : code.BodyState) (v : V) (w : W) (v' : V)
    (hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val) (hs : Control.Shape st.core)
    (halign : st.blocks.val.length = st.core.ctrls.val.length)
    (hbound : st.blocks.val.length ≤ st.core.pos.val + 1)
    (h : code.body_loop_loop visitor data env ctx index .Wasm2 v st =
      .ok (.Ok (), v')) :
    ∃ w', code.body_loop_loop replacement data env ctx' index .Wasm2 w st =
      .ok (.Ok (), w') := by
  generalize hn : Usize.max - st.core.pos.val = n
  induction n using Nat.strong_induction_on generalizing st v w with
  | h n ih =>
    unfold code.body_loop_loop at h ⊢
    rw [loop] at h ⊢
    simp only at h ⊢
    obtain ⟨cf, hb, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases cf with
    | done pair =>
      obtain ⟨r, v1⟩ := pair
      simp only [ok.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      obtain ⟨cf, hw, ho⟩ := body.transfer visitor replacement ha data env ctx ctx' hlocals
        index st v w _ hb rfl
      simp only [Wasm2.Visitor.body] at hw
      rw [hw]
      cases cf with
      | cont p => simp [bodyObserve] at ho
      | done p =>
        obtain ⟨r, w'⟩ := p
        simp only [bodyObserve, ControlFlow.done.injEq] at ho
        subst r
        exact ⟨w', by simp⟩
    | cont pair =>
      obtain ⟨v1, s⟩ := pair
      obtain ⟨cf, hw, ho⟩ := body.transfer visitor replacement ha data env ctx ctx' hlocals
        index st v w _ hb trivial
      have hp := code.body_loop_loop.body.wasm2_total replacement ha.toTotal
        data env ctx' index st w hdata hs halign hbound
      simp only [Wasm2.Visitor.body] at hw
      rw [hw, WP.spec_ok] at hp
      rw [hw]
      cases cf with
      | done p => simp [bodyObserve] at ho
      | cont p =>
        obtain ⟨w1, s'⟩ := p
        simp only [bodyObserve, ControlFlow.cont.injEq] at ho
        subst s'
        obtain ⟨hinv, hdecr⟩ := hp
        dsimp only at hinv hdecr
        obtain ⟨w', hw'⟩ := ih (Usize.max - s.core.pos.val) (by omega) s v1 w1
          hinv.1 hinv.2.1 hinv.2.2 ht rfl
        exact ⟨w', by simpa only [bind_ok, code.body_loop_loop, Std.uncurry] using hw'⟩

/-- The public size guard, signature checks, and shared initialization preserve
successful execution under accepting callback replacement. -/
theorem code.validate_multi_value_body_with.accepted_transfer {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (ha : FullVisitor.Accepts replacement) (data : Slice U8) (env : module.Env)
    (ctx ctx' : code.Context) (hlocals : ctx.locals = ctx'.locals) (index : U32)
    (v : V) (w : W) (v' : V)
    (h : code.validate_multi_value_body_with visitor data env ctx index v = .ok (.Ok (), v')) :
    ∃ w', code.validate_multi_value_body_with replacement data env ctx' index w = .ok (.Ok (), w') := by
  unfold code.validate_multi_value_body_with code.validate_body_with_profile at h ⊢
  by_cases hsize : Slice.len data > limits.MAX_FUNCTION_BYTES
  · simp [hsize] at h
  · simp only [hsize, if_false] at h ⊢
    obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    have hi : code.initial_state env ctx' index .Wasm2 =
        code.initial_state env ctx index .Wasm2 := rfl
    rw [hi, hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok st =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, code.body_loop] at h ⊢
      have hp := code.initial_state.wasm2_total env ctx index
      rw [hr, WP.spec_ok] at hp
      exact code.body_loop_loop.wasm2_accepted_transfer visitor replacement ha
        data env ctx ctx' hlocals index st v w v' (by scalar_tac) hp.1 hp.2.1 hp.2.2 h

end Itasca

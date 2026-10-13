import Itasca.Support.Result
import Itasca.Visitor.StepRefinement
import Itasca.Wasm1.Visitor.Erasure

/-!
# Visitor refinement and instrumentation (Wasm 1.0)

If a replacement visitor refines a visitor (`Refines`), `code.validate_body_with` returns the same
outcome with either (`code.validate_body_with.refines`). The `instrument` wrapper that appends
`Observation`s is a refinement, so instrumenting preserves the result and the underlying visitor
state (`instrument_forward`, `instrument_backward`, `instrument_iff`).
-/

open Aeneas Aeneas.Std

namespace Itasca

open VisitorTrace

/-- Successful empty-visitor steps supply byte progress. Callback refinement then preserves
every returned outcome of the body loop, including rejection. -/
theorem code.validate_body_with_loop.refines_of_contract {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (inv : code.OpIterState → Prop)
    (hstep : Wasm1.Loop.StepContract code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx (fun _ st => inv st))
    (st : code.OpIterState) (v : V) (w : W) (hi : inv st) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (v' : V)
    (h : code.validate_body_with_loop visitor data env ctx.locals ctx.results v st =
      .ok (res, v')) :
    ∃ w', code.validate_body_with_loop replacement data env ctx.locals ctx.results w st =
      .ok (res, w') ∧ related v' w' := by
  generalize hn : data.length - st.pos.val = n
  induction n using Nat.strong_induction_on generalizing st v w with
  | h n ih =>
    unfold code.validate_body_with_loop at h ⊢
    rw [loop] at h ⊢
    simp only [code.validate_body_with_loop.body, code.control_stack_empty,
      alloc.vec.Vec.is_empty, bind_ok] at h ⊢
    by_cases hc : st.ctrls.val = []
    · simp only [hc, List.isEmpty_nil, ↓reduceIte] at h ⊢
      by_cases hp : st.pos = Slice.len data
      · simp [hp] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hrelated⟩
      · simp [hp] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hrelated⟩
    · have hempty : st.ctrls.val.isEmpty = false := by simpa using hc
      simp only [hempty, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hp : st.pos.val < data.length
      · obtain ⟨next, hr, hnext⟩ := code.read_op_success st data hp
        rw [hr] at h ⊢
        simp [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_assoc] at h ⊢
        obtain ⟨⟨stepResult, out, v1⟩, hs, htail⟩ := ResultFacts.bind_ok_inv _ _ _ h
        obtain ⟨w1, hw, hr1⟩ := code.step.refines visitor replacement related hrefines
          {st with pos := next} data env ctx data.val[st.pos.val] v w hrelated
          stepResult out v1 hs
        rw [hw]
        cases stepResult with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at htail ⊢
          obtain ⟨rfl, rfl⟩ := htail
          exact ⟨rfl, hr1⟩
        | Ok u =>
          cases u
          have hdefault := code.step.accepted_erase visitor {st with pos := next} out
            data env ctx data.val[st.pos.val] v v1 hs
          have hprogress := hstep st () hi hc hp next hnext
          rw [hdefault, WP.spec_ok] at hprogress
          obtain ⟨hi', hge, hbound⟩ := hprogress rfl
          dsimp only at hi' hge hbound
          have hmeasure : data.length - out.pos.val < n := by omega
          simp only [bind_ok]
          simp at htail
          have htail' : code.validate_body_with_loop visitor data env ctx.locals ctx.results v1 out =
              .ok (res, v') := by
            simpa [code.validate_body_with_loop, code.validate_body_with_loop.body,
              code.control_stack_empty, alloc.vec.Vec.is_empty,
              core.result.Result.Insts.CoreOpsTry.branch] using htail
          obtain ⟨w2, hw2, hr2⟩ := ih (data.length - out.pos.val) hmeasure out v1 w1
            hi' hr1 htail' rfl
          refine ⟨w2, ?_, hr2⟩
          simpa [code.validate_body_with_loop, code.validate_body_with_loop.body,
            code.control_stack_empty, alloc.vec.Vec.is_empty,
            core.result.Result.Insts.CoreOpsTry.branch] using hw2
      · rw [code.read_op.eof st data (by omega)] at h ⊢
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hrelated⟩

/-- Hook refinement lifts through the size guard and initialization of
`code.validate_body_with`. -/
theorem code.validate_body_with.refines_of_contract {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (inv : code.OpIterState → Prop)
    (hstep : Wasm1.Loop.StepContract code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx (fun _ st => inv st))
    (hinit : data.length ≤ limits.MAX_FUNCTION_BYTES.val →
      inv (Wasm1.Loop.initial (Wasm1.Loop.initialBlockType ctx.results.val)))
    (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (v' : V)
    (h : code.validate_body_with visitor data env ctx v = .ok (res, v')) :
    ∃ w', code.validate_body_with replacement data env ctx w = .ok (res, w') ∧ related v' w' := by
  simp only [code.validate_body_with.eq_model] at h ⊢
  unfold code.validate_body_with_model at h ⊢
  dsimp only at h ⊢
  by_cases hsize : Slice.len data > limits.MAX_FUNCTION_BYTES
  · simp [hsize] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hrelated⟩
  · rw [if_neg hsize, code.start_function.raw_spec] at h ⊢
    simp only [bind_ok] at h ⊢
    apply code.validate_body_with_loop.refines_of_contract visitor replacement related hrefines
      data env ctx inv hstep _ v w _ hrelated res v' h
    simpa [alloc.vec.Vec.deref] using hinit (by scalar_tac)

/-- Any callback refinement preserves the returned outcome of `code.validate_body_with`. There
are no premises on the bytes, the environment or visitor termination. -/
theorem code.validate_body_with.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (v' : V)
    (h : code.validate_body_with visitor data env ctx v = .ok (res, v')) :
    ∃ w', code.validate_body_with replacement data env ctx w = .ok (res, w') ∧ related v' w' := by
  let bt := Wasm1.Loop.initialBlockType ctx.results.val
  have hsteps := Wasm1.steps code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
    FullVisitor.empty_total data env ctx bt
  exact code.validate_body_with.refines_of_contract visitor replacement related hrefines
    data env ctx (Wasm1.State data env ctx bt)
    (hsteps.contract code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor data env ctx bt)
    (fun hsize => Wasm1.State.start data env ctx bt hsize) v w hrelated res v' h

/-- Instrumenting an arbitrary visitor preserves every returned outcome and the underlying final
visitor state, and appends a suffix to the observation log. -/
theorem code.validate_body_with.instrument_forward {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) (log : List Observation)
    (res : core.result.Result Unit error.OpError) (v' : V)
    (h : code.validate_body_with visitor data env ctx v = .ok (res, v')) :
    ∃ added, code.validate_body_with (instrument visitor) data env ctx (v, log) =
      .ok (res, (v', log ++ added)) := by
  obtain ⟨⟨w, log'⟩, hw, heq, added, hlog⟩ := code.validate_body_with.refines visitor
    (instrument visitor) _ (instrument_refines visitor log) data env ctx v (v, log)
    ⟨rfl, [], by simp⟩ res v' h
  dsimp only at heq hlog
  subst w
  subst log'
  exact ⟨added, hw⟩

/-- Removing the `instrument` wrapper preserves both rejection and acceptance. The underlying
visitor need not terminate on other executions. -/
theorem code.validate_body_with.instrument_backward {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) (log : List Observation)
    (res : core.result.Result Unit error.OpError) (v' : V) (log' : List Observation)
    (h : code.validate_body_with (instrument visitor) data env ctx (v, log) =
      .ok (res, (v', log'))) :
    code.validate_body_with visitor data env ctx v = .ok (res, v') := by
  obtain ⟨w, hw, heq⟩ := code.validate_body_with.refines (instrument visitor) visitor
    _ (instrument_refines_back visitor) data env ctx (v, log) v rfl res (v', log') h
  simpa only [← heq] using hw

/-- An instrumented execution returns a result and underlying visitor state exactly when the
plain visitor does, with the appended observations as the witness. -/
theorem code.validate_body_with.instrument_iff {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) (log : List Observation)
    (res : core.result.Result Unit error.OpError) (v' : V) :
    code.validate_body_with visitor data env ctx v = .ok (res, v') ↔
      ∃ added, code.validate_body_with (instrument visitor) data env ctx (v, log) =
        .ok (res, (v', log ++ added)) := by
  constructor
  · exact code.validate_body_with.instrument_forward visitor data env ctx v log res v'
  · rintro ⟨added, h⟩
    exact code.validate_body_with.instrument_backward visitor data env ctx v log res v'
      (log ++ added) h

/-- Any returned instrumented execution extends its initial observation log. -/
theorem code.validate_body_with.instrument_log_extension {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) (log : List Observation)
    (res : core.result.Result Unit error.OpError) (v' : V) (log' : List Observation)
    (h : code.validate_body_with (instrument visitor) data env ctx (v, log) =
      .ok (res, (v', log'))) :
    ∃ added, log' = log ++ added := by
  have hb := code.validate_body_with.instrument_backward visitor data env ctx v log res v' log' h
  obtain ⟨added, hf⟩ := code.validate_body_with.instrument_forward visitor data env ctx v log res v' hb
  rw [h] at hf
  exact ⟨added, by simpa using hf⟩

end Itasca

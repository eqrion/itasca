import Itasca.Support.Result
import Itasca.Visitor.TraceBytes
import Itasca.Wasm1.Visitor.Erasure

/-!
# Body trace from a step contract

`StepContract` states the trace property for a single `code.step` return. The theorems
`code.validate_body_with_loop.trace_of_contract` and `code.validate_body_with.trace_of_contract`
lift it to the body loop and to `code.validate_body_with`, using the empty-visitor invariant for
progress.
-/

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

/-- Every returned `code.step` records callbacks with byte provenance and stops at a rejection. -/
def StepContract {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bt : code.BlockType) : Prop :=
  ∀ st (p : Wasm1.Pending data env ctx bt st) v result out v',
    code.step visitor st data env ctx (data.val[p.start.val]'p.inbounds) v = .ok (result, out, v') →
    ∃ observations, observe v' = observe v ++ observations ∧
      StepTrace data p.start observations result out

theorem BodyTrace.empty {data start result} (hb : start.val ≤ data.length)
    (hend : result = .Ok () → start.val = data.length) : BodyTrace data start [] result := by
  exact ⟨.empty result, [], [], start, [], rfl, .nil start hb, Or.inl rfl,
    fun h => ⟨rfl, hend h⟩⟩

theorem StepTrace.rejected {data start observations e st}
    (h : StepTrace data start observations (.Err e) st) (hb : start.val ≤ data.length) :
    BodyTrace data start observations (.Err e) := by
  refine ⟨h.outcomes, ?_⟩
  cases h with
  | silent => exact ⟨[], [], start, [], rfl, .nil start hb, Or.inl rfl, by simp⟩
  | complete hc _ =>
      exact ⟨observations, [_], st.pos, [], by simp,
        by simpa using Completed.cons hc (.nil _ hc.encoded.span.2), Or.inl rfl, by simp⟩
  | unfinished _ hp _ =>
      exact ⟨[], [], start, _, by simp, .nil start hb, Or.inr hp, by simp⟩

theorem BodyTrace.prepend {data start first token middle rest result}
    (hc : Chunk data start first token middle) (ho : AllAccepted first)
    (h : BodyTrace data middle rest result) : BodyTrace data start (first ++ rest) result := by
  obtain ⟨hout, complete, tokens, cursor, tail, rfl, hcomplete, htail, hend⟩ := h
  exact ⟨hout.prepend ho, first ++ complete, token :: tokens, cursor, tail,
    by simp [List.append_assoc], .cons hc hcomplete, htail, hend⟩

end Itasca.VisitorTrace

namespace Itasca

/-- A `StepContract` lifts through the extracted body loop. The empty-visitor invariant supplies
progress, so callbacks need not be total. -/
theorem code.validate_body_with_loop.trace_of_contract {V : Type}
    (visitor : code.OpVisitor V) (observe : V → List VisitorTrace.Observation)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (htrace : VisitorTrace.StepContract visitor observe data env ctx bt)
    (st : code.OpIterState) (v v' : V) (result : VisitorTrace.BodyResult)
    (hi : Wasm1.State data env ctx bt st)
    (h : code.validate_body_with_loop visitor data env ctx.locals ctx.results v st = .ok (result, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      VisitorTrace.BodyTrace data st.pos observations result := by
  generalize hn : data.length - st.pos.val = n
  induction n using Nat.strong_induction_on generalizing st v with
  | h n ih =>
    unfold code.validate_body_with_loop at h
    rw [loop] at h
    simp only [code.validate_body_with_loop.body, code.control_stack_empty,
      alloc.vec.Vec.is_empty, bind_ok] at h
    by_cases hc : st.ctrls.val = []
    · simp only [hc, List.isEmpty_nil, ↓reduceIte] at h
      by_cases hp : st.pos = Slice.len data
      · simp [hp] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], by simp, .empty hi.bounds.pos (by intro _; scalar_tac)⟩
      · simp [hp] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], by simp, .empty hi.bounds.pos (by simp)⟩
    · have hempty : st.ctrls.val.isEmpty = false := by simpa using hc
      simp only [hempty, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hp : st.pos.val < data.length
      · obtain ⟨next, hr, hnext⟩ := code.read_op_success st data hp
        rw [hr] at h
        simp [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_assoc] at h
        obtain ⟨⟨res, out, w⟩, hs, htail⟩ := ResultFacts.bind_ok_inv _ _ _ h
        obtain ⟨p, hstart⟩ := hi.pending hc hp next hnext
        have hs' : code.step visitor {st with pos := next} data env ctx
            (data.val[p.start.val]'p.inbounds) v = .ok (res, out, w) := by simpa [hstart] using hs
        obtain ⟨first, hfirst, hchunk⟩ := htrace _ p v res out w hs'
        rw [hstart] at hchunk
        cases res with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at htail
          obtain ⟨rfl, rfl⟩ := htail
          exact ⟨first, hfirst, hchunk.rejected hi.bounds.pos⟩
        | Ok u =>
          cases u
          have hdefault := code.step.accepted_erase visitor {st with pos := next} out
            data env ctx data.val[st.pos.val] v w hs
          have hprogress := (Wasm1.steps code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
            FullVisitor.empty_total data env ctx bt).contract
            code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor data env ctx bt st () hi hc hp next hnext
          rw [hdefault, WP.spec_ok] at hprogress
          obtain ⟨hi', hge, hbound⟩ := hprogress rfl
          dsimp only at hi' hge hbound
          have hmeasure : data.length - out.pos.val < n := by omega
          simp at htail
          have htail' : code.validate_body_with_loop visitor data env ctx.locals ctx.results w out =
              .ok (result, v') := by
            simpa [code.validate_body_with_loop, code.validate_body_with_loop.body,
              code.control_stack_empty, alloc.vec.Vec.is_empty,
              core.result.Result.Insts.CoreOpsTry.branch] using htail
          obtain ⟨rest, hrest, hbody⟩ := ih (data.length - out.pos.val) hmeasure out w hi' htail' rfl
          obtain ⟨token, hencoded⟩ := hchunk.accepted
          exact ⟨first ++ rest, by simp [hrest, hfirst, List.append_assoc],
            hbody.prepend hencoded hchunk.outcomes⟩
      · rw [code.read_op.eof st data (by omega)] at h
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], by simp, .empty hi.bounds.pos (by simp)⟩

/-- A `StepContract` lifts through `code.validate_body_with`. Initialization makes no body
callback, including when it fails the size limit. -/
theorem code.validate_body_with.trace_of_contract {V : Type}
    (visitor : code.OpVisitor V) (observe : V → List VisitorTrace.Observation)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (htrace : VisitorTrace.StepContract visitor observe data env ctx
      (Wasm1.Loop.initialBlockType ctx.results.val))
    (v v' : V) (result : VisitorTrace.BodyResult)
    (h : code.validate_body_with visitor data env ctx v = .ok (result, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      VisitorTrace.BodyTrace data 0#usize observations result := by
  simp only [code.validate_body_with.eq_model] at h
  unfold code.validate_body_with_model at h
  dsimp only at h
  by_cases hsize : Slice.len data > limits.MAX_FUNCTION_BYTES
  · simp [hsize] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, .empty (by simp) (by simp)⟩
  · rw [if_neg hsize, code.start_function.raw_spec] at h
    simp only [bind_ok] at h
    exact code.validate_body_with_loop.trace_of_contract visitor observe data env ctx _ htrace
      _ v v' result (Wasm1.State.start data env ctx _ (by scalar_tac))
      (by simpa [alloc.vec.Vec.deref] using h)

end Itasca

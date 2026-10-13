import Itasca.MultiValue.CallbackTrace
import Itasca.MultiValue.VisitorBody
import Itasca.Visitor.VisitorBodyTraceGeneric

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.CallbackTrace

open VisitorTrace

/-- Byte provenance and stopping for every ordinary Core 2.0 step. -/
def StepContract {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (data : Slice U8) (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (ctx : code.Context) (index : U32) : Prop :=
  ∀ st (p : Pending data env locals index st) v result out v',
    code.step_profile visitor st data env ctx index .Wasm2
      (data.val[p.start.val]'p.inbounds) v = .ok (result, out, v') →
    ∃ observations, observe v' = observe v ++ observations ∧
      StepTrace data p.start observations result out.core

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

end Itasca.MultiValue.CallbackTrace

namespace Itasca

open MultiValue

/-- Lift returned-step Core 2.0 byte provenance through the actual body loop.
The existing accepting-visitor invariant supplies strict cursor progress. -/
theorem code.validate_multi_value_body_with_loop.trace_of_contract {V : Type}
    (visitor : code.OpVisitor V) (observe : V → List VisitorTrace.Observation)
    (data : Slice U8) (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (ctx : code.Context) (index : U32) (hlocals : ctx.locals = locals)
    (htrace : CallbackTrace.StepContract visitor observe data env locals ctx index)
    (st : code.BodyState) (v v' : V) (result : VisitorTrace.BodyResult)
    (hi : State data env locals index st)
    (h : code.validate_multi_value_body_with_loop visitor data env.types env.imports env.globals
      env.exports env.elements env.data_count env.declared_funcs env.start env.func_type_indices
      env.func_types env.table_types env.mem_types env.global_types env.num_imported_funcs
      env.num_imported_globals ctx index v st = .ok (result, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.BodyTrace data st.core.pos observations result := by
  generalize hn : data.length - st.core.pos.val = n
  induction n using Nat.strong_induction_on generalizing st v with
  | h n ih =>
    unfold code.validate_multi_value_body_with_loop code.body_loop_loop at h
    rw [loop] at h
    simp only [Std.uncurry] at h
    obtain ⟨cf, hb, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
    have hb0 := hb
    unfold code.body_loop_loop.body at hb
    simp only [alloc.vec.Vec.is_empty, bind_ok] at hb
    by_cases hc : st.blocks.val = []
    · have he : st.core.ctrls.val = [] := by simpa using hc
      simp only [he, List.isEmpty_nil, ↓reduceIte] at hb
      by_cases hp : st.core.pos = Slice.len data
      · simp [hp] at hb
        subst cf
        simp at ht
        obtain ⟨rfl, rfl⟩ := ht
        exact ⟨[], by simp, .empty hi.bounds.pos (by intro _; scalar_tac)⟩
      · simp [hp] at hb
        subst cf
        simp at ht
        obtain ⟨rfl, rfl⟩ := ht
        exact ⟨[], by simp, .empty hi.bounds.pos (by simp)⟩
    · have he : st.core.ctrls.val.isEmpty = false := by simpa using hc
      simp only [he, Bool.false_eq_true, ↓reduceIte] at hb
      by_cases hp : st.core.pos.val < data.length
      · obtain ⟨r, hr, next, heq, hnext⟩ :=
          WP.spec_imp_exists (reader.read_byte.spec data st.core.pos hp)
        rw [heq] at hr
        rw [hr] at hb
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at hb
        obtain ⟨⟨res, out, w⟩, hs, htail⟩ := ResultFacts.bind_ok_inv _ _ _ hb
        obtain ⟨p, hstart⟩ := hi.pending hc hp next hnext
        have hs' : code.step_profile visitor {core := {st.core with pos := next}}
            data env ctx index .Wasm2 (data.val[p.start.val]'p.inbounds) v =
            .ok (res, out, w) := by simpa [hstart] using hs
        obtain ⟨first, hfirst, hchunk⟩ := htrace _ p v res out w hs'
        rw [hstart] at hchunk
        cases res with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at htail
          subst cf
          simp at ht
          obtain ⟨rfl, rfl⟩ := ht
          exact ⟨first, hfirst, hchunk.rejected hi.bounds.pos⟩
        | Ok u =>
          cases u
          simp [core.result.Result.Insts.CoreOpsTry.branch] at htail
          subst cf
          obtain ⟨emptyCf, hempty, hobs⟩ := Visitor.body.transfer visitor
            code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts
            data env ctx ctx rfl index st v () _ hb0 trivial
          obtain ⟨⟨res, s⟩, hs0, hafter⟩ :=
            WP.spec_imp_exists (steps data env locals ctx index hlocals _ p)
          simp only [hstart] at hs0
          have heval : Visitor.body code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
              data env ctx index () st =
              .ok (match continueStep (res, s) with
                | .cont (s, _) => .cont ((), s)
                | .done r => .done (r, ())) := by
            change code.body_loop_loop.body _ _ _ _ _ _ _ _ = _
            rw [code.validate_multi_value_body_loop.body_eq]
            change (loopBody data env ctx index st >>= fun r => .ok
              (match r with | .cont (s, _) => .cont ((), s) | .done r => .done (r, ())
                : ControlFlow (Unit × code.BodyState) (core.result.Result Unit error.OpError × Unit))) = _
            rw [loopBody_eq, if_neg hc, hr]
            simp only [bind_ok, hs0]
            cases res <;> simp [continueStep, Std.bind_assoc]
          rw [hempty] at heval
          simp only [Result.ok.injEq] at heval
          subst emptyCf
          cases res with
          | Err e => simp [continueStep, Visitor.bodyObserve] at hobs
          | Ok u =>
            cases u
            simp only [continueStep, Visitor.bodyObserve, ControlFlow.cont.injEq] at hobs
            subst s
            obtain ⟨hi', hge, hbound⟩ := hafter rfl
            change next.val ≤ out.core.pos.val at hge
            have hmeasure : data.length - out.core.pos.val < n := by omega
            have ht' : code.validate_multi_value_body_with_loop visitor data env.types env.imports
                env.globals env.exports env.elements env.data_count env.declared_funcs env.start
                env.func_type_indices env.func_types env.table_types env.mem_types env.global_types
                env.num_imported_funcs env.num_imported_globals ctx index w out = .ok (result, v') := by
              simpa [code.validate_multi_value_body_with_loop, code.body_loop_loop] using ht
            obtain ⟨rest, hrest, hbody⟩ := ih (data.length - out.core.pos.val)
              hmeasure out w hi' ht' rfl
            obtain ⟨token, hencoded⟩ := hchunk.accepted
            exact ⟨first ++ rest, by simp [hrest, hfirst, List.append_assoc],
              hbody.prepend hencoded hchunk.outcomes⟩
      · rw [reader.read_byte.eof data st.core.pos (by omega)] at hb
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hb
        subst cf
        simp at ht
        obtain ⟨rfl, rfl⟩ := ht
        exact ⟨[], by simp, .empty hi.bounds.pos (by simp)⟩

/-- Successful Core 2.0 initialization selects the actual type entry and the
same root frame used by the independent syntax invariant. -/
theorem code.initial_state.multi_value_start (env : module.Env) (ctx : code.Context)
    (index : U32) :
    code.initial_state env ctx index .Wasm2 ⦃ r => match r with
      | .Err _ => True
      | .Ok st => st = initial index ∧ ∃ ft, env.types.val[index.val]? = some ft ⦄ := by
  unfold code.initial_state
  step as ⟨idx, hidx⟩
  split
  · simp
  · rename_i hbound
    step as ⟨ft, hft⟩
    have hi : env.types.val[index.val]? = some ft := by
      rw [List.getElem?_eq_getElem (by scalar_tac)]
      simp_all
    step as ⟨r, hr⟩
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok u =>
      cases u
      simp [core.result.Result.Insts.CoreOpsTry.branch, code.push_frame.initial]
      exact ⟨ft, hi⟩

/-- Initialization emits no Core 2.0 callback. Step provenance therefore gives
an exact whole-body trace for every ordinary public outcome, including errors. -/
theorem code.validate_multi_value_body_with.trace_of_contract {V : Type}
    (visitor : code.OpVisitor V) (observe : V → List VisitorTrace.Observation)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (htrace : CallbackTrace.StepContract visitor observe data env ctx.locals ctx index)
    (v v' : V) (result : VisitorTrace.BodyResult)
    (h : code.validate_multi_value_body_with visitor data env ctx index v = .ok (result, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.BodyTrace data 0#usize observations result := by
  unfold code.validate_multi_value_body_with code.validate_body_with_profile at h
  by_cases hsize : Slice.len data > limits.MAX_FUNCTION_BYTES
  · simp [hsize] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, .empty (by simp) (by simp)⟩
  · simp only [hsize, if_false] at h
    obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], by simp, .empty (by simp) (by simp)⟩
    | Ok st =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, code.body_loop] at h
      have hp := code.initial_state.multi_value_start env ctx index
      rw [hr, WP.spec_ok] at hp
      obtain ⟨rfl, ft, hi⟩ := hp
      exact code.validate_multi_value_body_with_loop.trace_of_contract visitor observe
        data env ctx.locals ctx index rfl htrace (initial index) v v' result
        (State.start data env ctx.locals index ft hi (by scalar_tac)) h

end Itasca

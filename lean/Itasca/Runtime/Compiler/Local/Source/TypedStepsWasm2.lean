import Itasca.Runtime.Equations
import Itasca.Wasm2.Trace.Correspondence
import Itasca.Profile.EntrySound
import Itasca.Stream.Batch
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
open Itasca Itasca.Wasm2

/-- Actual Wasm 2.0 instruction steps paired with typed source zippers,
including indexed block signatures and the declared-reference condition. -/
inductive TypedRunWasm2 {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32) :
    code.BodyState → V → V → Prop where
  | done {st v} (typed : State data env .Wasm2 ctx.locals index st)
      (closed : st.blocks.val = []) (finished : st.core.pos = Slice.len data) :
      TypedRunWasm2 visitor data env ctx index st v v
  | step {st v next out middle final}
      (typed : State data env .Wasm2 ctx.locals index st)
      (pending : Pending data env .Wasm2 ctx.locals index {core := {st.core with pos := next}})
      (start : pending.start = st.core.pos)
      (advance : next.val = st.core.pos.val + 1)
      (called : code.step_profile visitor {core := {st.core with pos := next}} data env ctx index .Wasm2
        (data.val[pending.start.val]'pending.inbounds) v = .ok (.Ok (), out, middle))
      (rest : TypedRunWasm2 visitor data env ctx index out middle final) :
      TypedRunWasm2 visitor data env ctx index st v final

theorem typed_loop_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (st : code.BodyState) (v v' : V) (hi : State data env .Wasm2 ctx.locals index st)
    (h : code.body_loop_loop visitor data env ctx index .Wasm2 v st = .ok (.Ok (), v')) :
    TypedRunWasm2 visitor data env ctx index st v v' := by
  generalize hn : data.length - st.core.pos.val = n
  induction n using Nat.strong_induction_on generalizing st v with
  | h n ih =>
    unfold code.body_loop_loop at h
    rw [loop] at h
    simp only at h
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
        subst v
        exact .done hi hc hp
      · simp [hp] at hb
        subst cf
        simp at ht

    · have he : st.core.ctrls.val.isEmpty = false := by simpa using hc
      simp only [he, Bool.false_eq_true, ↓reduceIte] at hb
      by_cases hp : st.core.pos.val < data.length
      · obtain ⟨r, hr, next, heq, hnext⟩ :=
          WP.spec_imp_exists (reader.read_byte.spec data st.core.pos hp)
        rw [heq] at hr
        rw [hr] at hb
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at hb
        obtain ⟨⟨res, out, w⟩, hs, htail⟩ := ResultFacts.bind_ok_inv _ _ _ hb
        obtain ⟨p, hstart⟩ := hi.pending hc hp (fun h => nomatch h) next hnext
        have hs' : code.step_profile visitor {core := {st.core with pos := next}}
            data env ctx index .Wasm2 (data.val[p.start.val]'p.inbounds) v =
            .ok (res, out, w) := by simpa [hstart] using hs
        cases res with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at htail
          subst cf
          simp at ht

        | Ok acceptedUnit =>
          cases acceptedUnit
          simp at htail
          subst cf
          obtain ⟨emptyCf, hempty, hobs⟩ := Visitor.body.transfer visitor
            code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts
            data env ctx ctx rfl index .Wasm2 st v () _ hb0 trivial
          obtain ⟨⟨res, s⟩, hs0, hafter⟩ :=
            WP.spec_imp_exists (steps data env .Wasm2 ctx.locals ctx index rfl _ p)
          simp only [hstart] at hs0
          have heval : Visitor.body code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
              data env ctx index .Wasm2 () st =
              .ok (match continueStep (res, s) with
                | .cont (s, _) => .cont ((), s)
                | .done r => .done (r, ())) := by
            change code.body_loop_loop.body _ _ _ _ _ _ _ _ = _
            rw [Wasm2.emptyVisitorLoop.body_eq]
            change (loopBody data env .Wasm2 ctx index st >>= fun r => .ok
              (match r with | .cont (s, _) => .cont ((), s) | .done r => .done (r, ())
                : ControlFlow (Unit × code.BodyState) (core.result.Result Unit error.OpError × Unit))) = _
            rw [loopBody_eq, if_neg hc, hr]
            simp only [bind_ok, code.check_opcode, hs0]
            cases res <;> simp [continueStep]
          rw [hempty] at heval
          simp only [Result.ok.injEq] at heval
          subst emptyCf
          cases res with
          | Err e => simp [continueStep, Visitor.bodyObserve] at hobs
          | Ok acceptedUnit =>
            cases acceptedUnit
            simp only [continueStep, Visitor.bodyObserve, ControlFlow.cont.injEq] at hobs
            subst s
            obtain ⟨hi', hge, hbound⟩ := hafter rfl
            change next.val ≤ out.core.pos.val at hge
            have hmeasure : data.length - out.core.pos.val < n := by omega
            have ht' : code.body_loop_loop visitor data env ctx index .Wasm2 w out = .ok (.Ok (), v') := by
              simpa [code.body_loop_loop] using ht
            exact .step hi p hstart hnext hs'
              (ih (data.length - out.core.pos.val) hmeasure out w hi' ht' rfl)
      · rw [reader.read_byte.eof data st.core.pos (by omega)] at hb
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hb
        subst cf
        simp at ht

/-- A real successful body validation starts the typed instruction trace at
its actual root frame; no compiler-correctness premise is assumed. -/
theorem typed_body_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (before after : V)
    (accepted : code.validate_body_with visitor data env ctx index .Wasm2 before =
      .ok (.Ok (), after)) :
    TypedRunWasm2 visitor data env ctx index (initial index) before after := by
  unfold code.validate_body_with at accepted
  by_cases size : Slice.len data > limits.MAX_FUNCTION_BYTES
  · simp [size] at accepted
  · simp only [size, if_false] at accepted
    obtain ⟨result, initialized, tail⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
    cases result with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
    | Ok st =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, code.body_loop] at tail
      have start := code.initial_state.start env index
      rw [initialized, WP.spec_ok] at start
      obtain ⟨rfl, ft, lookup⟩ := start
      exact typed_loop_wasm2 visitor data env ctx index _ before after
        (State.start data env .Wasm2 ctx.locals index ft lookup (by scalar_tac)) tail
end Itasca.Runtime.Compiler

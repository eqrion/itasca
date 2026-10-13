import Itasca.Wasm2.Totality
import Itasca.Wasm2.Execution

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

def Steps (data : Slice U8) (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (ctx : code.Context) (index : U32) : Prop :=
  ∀ st (p : Pending data env locals index st),
    step st data env ctx index (data.val[p.start.val]'p.inbounds) ⦃ r =>
      r.1 = .Ok () → p.After r.2 ⦄

/-- Each successful iteration extends the independent syntax and typing
invariant. Its strictly increasing cursor justifies the whole-body induction. -/
theorem run.sound (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (ctx : code.Context) (index : U32)
    (hsteps : Steps data env locals ctx index) (st : code.BodyState)
    (hi : State data env locals index st)
    (haccepted : run data env ctx index st = .ok (.Ok ())) :
    Validated data env locals index := by
  generalize he : Usize.max - st.core.pos.val = fuel
  induction fuel using Nat.strong_induction_on generalizing st with
  | h fuel ih =>
    rw [run_unfold, loopBody_eq] at haccepted
    by_cases hc : st.blocks.val = []
    · simp only [hc, if_true, bind_ok] at haccepted
      split at haccepted
      · rename_i hp
        exact hi.finished hc (by simpa using congrArg UScalar.val hp)
      · simp at haccepted
    · simp only [hc, if_false] at haccepted
      by_cases hp : st.core.pos.val < data.length
      · obtain ⟨r, hr, next, heq, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.core.pos hp)
        rw [heq] at hr
        obtain ⟨p, hstart⟩ := hi.pending hc hp next hn
        obtain ⟨⟨result, s⟩, hs, hout⟩ := WP.spec_imp_exists (hsteps _ p)
        simp only [hstart] at hs
        rw [hr] at haccepted
        simp only [bind_ok, hs] at haccepted
        cases result with
        | Err e => simp [continueStep] at haccepted
        | Ok v =>
          cases v
          simp only [continueStep] at haccepted
          obtain ⟨hinv, hprogress, _⟩ := hout rfl
          apply ih (Usize.max - s.core.pos.val) _ s hinv haccepted rfl
          have hmax : s.core.pos.val ≤ Usize.max := by scalar_tac
          have hn' : st.core.pos.val < s.core.pos.val := by
            change next.val ≤ s.core.pos.val at hprogress
            omega
          omega
      · rw [reader.read_byte.eof data st.core.pos (by omega)] at haccepted
        simp at haccepted

theorem run.spec (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (ctx : code.Context) (index : U32)
    (hsteps : Steps data env locals ctx index) (st : code.BodyState)
    (hi : State data env locals index st) :
    run data env ctx index st ⦃ r => r = .Ok () → Validated data env locals index ⦄ := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (code.validate_multi_value_body_loop.total data env ctx.locals ctx.results index st ()
      hi.bounds.size hi.shape.core hi.shape.aligned hi.bounds.ctrls)
  change run data env ctx index st = .ok r at hr
  rw [hr]
  simp only [WP.spec_ok]
  intro hok
  exact run.sound data env locals ctx index hsteps st hi (by simpa [hok] using hr)

theorem public_spec_of_steps (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32)
    (hsteps : Steps data env locals ⟨locals, alloc.vec.Vec.new _⟩ index) :
    code.validate_multi_value_body data env locals index ⦃ r =>
      r = .Ok () → Validated data env locals index ⦄ := by
  rw [code.validate_multi_value_body.eq_core]
  unfold code.bodyCore
  dsimp only
  split
  · simp
  · rename_i hsize
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
      | Ok v =>
        cases v
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          code.push_frame.initial]
        exact run.spec data env locals ⟨locals, alloc.vec.Vec.new _⟩ index hsteps
          (initial index) (State.start data env locals index ft hi (by scalar_tac))

end Itasca.MultiValue

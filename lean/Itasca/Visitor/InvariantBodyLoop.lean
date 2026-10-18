import Itasca.Binary.ReadByte

namespace Itasca
open Aeneas Aeneas.Std

namespace ReachedBody
/-- Only the reader/visitor pairs actually retained by the prefix invariant
must return. Bytes may be malformed, and a callback may reject normally. -/
def StepTotalOn {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (typeIndex : U32) (profile : ValidationProfile)
    (inv : V → code.BodyState → Prop) : Prop :=
  ∀ (st : code.BodyState) (v : V), inv v st → st.core.ctrls.val ≠ [] →
    ∀ (inbounds : st.core.pos.val < data.length) (next : Usize), next.val = st.core.pos.val + 1 →
      code.step_profile visitor {core := {st.core with pos := next}} data env ctx typeIndex profile
        data.val[st.core.pos.val] v ⦃ out => out.1 = .Ok () →
          inv out.2.2 out.2.1 ∧ next.val ≤ out.2.1.core.pos.val ⦄
end ReachedBody

/-- The actual common body loop returns from normal reader steps at reached
states. Its termination measure uses the concrete byte cursor, independently of
source validity or callback behavior at unreachable states. -/
theorem code.body_loop_loop.total_on {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (typeIndex : U32)
    (profile : ValidationProfile) (inv : V → code.BodyState → Prop) (post : V → Prop)
    (steps : ReachedBody.StepTotalOn visitor data env ctx typeIndex profile inv)
    (closed : ∀ st v, inv v st → st.core.ctrls.val = [] → st.core.pos.val = data.length → post v)
    (v : V) (st : code.BodyState) (initial : inv v st) :
    code.body_loop_loop visitor data env ctx typeIndex profile v st ⦃ out =>
      out.1 = .Ok () → post out.2 ⦄ := by
  unfold code.body_loop_loop
  apply loop.spec_decr_nat (fun state => Usize.max - state.2.core.pos.val)
    (fun state => inv state.1 state.2)
  · rintro ⟨v,st⟩ held
    unfold code.body_loop_loop.body
    simp only [alloc.vec.Vec.is_empty,bind_ok]
    by_cases empty : st.core.ctrls.val = []
    · simp only [empty,List.isEmpty_nil,↓reduceIte]
      split
      · simp
      · rename_i atEnd
        simp only [WP.spec_ok]
        intro _
        apply closed st v held empty
        simpa using atEnd
    · have nonempty : st.core.ctrls.val.isEmpty = false := by simpa using empty
      simp only [nonempty,Bool.false_eq_true,↓reduceIte]
      by_cases inbounds : st.core.pos.val < data.length
      · obtain ⟨result,read,next,resultEq,advance⟩ := WP.spec_imp_exists
          (reader.read_byte.spec data st.core.pos inbounds)
        rw [resultEq] at read
        rw [read]
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry]
        obtain ⟨⟨status,after,visitorAfter⟩,run,retained⟩ := WP.spec_imp_exists
          (steps st v held empty inbounds next advance)
        rw [run]
        cases status with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok acceptedUnit =>
          cases acceptedUnit
          obtain ⟨fresh,forward⟩ := retained rfl
          simp only [Std.uncurry,bind_ok,WP.spec_ok]
          refine ⟨fresh, ?_⟩
          dsimp only at forward
          have bound : after.core.pos.val ≤ Usize.max := by scalar_tac
          omega
      · rw [reader.read_byte.eof data st.core.pos (by omega)]
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · exact initial

/-- The outer size guard and initialization preserve the reached-state loop
contract. Initialization errors and oversized bodies return without callbacks. -/
theorem code.validate_body_with_profile.total_on {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (typeIndex : U32)
    (profile : ValidationProfile) (inv : V → code.BodyState → Prop) (post : V → Prop)
    (v : V)
    (initialization : code.initial_state env ctx typeIndex profile ⦃ result =>
      ∀ st, result = .Ok st → inv v st ⦄)
    (steps : ReachedBody.StepTotalOn visitor data env ctx typeIndex profile inv)
    (closed : ∀ st v, inv v st → st.core.ctrls.val = [] → st.core.pos.val = data.length → post v) :
    code.validate_body_with_profile visitor data env ctx typeIndex profile v ⦃ out =>
      out.1 = .Ok () → post out.2 ⦄ := by
  unfold code.validate_body_with_profile
  dsimp only
  split
  · simp
  · obtain ⟨result,started,held⟩ := WP.spec_imp_exists initialization
    rw [started]
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok st =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,code.body_loop]
      exact code.body_loop_loop.total_on visitor data env ctx typeIndex profile inv post
        steps closed v st (held st rfl)
end Itasca

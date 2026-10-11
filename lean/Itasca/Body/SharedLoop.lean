import Itasca.Body.LegacyExecution
import Itasca.Support.LoopMap

open Aeneas Aeneas.Std

namespace Itasca

/-- The shared worker specializes to the former Wasm 1.0 iteration, with only
its state record wrapped. Hook order and the complete returned state coincide. -/
theorem multi_value.body_loop_loop.body_wasm1 {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) (st : code.OpIterState) :
    multi_value.body_loop_loop.body visitor data env ctx index .Wasm1 v ⟨st⟩ = (do
      let cf ← code.validate_body_with_loop.body visitor data env ctx.locals ctx.results v st
      pure (match cf with
        | .cont pair => .cont (pair.1, (⟨pair.2⟩ : multi_value.State))
        | .done out => .done out)) := by
  unfold multi_value.body_loop_loop.body code.validate_body_with_loop.body
  simp only [Std.uncurry, code.control_stack_empty, alloc.vec.Vec.is_empty, Aeneas.Std.bind_ok]
  split
  · by_cases hp : st.pos = Slice.len data <;> simp [hp, Pure.pure]
  · simp only [Std.uncurry, code.read_op, multi_value.step_profile, Aeneas.Std.bind_assoc,
      Aeneas.Std.bind_ok, Pure.pure]
    congr 1
    funext r
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      rcases pair with ⟨op, pos⟩
      simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.bind_ok]
      simp only [Std.uncurry, Aeneas.Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
        Aeneas.Std.bind_assoc]
      congr 1
      funext out
      rcases out with ⟨res, next, w⟩
      cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Exact refinement of the actual shared loop by the proof-only former loop. -/
theorem multi_value.body_loop_loop.wasm1_eq {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) (st : code.OpIterState) :
    multi_value.body_loop_loop visitor data env ctx index .Wasm1 v ⟨st⟩ =
      code.validate_body_with_loop visitor data env ctx.locals ctx.results v st := by
  unfold multi_value.body_loop_loop code.validate_body_with_loop
  symm
  apply LoopMap.conjugate
    (f := fun (s : V × code.OpIterState) => (s.1, (⟨s.2⟩ : multi_value.State)))
  rintro ⟨w, s⟩
  simp only [Std.uncurry]
  rw [multi_value.body_loop_loop.body_wasm1]
  congr 1
  funext cf
  cases cf <;> rfl

/-- This equation preserves the historical raw-body API, including arbitrary
caller-supplied result vectors and every visitor callback. -/
theorem code.validate_body_with.eq_model {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (v : V) :
    code.validate_body_with visitor data env ctx v =
      code.validate_body_with_model visitor data env ctx v := by
  unfold code.validate_body_with multi_value.validate_body_with_profile
    code.validate_body_with_model
  dsimp only
  split
  · rfl
  · simp only [Std.uncurry, multi_value.initial_state, Aeneas.Std.bind_assoc, Aeneas.Std.bind_ok,
      core.result.Result.Insts.CoreOpsTry.branch, multi_value.body_loop]
    congr 1
    funext st
    exact multi_value.body_loop_loop.wasm1_eq visitor data env ctx 0#u32 v st

end Itasca

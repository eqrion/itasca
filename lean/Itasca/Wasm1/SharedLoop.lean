import Itasca.Wasm1.LegacyExecution
import Itasca.Support.LoopMap

/-!
# Refinement of the shared body loop

Proves that the extracted shared loop `code.body_loop_loop` at `.Wasm1` equals the proof-only
loop of `Wasm1/LegacyExecution` up to wrapping the state in `code.BodyState`
(`code.body_loop_loop.wasm1_eq`). Hence `code.validate_body_with` equals
`code.validate_body_with_model` (`code.validate_body_with.eq_model`).
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- One iteration of `code.body_loop_loop` at `.Wasm1` equals one iteration of the proof-only
loop, with the state record wrapped. Hook order and the returned state coincide. -/
theorem code.body_loop_loop.body_wasm1 {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) (st : code.OpIterState) :
    code.body_loop_loop.body visitor data env ctx index .Wasm1 v ⟨st⟩ = (do
      let cf ← code.validate_body_with_loop.body visitor data env ctx.locals ctx.results v st
      pure (match cf with
        | .cont pair => .cont (pair.1, (⟨pair.2⟩ : code.BodyState))
        | .done out => .done out)) := by
  unfold code.body_loop_loop.body code.validate_body_with_loop.body
  simp only [Std.uncurry, code.control_stack_empty, alloc.vec.Vec.is_empty, Aeneas.Std.bind_ok]
  split
  · by_cases hp : st.pos = Slice.len data <;> simp [hp, Pure.pure]
  · simp only [Std.uncurry, code.read_op, code.step_profile, Aeneas.Std.bind_assoc,
      Aeneas.Std.bind_ok, Pure.pure]
    congr 1
    funext r
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      rcases pair with ⟨op, pos⟩
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.bind_ok]
      simp only [Std.uncurry, Aeneas.Std.bind_assoc]
      congr 1
      funext out
      rcases out with ⟨res, next, w⟩
      cases res <;> simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- The extracted shared loop at `.Wasm1` equals the proof-only loop. -/
theorem code.body_loop_loop.wasm1_eq {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) (st : code.OpIterState) :
    code.body_loop_loop visitor data env ctx index .Wasm1 v ⟨st⟩ =
      code.validate_body_with_loop visitor data env ctx.locals ctx.results v st := by
  unfold code.body_loop_loop code.validate_body_with_loop
  symm
  apply LoopMap.conjugate
    (f := fun (s : V × code.OpIterState) => (s.1, (⟨s.2⟩ : code.BodyState)))
  rintro ⟨w, s⟩
  simp only
  rw [code.body_loop_loop.body_wasm1]
  congr 1
  funext cf
  cases cf <;> rfl

/-- The extracted `code.validate_body_with` equals the proof-only model for every visitor,
including arbitrary result vectors in the context. -/
theorem code.validate_body_with.eq_model {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (v : V) :
    code.validate_body_with visitor data env ctx v =
      code.validate_body_with_model visitor data env ctx v := by
  unfold code.validate_body_with code.validate_body_with_profile
    code.validate_body_with_model
  dsimp only
  split
  · rfl
  · simp only [code.initial_state, Aeneas.Std.bind_assoc, Aeneas.Std.bind_ok,
      core.result.Result.Insts.CoreOpsTry.branch, code.body_loop]
    congr 1
    funext st
    exact code.body_loop_loop.wasm1_eq visitor data env ctx 0#u32 v st

end Itasca

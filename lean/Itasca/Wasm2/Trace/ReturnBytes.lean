import Itasca.Wasm2.Trace.ControlRecords
import Itasca.Wasm2.Control.Return

open Aeneas Aeneas.Std
namespace Itasca.MultiValue.CallbackTrace
open VisitorTrace

/-- Factor the actual return callback after result checking and stack erasure. -/
theorem dispatch_return {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_profile visitor st data env ctx index .Wasm2 0x0f#u8 v =
      bodyRun (returnStep st env index) visitor (fun _ => .return_) v := by
  simp [code.step_profile, global_simps, bodyRun, returnStep, Std.bind_assoc, Std.uncurry,
    core.result.Result.Insts.CoreOpsTry.branch, code.visit,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok u =>
    cases u
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.bind_assoc, Std.uncurry]
    congr 1
    funext state
    simp only [bind_ok, Std.uncurry, invoke]
    congr 1
    funext pair
    obtain ⟨reply, w⟩ := pair
    cases reply <;> simp [hookResult, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Return reads no immediate bytes; checking results and erasing the active
stack segment preserve its post-opcode cursor. -/
theorem return_position (st : code.BodyState) (env : module.Env) (index : U32)
    (shape : Control.Shape st.core) :
    returnStep st env index ⦃ r => r.2.core.pos = st.core.pos ⦄ := by
  obtain ⟨⟨res, popped⟩, hp, hs, _, hpos, _⟩ := WP.spec_imp_exists
    (code.pop_results.total st.core env (.Type index .Results) shape)
  dsimp only at hs hpos
  cases res with
  | Err e => simpa [returnStep, hp] using hpos
  | Ok u =>
    cases u
    obtain ⟨marked, hm, _, _, hmark, _⟩ := WP.spec_imp_exists
      (code.mark_unreachable_total popped hs)
    simpa [returnStep, hp, hm] using hmark.trans hpos

theorem step_return {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0f#u8) :
    ProfileStepRecords p visitor observe ctx 0x0f#u8 := by
  intro v result final v' run
  rw [dispatch_return] at run
  apply bodyRun.trace data p.start _ visitor observe records (fun _ => .return_) ?_ v result final v' run
  intro state unit hr
  have spec := return_position st env index p.opened.shape.core
  rw [hr, WP.spec_ok] at spec
  dsimp only at spec
  refine ⟨.plain .RETURN, rfl, by simp [Action.opcode], ?_⟩
  exact At.plain (.no_immediate p.inbounds byte (by simpa [spec] using p.pos) .return_)

end Itasca.MultiValue.CallbackTrace

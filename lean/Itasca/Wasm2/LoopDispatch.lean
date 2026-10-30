import Itasca.Wasm2.Invariant
import Itasca.Wasm2.EmptyVisitorLoop

/-!
# Opcode dispatch in the body loop

Proof-side view of one iteration of the extracted body loop with the empty visitor. `step` is
the dispatch on one opcode, `loopBody` the whole iteration, and `loopBody_eq` unfolds the
iteration into the end-of-body check, `reader.read_byte` and `step`.
-/

open Aeneas Aeneas.Std Result

namespace Itasca.Wasm2

/-- The return arm of the extracted loop, with its state exposed for proofs. -/
def returnStep (st : code.BodyState) (env : metadata.Env) (index : U32) :
    Result (core.result.Result Unit error.OpError × code.BodyState) := do
  let (r, ois) ← code.pop_results st.core env (.Type index .Results)
  match r with
  | .Err e => .ok (.Err e, { st with core := ois })
  | .Ok () =>
    let ois ← code.mark_unreachable ois
    .ok (.Ok (), { st with core := ois })

/-- Proof adapter for one opcode of the extracted body loop after the profile's opcode filter. Its
exact factorization is checked by `loopBody_eq`; it is not a separate validity judgment. -/
def step (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (ctx : code.Context) (index : U32) (opcode : U8) :
    Result (core.result.Result Unit error.OpError × code.BodyState) :=
  match opcode with
  | 2#uscalar => code.enter st data env profile .Block
  | 3#uscalar => code.enter st data env profile .Loop
  | 4#uscalar => code.enter st data env profile .Then
  | 5#uscalar => code.end_frame st env true
  | 11#uscalar => code.end_frame st env false
  | 12#uscalar => code.branch st data env false
  | 13#uscalar => code.branch st data env true
  | 14#uscalar => code.branch_table st data env profile
  | 15#uscalar => returnStep st env index
  | 16#uscalar => code.call st data env profile false
  | 17#uscalar => code.call st data env profile true
  | _ =>
    if alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX then
      .ok (.Err .StackTooLarge, st)
    else do
      let (r, ois, _) ← code.step_wasm2 code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
        st.core data env ctx opcode ()
      .ok (r, { st with core := ois })

/-- The extracted body loop with the empty visitor. -/
abbrev run (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile) (ctx : code.Context)
    (index : U32) (st : code.BodyState) :=
  Wasm2.emptyVisitorLoop data env profile index st ctx.locals ctx.results ()

/-- One iteration of `run`. -/
abbrev loopBody (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (ctx : code.Context) (index : U32) (st : code.BodyState) :=
  Wasm2.emptyVisitorLoop.body data env profile index ctx.locals ctx.results st ()

/-- The loop control flow after one opcode: continue on success and stop with the error otherwise. -/
def continueStep (r : core.result.Result Unit error.OpError × code.BodyState) :
    ControlFlow (code.BodyState × code.EmptyOpVisitor) (core.result.Result Unit error.OpError) :=
  match r.1 with
  | .Ok () => .cont (r.2, ())
  | .Err e => .done (.Err e)

/-- One loop iteration stops at the end of the body (with `TrailingBytes` if bytes remain) and
otherwise reads an opcode, applies the profile's opcode filter and runs `step`. -/
theorem loopBody_eq (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (ctx : code.Context) (index : U32) (st : code.BodyState) :
    loopBody data env profile ctx index st =
      if st.blocks.val = [] then
        .ok (.done (if st.core.pos = Slice.len data then .Ok () else .Err .TrailingBytes))
      else (do
        let r ← reader.read_byte data st.core.pos
        match r with
        | .Err e => .ok (.done (.Err e))
        | .Ok (opcode, pos) =>
          let r ← code.check_opcode profile opcode
          match r with
          | .Err e => .ok (.done (.Err e))
          | .Ok () =>
            let r ← step { st with core := { st.core with pos := pos } } data env profile ctx index
              opcode
            .ok (continueStep r)) := by
  unfold loopBody Wasm2.emptyVisitorLoop.body
  simp only [alloc.vec.Vec.is_empty, bind_ok, List.isEmpty_iff]
  split
  · by_cases hp : st.core.pos = Slice.len data
    · simp [hp]
    · simp [hp]
  · rename_i hn
    congr 1
    funext r
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨op, pos⟩ := pair
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.bind_assoc]
      congr 1
      funext r0
      cases r0 with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
      cases u
      simp only [bind_ok]
      unfold step
      split
      all_goals first
        | (congr 1; funext pair; obtain ⟨r, s⟩ := pair; cases r <;> simp [continueStep,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual])
        | skip
      · unfold returnStep
        simp only [Std.bind_assoc]
        congr 1
        funext pair
        obtain ⟨r, s⟩ := pair
        cases r <;> simp [continueStep,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · split
        · simp [continueStep]
        · simp only [Std.bind_assoc]
          congr 1
          funext pair
          obtain ⟨r, s, v⟩ := pair
          cases v
          cases r <;> simp [continueStep,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Wasm2

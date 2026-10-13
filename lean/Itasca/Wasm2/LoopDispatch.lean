import Itasca.Wasm2.Invariant
import Itasca.Wasm2.EmptyVisitorLoop

open Aeneas Aeneas.Std Result

namespace Itasca.MultiValue

/-- The return arm of the extracted loop, with its state exposed for proofs. -/
def returnStep (st : code.BodyState) (env : module.Env) (index : U32) :
    Result (core.result.Result Unit error.OpError × code.BodyState) := do
  let (r, ois) ← code.pop_results st.core env (.Type index .Results)
  match r with
  | .Err e => .ok (.Err e, { st with core := ois })
  | .Ok () =>
    let ois ← code.mark_unreachable ois
    .ok (.Ok (), { st with core := ois })

/-- Proof adapter for one opcode of the actual multi-value loop. Its exact
factorization is checked below; this is not a separate validity judgment. -/
def step (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (opcode : U8) :
    Result (core.result.Result Unit error.OpError × code.BodyState) := do
  match opcode with
  | 2#uscalar => code.enter st data env .Block
  | 3#uscalar => code.enter st data env .Loop
  | 4#uscalar => code.enter st data env .Then
  | 5#uscalar => code.end_frame st env true
  | 11#uscalar => code.end_frame st env false
  | 12#uscalar => code.branch st data env false
  | 13#uscalar => code.branch st data env true
  | 14#uscalar => code.branch_table st data env
  | 15#uscalar => returnStep st env index
  | 16#uscalar => code.call st data env false
  | 17#uscalar => code.call st data env true
  | _ =>
    if alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX then
      .ok (.Err .StackTooLarge, st)
    else
      let (r, ois, _) ← code.step_wasm2 code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
        st.core data env ctx opcode ()
      .ok (r, { st with core := ois })

abbrev run (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (st : code.BodyState) :=
  code.validate_multi_value_body_loop data env.types env.imports env.globals env.exports
    env.elements env.data_count env.declared_funcs env.start env.func_type_indices env.func_types env.table_types env.mem_types
    env.global_types env.num_imported_funcs env.num_imported_globals index st ctx.locals ctx.results ()

abbrev loopBody (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (st : code.BodyState) :=
  code.validate_multi_value_body_loop.body data env.types env.imports env.globals env.exports
    env.elements env.data_count env.declared_funcs env.start env.func_type_indices env.func_types env.table_types env.mem_types
    env.global_types env.num_imported_funcs env.num_imported_globals index ctx.locals ctx.results st ()

def continueStep (r : core.result.Result Unit error.OpError × code.BodyState) :
    ControlFlow (code.BodyState × code.EmptyOpVisitor) (core.result.Result Unit error.OpError) :=
  match r.1 with
  | .Ok () => .cont (r.2, ())
  | .Err e => .done (.Err e)

theorem loopBody_eq (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (st : code.BodyState) :
    loopBody data env ctx index st =
      if st.blocks.val = [] then
        .ok (.done (if st.core.pos = Slice.len data then .Ok () else .Err .TrailingBytes))
      else (do
        let r ← reader.read_byte data st.core.pos
        match r with
        | .Err e => .ok (.done (.Err e))
        | .Ok (opcode, pos) =>
          let r ← step { st with core := { st.core with pos := pos } } data env ctx index opcode
          .ok (continueStep r)) := by
  unfold loopBody code.validate_multi_value_body_loop.body
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
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      conv_lhs => whnf
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

end Itasca.MultiValue

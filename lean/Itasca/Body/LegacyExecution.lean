import Itasca.Generated.Funs

open Aeneas Aeneas.Std Result ControlFlow

noncomputable section

namespace Itasca

/-! A proof-only snapshot of the former Wasm 1.0 loop. These definitions are
not a Rust execution path. The shared-runtime refinement theorem must relate
this model to the sole extracted body loop before any public proof uses it. -/

/-- [itasca::code::validate_body_with]: loop body 0:
    Source: 'src/code.rs', lines 1442:4-1452:5
    Visibility: public -/
@[rust_loop_body]
def code.validate_body_with_loop.body
  {V : Type} (OpVisitorInst : code.OpVisitor V) (data : Slice Std.U8)
  (env : _root_.Itasca.module.Env)
  (v : alloc.vec.Vec _root_.Itasca.types.ValueType)
  (v1 : alloc.vec.Vec _root_.Itasca.types.ValueType) (v2 : V)
  (st : _root_.Itasca.code.OpIterState) :
  Result (ControlFlow (V × _root_.Itasca.code.OpIterState)
    ((core.result.Result Unit _root_.Itasca.error.OpError) × V))
  := do
  let b ← code.control_stack_empty st
  if b
  then
    let i := Slice.len data
    if st.pos = i
    then ok (done (core.result.Result.Ok (), v2))
    else ok (done (core.result.Result.Err error.OpError.TrailingBytes, v2))
  else
    let (r, st1) ← code.read_op st data
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r1, st2, v3) ←
        code.step OpVisitorInst st1 data env { locals := v, results := v1 } val
          v2
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ => ok (cont (v3, st2))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
        ok (done (r2, v3))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
      ok (done (r1, v2))

/-- [itasca::code::validate_body_with]: loop 0:
    Source: 'src/code.rs', lines 1442:4-1452:5
    Visibility: public -/
@[rust_loop]
def code.validate_body_with_loop
  {V : Type} (OpVisitorInst : code.OpVisitor V) (data : Slice Std.U8)
  (env : _root_.Itasca.module.Env)
  (v : alloc.vec.Vec _root_.Itasca.types.ValueType)
  (v1 : alloc.vec.Vec _root_.Itasca.types.ValueType) (v2 : V)
  (st : _root_.Itasca.code.OpIterState) :
  Result ((core.result.Result Unit _root_.Itasca.error.OpError) × V)
  := do
  loop
    (fun (v3, st1) => code.validate_body_with_loop.body OpVisitorInst data env
      v v1 v3 st1)
    (v2, st)

/-- [itasca::code::validate_body_with]:
    Source: 'src/code.rs', lines 1432:0-1453:1
    Visibility: public -/
def code.validate_body_with_model
  {V : Type} (OpVisitorInst : code.OpVisitor V) (data : Slice Std.U8)
  (env : _root_.Itasca.module.Env) (ctx : _root_.Itasca.code.Context) 
  (v : V) :
  Result ((core.result.Result Unit _root_.Itasca.error.OpError) × V)
  := do
  let i := Slice.len data
  if i > limits.MAX_FUNCTION_BYTES
  then ok (core.result.Result.Err error.OpError.BodyTooLarge, v)
  else
    let s := alloc.vec.Vec.deref ctx.results
    let st ← code.start_function s
    code.validate_body_with_loop OpVisitorInst data env ctx.locals ctx.results
      v st


end Itasca

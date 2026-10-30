import Itasca.Support.BodyState
import Itasca.Wasm2.ProfileFilters

/-!
# Body loop with the empty visitor

Proof-side views of the extracted visiting loop `code.body_loop_loop` instantiated with
`code.EmptyOpVisitor`. `Wasm2.emptyVisitorLoop.body` drops the visitor from the loop body,
`Wasm2.emptyVisitorLoop.body_eq` relates it to the extracted body, and `code.bodyCore` is the
visitor-free body validator.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca

/-- One iteration of the extracted loop body with the visitor argument kept only as a pass-through
value, so semantic proofs do not track the empty visitor. -/
def Wasm2.emptyVisitorLoop.body
  (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile) (type_index : U32)
  (locals : alloc.vec.Vec wasm_types.ValueType)
  (results : alloc.vec.Vec wasm_types.ValueType)
  (st : code.BodyState)
  (visitor : code.EmptyOpVisitor) :
  Result (ControlFlow (code.BodyState ×
    code.EmptyOpVisitor) (core.result.Result Unit
    error.OpError))
  := do
  let b ← alloc.vec.Vec.is_empty Global st.blocks
  if b
  then
    let i2 := Slice.len data
    if st.core.pos != i2
    then ok (done (core.result.Result.Err error.OpError.TrailingBytes))
    else ok (done (core.result.Result.Ok ()))
  else
    let r ← reader.read_byte data st.core.pos
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue (op, «end») =>
      let r0 ← code.check_opcode profile op
      let cf0 ← core.result.Result.Insts.CoreOpsTry.branch r0
      match cf0 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
          match op with
          | 2#uscalar =>
            let (r1, st1) ←
              code.enter { st with core := { st.core with pos := «end» } }
                data
                env profile code.LabelKind.Block
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              ok (cont (st1, visitor))
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r2 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame error.OpError) residual
              ok (done r2)
          | 3#uscalar =>
            let (r1, st1) ←
              code.enter { st with core := { st.core with pos := «end» } }
                data
                env profile code.LabelKind.Loop
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              ok (cont (st1, visitor))
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r2 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame error.OpError) residual
              ok (done r2)
          | 4#uscalar =>
            let (r1, st1) ←
              code.enter { st with core := { st.core with pos := «end» } }
                data
                env profile code.LabelKind.Then
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              ok (cont (st1, visitor))
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r2 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame error.OpError) residual
              ok (done r2)
          | 5#uscalar =>
            let (r1, st1) ←
              code.end_frame
                { st with core := { st.core with pos := «end» } }
                env true
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              ok (cont (st1, visitor))
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r2 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame error.OpError) residual
              ok (done r2)
          | 11#uscalar =>
            let (r1, st1) ←
              code.end_frame
                { st with core := { st.core with pos := «end» } }
                env false
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              ok (cont (st1, visitor))
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r2 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame error.OpError) residual
              ok (done r2)
          | 12#uscalar =>
            let (r1, st1) ←
              code.branch
                { st with core := { st.core with pos := «end» } } data
                env false
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              ok (cont (st1, visitor))
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r2 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame error.OpError) residual
              ok (done r2)
          | 13#uscalar =>
            let (r1, st1) ←
              code.branch
                { st with core := { st.core with pos := «end» } } data
                env true
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              ok (cont (st1, visitor))
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r2 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame error.OpError) residual
              ok (done r2)
          | 14#uscalar =>
            let (r1, st1) ←
              code.branch_table
                { st with core := { st.core with pos := «end» } } data
                env profile
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              ok (cont (st1, visitor))
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r2 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame error.OpError) residual
              ok (done r2)
          | 15#uscalar =>
            let (r1, ois) ←
              code.pop_results { st.core with pos := «end» }
                env (signature.ResultType.Type type_index signature.TypePart.Results)
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let ois1 ← code.mark_unreachable ois
              ok (cont ({ st with core := ois1 }, visitor))
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r2 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame error.OpError) residual
              ok (done r2)
          | 16#uscalar =>
            let (r1, st1) ←
              code.call { st with core := { st.core with pos := «end» } }
                data
                env profile false
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              ok (cont (st1, visitor))
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r2 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame error.OpError) residual
              ok (done r2)
          | 17#uscalar =>
            let (r1, st1) ←
              code.call { st with core := { st.core with pos := «end» } }
                data
                env profile true
            let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
            match cf1 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              ok (cont (st1, visitor))
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r2 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame error.OpError) residual
              ok (done r2)
          | _ =>
            let i2 := alloc.vec.Vec.len st.core.vals
            if i2 = core.num.Usize.MAX
            then ok (done (core.result.Result.Err error.OpError.StackTooLarge))
            else
              let (r1, ois, visitor1) ←
                code.step_wasm2 code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
                  { st.core with pos := «end» } data
                  env { locals, results } op visitor
              let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
              match cf1 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                ok (cont ({ st with core := ois }, visitor1))
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r2 ←
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    Unit (core.convert.FromSame error.OpError)
                    residual
                ok (done r2)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.OpError) residual
        ok (done r1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.OpError) residual
      ok (done r1)

/-- The extracted loop `code.body_loop_loop` run with the empty visitor, returning only the
validation result. -/
def Wasm2.emptyVisitorLoop
  (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile) (type_index : U32)
  (st : code.BodyState)
  (locals : alloc.vec.Vec wasm_types.ValueType)
  (results : alloc.vec.Vec wasm_types.ValueType)
  (visitor : code.EmptyOpVisitor) :
  Result (core.result.Result Unit error.OpError)
  := do
  let (r, _) ← code.body_loop_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor data env
    ⟨locals, results⟩ type_index profile visitor st
  .ok r

/-- Only the placement of the empty visitor changes between the semantic
adapter and the extracted visiting loop. -/
theorem Wasm2.emptyVisitorLoop.body_eq (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (profile : ValidationProfile) (st : code.BodyState) :
    code.body_loop_loop.body code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx index profile () st = (do
      let r ← Wasm2.emptyVisitorLoop.body data env profile index ctx.locals ctx.results st ()
      .ok (match r with | .cont (s, _) => .cont ((), s) | .done result => .done (result, ()))) := by
  unfold code.body_loop_loop.body code.step_profile Wasm2.emptyVisitorLoop.body
  simp only [code.BodyState.blocks_is_empty, Std.bind_assoc]
  congr 1
  funext b
  split
  · split <;> simp
  · simp only [Std.bind_assoc]
    congr 1
    funext r
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨opcode, pos⟩ := pair
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry, Std.bind_assoc]
      congr 1
      funext r0
      cases r0 with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
      cases u
      simp only [bind_ok]
      split
      all_goals simp_all only [code.enter, code.end_frame,
        code.branch, code.branch_table, code.call, Bool.false_eq_true, ↓reduceIte, Std.bind_assoc]
      all_goals first
        | (congr 1; funext pair; rcases pair with ⟨r, s⟩; cases r <;>
            simp [code.OpVisitor.on_block.default,
              code.OpVisitor.on_loop.default, code.OpVisitor.on_if.default,
              code.OpVisitor.on_else.default, code.OpVisitor.on_end.default,
              code.OpVisitor.on_br.default, code.OpVisitor.on_br_if.default,
              code.OpVisitor.on_call.default, code.OpVisitor.on_call_indirect.default,
              code.OpVisitor.on_return.default, code.visit, Std.bind_assoc,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual])
        | skip
      all_goals try (rcases s with ⟨s, v⟩; cases v; simp)
      split
      · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp only [Std.bind_assoc]
        congr 1
        funext pair
        obtain ⟨r, s, v⟩ := pair
        cases v
        cases r <;> simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- The visitor-free body validator with the loop replaced by `Wasm2.emptyVisitorLoop`. -/
def code.bodyCore
  (data : Slice U8) (env : metadata.Env)
  (locals results : alloc.vec.Vec wasm_types.ValueType) (type_index : U32)
  (profile : ValidationProfile) :
  Result (core.result.Result Unit error.OpError)
  := do
  let i := Slice.len data
  if i > limits.MAX_FUNCTION_BYTES
  then ok (core.result.Result.Err error.OpError.BodyTooLarge)
  else
    let i1 ← lift (UScalar.cast .Usize type_index)
    let i2 := alloc.vec.Vec.len env.types
    if i1 >= i2
    then ok (core.result.Result.Err error.OpError.UnknownType)
    else
      let ft ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          wasm_types.FuncType) env.types i1
      let r ← code.check_func_type ft
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let st ←
          code.push_frame
            {
              core :=
                {
                  vals := (alloc.vec.Vec.new code.StackType),
                  ctrls := (alloc.vec.Vec.new code.Ctrl),
                  pos := 0#usize
                }
            } code.LabelKind.Body (signature.BlockType.TypeIndex type_index)
        Wasm2.emptyVisitorLoop data env profile type_index st locals results ()
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.OpError) residual

end Itasca

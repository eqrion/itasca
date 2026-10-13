import Itasca.Support.BodyState

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca

/-! Checked projections of the actual visiting body loop. The normalized body
keeps semantic proofs independent of the empty visitor's bookkeeping. -/

def code.validate_multi_value_body_loop.body
  (data : Slice U8) (v : alloc.vec.Vec types.FuncType)
  (v1 : alloc.vec.Vec module.Import)
  (v2 : alloc.vec.Vec module.Global)
  (v3 : alloc.vec.Vec module.Export)
  (v4 : alloc.vec.Vec module.Element) (data_count : Option U32)
  (declared_funcs : alloc.vec.Vec U32) (o : Option U32)
  (v5 : alloc.vec.Vec U32)
  (v6 : alloc.vec.Vec types.FuncType)
  (v7 : alloc.vec.Vec types.TableType)
  (v8 : alloc.vec.Vec types.MemType)
  (v9 : alloc.vec.Vec types.GlobalType) (i : Usize)
  (i1 : Usize) (type_index : U32)
  (locals : alloc.vec.Vec types.ValueType)
  (v10 : alloc.vec.Vec types.ValueType)
  (st : code.BodyState)
  (visitor : code.EmptyOpVisitor) :
  Result (ControlFlow (code.BodyState ×
    code.EmptyOpVisitor) (core.result.Result Unit
    error.OpError))
  := do
  let env : module.Env := ⟨v, v1, v2, v3, v4, data_count, declared_funcs, o, v5, v6, v7, v8, v9, i, i1⟩
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
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (op, «end») := val
      match op with
      | 2#uscalar =>
        let (r1, st1) ←
          code.enter { st with core := { st.core with pos := «end» } }
            data
            env code.LabelKind.Block
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
            env code.LabelKind.Loop
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
            env code.LabelKind.Then
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
            env
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
      | 17#uscalar =>
        let (r1, st1) ←
          code.call { st with core := { st.core with pos := «end» } }
            data
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
      | _ =>
        let i2 := alloc.vec.Vec.len st.core.vals
        if i2 = core.num.Usize.MAX
        then ok (done (core.result.Result.Err error.OpError.StackTooLarge))
        else
          let (r1, ois, visitor1) ←
            code.step_wasm2 code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
              { st.core with pos := «end» } data
              env { locals, results := v10 } op visitor
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

def code.validate_multi_value_body_loop
  (data : Slice U8) (v : alloc.vec.Vec types.FuncType)
  (v1 : alloc.vec.Vec module.Import)
  (v2 : alloc.vec.Vec module.Global)
  (v3 : alloc.vec.Vec module.Export)
  (v4 : alloc.vec.Vec module.Element) (data_count : Option U32)
  (declared_funcs : alloc.vec.Vec U32) (o : Option U32)
  (v5 : alloc.vec.Vec U32)
  (v6 : alloc.vec.Vec types.FuncType)
  (v7 : alloc.vec.Vec types.TableType)
  (v8 : alloc.vec.Vec types.MemType)
  (v9 : alloc.vec.Vec types.GlobalType) (i : Usize)
  (i1 : Usize) (type_index : U32)
  (st : code.BodyState)
  (locals : alloc.vec.Vec types.ValueType)
  (v10 : alloc.vec.Vec types.ValueType)
  (visitor : code.EmptyOpVisitor) :
  Result (core.result.Result Unit error.OpError)
  := do
  let (r, _) ← code.body_loop_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor data
    ⟨v, v1, v2, v3, v4, data_count, declared_funcs, o, v5, v6, v7, v8, v9, i, i1⟩
    ⟨locals, v10⟩ type_index .Wasm2 visitor st
  .ok r

/-- Only the placement of the empty visitor changes between the semantic
adapter and the extracted visiting loop. -/
theorem code.validate_multi_value_body_loop.body_eq (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (st : code.BodyState) :
    code.body_loop_loop.body code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx index .Wasm2 () st = (do
      let r ← code.validate_multi_value_body_loop.body data env.types env.imports env.globals
        env.exports env.elements env.data_count env.declared_funcs env.start env.func_type_indices env.func_types env.table_types
        env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
        index ctx.locals ctx.results st ()
      .ok (match r with | .cont (s, _) => .cont ((), s) | .done result => .done (result, ()))) := by
  unfold code.body_loop_loop.body code.step_profile code.validate_multi_value_body_loop.body
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
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry]
      conv_lhs => arg 1; whnf
      conv_rhs => arg 1; whnf
      split
      all_goals simp_all only [bind_ok, code.enter, code.end_frame,
        code.branch, code.branch_table, code.call, Bool.false_eq_true, ↓reduceIte, Std.bind_assoc]
      all_goals first
        | (congr 1; funext pair; rcases pair with ⟨r, s⟩; cases r <;>
            simp [code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor, code.OpVisitor.on_block.default,
              code.OpVisitor.on_loop.default, code.OpVisitor.on_if.default,
              code.OpVisitor.on_else.default, code.OpVisitor.on_end.default,
              code.OpVisitor.on_br.default, code.OpVisitor.on_br_if.default,
              code.OpVisitor.on_call.default, code.OpVisitor.on_call_indirect.default,
              code.OpVisitor.on_return.default, code.visit, Std.bind_assoc,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual])
        | skip
      all_goals try (rename_i pair; rcases pair with ⟨a, b⟩; rfl)
      all_goals try (rcases s with ⟨s, v⟩; cases v; simp [
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual])
      split
      · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp only [Std.bind_assoc]
        congr 1
        funext pair
        obtain ⟨r, s, v⟩ := pair
        cases v
        cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

def code.bodyCore
  (data : Slice U8) (env : module.Env)
  (locals : alloc.vec.Vec types.ValueType) (type_index : U32)
  :
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
          types.FuncType) env.types i1
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
        code.validate_multi_value_body_loop data env.types env.imports env.globals
          env.exports env.elements env.data_count env.declared_funcs env.start env.func_type_indices
          env.func_types env.table_types env.mem_types env.global_types
          env.num_imported_funcs env.num_imported_globals type_index st locals
          (alloc.vec.Vec.new types.ValueType) ()
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame error.OpError) residual


 theorem code.validate_multi_value_body.eq_core (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32) :
    code.validate_multi_value_body data env locals index = code.bodyCore data env locals index := by
  unfold code.validate_multi_value_body code.validate_multi_value_body_with code.validate_body_with_profile code.initial_state code.bodyCore
  simp only [Std.bind_assoc]
  split
  · simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp only [Std.bind_assoc]
    congr 1
    funext i
    split
    · simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · simp only [Std.bind_assoc]
      congr 1
      funext ft
      congr 1
      funext r
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
        cases u
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.bind_assoc]
        rfl

end Itasca

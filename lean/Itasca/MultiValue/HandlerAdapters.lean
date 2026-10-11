import Itasca.Profile.State
import Itasca.Support.Result

open Aeneas Aeneas.Std Result

namespace Itasca

/- State-only presentations of metadata-returning handlers. -/

def MultiValue.branchCore
  (st : _root_.Itasca.multi_value.State) (data : Slice Std.U8)
  (env : _root_.Itasca.module.Env) (conditional : Bool) :
  Result ((core.result.Result Unit _root_.Itasca.error.OpError) ×
    _root_.Itasca.multi_value.State)
  := do
  let (r, st1) ← multi_value.read_label st data
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    if conditional
    then
      let (r1, ois) ← code.pop_with_type st1.core types.ValueType.I32
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let (r2, ois1) ← multi_value.pop_results ois env val
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          if conditional
          then
            let (r3, ois2) ← multi_value.push_results ois1 env val
            ok (r3, { st1 with core := ois2 })
          else
            let ois2 ← code.mark_unreachable ois1
            ok (core.result.Result.Ok (), { st1 with core := ois2 })
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
          ok (r3, { st1 with core := ois1 })
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
        ok (r2, { st1 with core := ois })
    else
      let (r1, ois) ← multi_value.pop_results st1.core env val
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        if conditional
        then
          let (r2, ois1) ← multi_value.push_results ois env val
          ok (r2, { st1 with core := ois1 })
        else
          let ois1 ← code.mark_unreachable ois
          ok (core.result.Result.Ok (), { st1 with core := ois1 })
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
        ok (r2, { st1 with core := ois })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
    ok (r1, st1)

def MultiValue.callCore
  (st : _root_.Itasca.multi_value.State) (data : Slice Std.U8)
  (env : _root_.Itasca.module.Env) (indirect : Bool) :
  Result ((core.result.Result Unit _root_.Itasca.error.OpError) ×
    _root_.Itasca.multi_value.State)
  := do
  let r ← reader.read_u32_leb data st.core.pos
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (index, «end») := val
    let i ← lift (UScalar.cast .Usize index)
    if indirect
    then
      let r1 ← reader.read_byte data «end»
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let (reserved, end1) := val1
        if reserved != 0#u8
        then
          ok (core.result.Result.Err error.OpError.ReservedByteNotZero,
            { st with core := { st.core with pos := «end» } })
        else
          let b ← alloc.vec.Vec.is_empty Global env.table_types
          if b
          then
            ok (core.result.Result.Err error.OpError.UnknownTable,
              { st with core := { st.core with pos := end1 } })
          else
            let i1 := alloc.vec.Vec.len env.types
            if i >= i1
            then
              ok (core.result.Result.Err error.OpError.UnknownType,
                { st with core := { st.core with pos := end1 } })
            else
              let (r2, ois) ←
                code.pop_with_type { st.core with pos := end1 }
                  types.ValueType.I32
              let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
              match cf2 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let ft ←
                  alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
                    _root_.Itasca.types.FuncType) env.types i
                let (r3, ois1) ← multi_value.apply_func_type ois ft
                ok (r3, { st with core := ois1 })
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r3 ←
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    Unit (core.convert.FromSame _root_.Itasca.error.OpError)
                    residual
                ok (r3, { st with core := ois })
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
        ok (r2, { st with core := { st.core with pos := «end» } })
    else
      let i1 := alloc.vec.Vec.len env.func_types
      if i >= i1
      then
        ok (core.result.Result.Err error.OpError.UnknownFunc,
          { st with core := { st.core with pos := «end» } })
      else
        let ft ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            _root_.Itasca.types.FuncType) env.func_types i
        let (r1, ois) ←
          multi_value.apply_func_type { st.core with pos := «end» } ft
        ok (r1, { st with core := ois })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
    ok (r1, st)


theorem multi_value.branch.eq_core (st : multi_value.State) (data : Slice U8)
    (env : module.Env) (conditional : Bool) :
    multi_value.branch st data env conditional = MultiValue.branchCore st data env conditional := by
  simp only [multi_value.branch, multi_value.branch_info, MultiValue.branchCore,
    multi_value.read_label, Std.bind_assoc]
  congr 1
  funext x
  obtain ⟨r, s⟩ := x
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨depth, ts⟩ := pair
    cases conditional <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Std.bind_assoc]
    all_goals
      congr 1
      funext x
      obtain ⟨r, ois⟩ := x
      cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Std.bind_assoc]
    all_goals
      congr 1
      funext x
      obtain ⟨r, ois⟩ := x
      cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Std.bind_assoc]
    all_goals
      congr 1
      funext x
      obtain ⟨r, ois⟩ := x
      cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Std.bind_assoc]

theorem multi_value.call.eq_core (st : multi_value.State) (data : Slice U8)
    (env : module.Env) (indirect : Bool) :
    multi_value.call st data env indirect = MultiValue.callCore st data env indirect := by
  simp only [multi_value.call, multi_value.call_info, MultiValue.callCore, Std.bind_assoc]
  congr 1
  funext r
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨index, next⟩ := pair
    simp only [uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift, Std.bind_assoc]
    cases indirect with
    | false =>
      simp only [uncurry, Bool.false_eq_true, ↓reduceIte, Std.bind_assoc]
      split
      · simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp only [Std.bind_assoc]
        congr 1
        funext ft
        congr 1
        funext x
        obtain ⟨r, ois⟩ := x
        cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | true =>
      simp only [uncurry, ↓reduceIte, Std.bind_assoc]
      congr 1
      funext r
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨reserved, next⟩ := pair
        simp only [uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.bind_assoc]
        split
        · simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        · simp only [Std.bind_assoc]
          congr 1
          funext empty
          cases empty <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Std.bind_assoc]
          split
          · simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          · simp only [Std.bind_assoc]
            congr 1
            funext x
            obtain ⟨r, ois⟩ := x
            cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Std.bind_assoc]
            congr 1
            funext ft
            congr 1
            funext x
            obtain ⟨r, ois⟩ := x
            cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca

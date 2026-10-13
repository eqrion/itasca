import Itasca.Support.BodyState
import Itasca.Support.Result

open Aeneas Aeneas.Std Result

namespace Itasca

/- State-only presentations of metadata-returning handlers. -/

def Wasm2.branchCore
  (st : _root_.Itasca.code.BodyState) (data : Slice Std.U8)
  (env : _root_.Itasca.module.Env) (conditional : Bool) :
  Result ((core.result.Result Unit _root_.Itasca.error.OpError) ×
    _root_.Itasca.code.BodyState)
  := do
  let (r, st1) ← code.read_multi_value_label st data
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    if conditional
    then
      let (r1, ois) ← code.pop_with_type st1.core types.ValueType.I32
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let (r2, ois1) ← code.pop_results ois env val
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          if conditional
          then
            let (r3, ois2) ← code.push_results ois1 env val
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
      let (r1, ois) ← code.pop_results st1.core env val
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        if conditional
        then
          let (r2, ois1) ← code.push_results ois env val
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

def Wasm2.callCore (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (indirect : Bool) :
    Result (core.result.Result Unit error.OpError × code.BodyState) := do
  if indirect then
    let (r, out) ← code.call_indirect_info st data env
    match r with
    | .Err e => .ok (.Err e, out)
    | .Ok _ => .ok (.Ok (), out)
  else
    let r ← reader.read_u32_leb data st.core.pos
    match r with
    | .Err e => .ok (.Err e, st)
    | .Ok (index, next) =>
      let i ← lift (UScalar.cast .Usize index)
      if i ≥ alloc.vec.Vec.len env.func_types then
        .ok (.Err .UnknownFunc, { st with core := { st.core with pos := next } })
      else
        let ft ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice types.FuncType)
          env.func_types i
        let (r, out) ← code.apply_func_type { st.core with pos := next } ft
        .ok (r, { st with core := out })


theorem code.branch.eq_core (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (conditional : Bool) :
    code.branch st data env conditional = Wasm2.branchCore st data env conditional := by
  simp only [code.branch, code.branch_info, Wasm2.branchCore,
    code.read_multi_value_label, Std.bind_assoc]
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

theorem code.call.eq_core (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (indirect : Bool) :
    code.call st data env indirect = Wasm2.callCore st data env indirect := by
  cases indirect with
  | true =>
    simp only [code.call, Wasm2.callCore, ↓reduceIte]
    congr 1
    funext pair
    obtain ⟨r, out⟩ := pair
    cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | false =>
    simp only [code.call, code.call_info, code.take_index, Wasm2.callCore,
      Bool.false_eq_true, ↓reduceIte, Std.bind_assoc]
    congr 1
    funext r
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨index, next⟩ := pair
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry, Std.bind_assoc]
      congr 1
      funext i
      split
      · simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp only [Std.bind_assoc]
        congr 1
        funext ft
        congr 1
        funext pair
        obtain ⟨r, out⟩ := pair
        cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca

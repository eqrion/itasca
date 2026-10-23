import Itasca.Support.BodyState
import Itasca.Support.Result

/-!
# `br_table` handler adapters

State-only presentations of the `br_table` handler `code.branch_table` and its worker loop
`code.branch_table_with_loop` with the empty visitor. `Wasm2.branchTableLoop` and
`Wasm2.tableCore` project away the visitor, `Wasm2.tableBody_eq` relates the loop bodies, and
`code.branch_table.eq_core` shows that the extracted `code.branch_table` equals `Wasm2.tableCore`.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca

/-- A pure result projection preserves the producer's postcondition. -/
theorem ResultFacts.map_spec {A B : Type} (m : Result A) (f : A → B) (P : B → Prop)
    (h : m ⦃ x => P (f x) ⦄) :
    (do let x ← m; .ok (f x)) ⦃ P ⦄ :=
  WP.spec_bind h (fun _ hx => by simpa only [WP.spec_ok] using hx)

/-- One iteration of `code.branch_table_with_loop` with the empty visitor removed. -/
def Wasm2.branchTableLoop.body
  (data : Slice Std.U8) (env : _root_.Itasca.module.Env) (profile : ValidationProfile)
  (count : Std.U32) (ois : _root_.Itasca.code.OpIterState)
  (arity : Option Std.Usize) (first : signature.ResultType) (i : Std.U32) :
  Result (ControlFlow (_root_.Itasca.code.OpIterState × (Option Std.Usize) ×
    signature.ResultType × Std.U32)
    ((core.result.Result Unit _root_.Itasca.error.OpError) ×
    _root_.Itasca.code.BodyState))
  := do
  let (r, st) ← code.read_label_info { core := ois } data
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (_, ts) := val
    let first1 ← if i = 0#u32 then ok ts else ok first
    let r1 ← code.check_table_target profile env first1 ts
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let r2 ← signature.ResultType.len ts env
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        match arity with
        | none =>
          let r3 ← code.check_suffix st.core env ts
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            if i = count
            then
              let ois1 ← code.mark_unreachable st.core
              ok (done (core.result.Result.Ok (), { core := ois1 }))
            else
              let i1 ← i + 1#u32
              ok (cont (st.core, some val1, first1, i1))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r4 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
            ok (done (r4, st))
        | some expected =>
          if expected != val1
          then ok (done (core.result.Result.Err error.OpError.TypeMismatch, st))
          else
            let r3 ← code.check_suffix st.core env ts
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              if i = count
              then
                let ois1 ← code.mark_unreachable st.core
                ok (done (core.result.Result.Ok (), { core := ois1 }))
              else
                let i1 ← i + 1#u32
                ok (cont (st.core, arity, first1, i1))
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r4 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
              ok (done (r4, st))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
        ok (done (r3, st))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
      ok (done (r2, st))
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
    ok (done (r1, st))

/-- The extracted `code.branch_table_with_loop` with the empty visitor, returning only the result
and body state. -/
def Wasm2.branchTableLoop
  (ois : code.OpIterState) (data : Slice U8) (env : module.Env) (profile : ValidationProfile)
  (count : U32) (arity : Option Usize) (first : signature.ResultType) (i : U32) :
  Result (core.result.Result Unit error.OpError × code.BodyState) := do
  let (r, s, _) ← code.branch_table_with_loop
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor ois data env profile () count arity first i
  .ok (r, s)

/-- `code.branch_table_with` with the empty visitor, unfolded to `Wasm2.branchTableLoop`. -/
def Wasm2.tableCore
  (st : _root_.Itasca.code.BodyState) (data : Slice Std.U8)
  (env : _root_.Itasca.module.Env) (profile : ValidationProfile) :
  Result ((core.result.Result Unit _root_.Itasca.error.OpError) ×
    _root_.Itasca.code.BodyState)
  := do
  let r ← reader.read_u32_leb data st.core.pos
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (count, «end») := val
    let (r1, ois) ←
      code.pop_with_type { st.core with pos := «end» } types.ValueType.I32
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      Wasm2.branchTableLoop ois data env profile count none .Empty 0#u32
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
      ok (r2, { core := ois })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
    ok (r1, st)


namespace Wasm2

@[simp] def tableCont (p : code.OpIterState × Option Usize × signature.ResultType × U32) :=
  (p.1, (), p.2.1, p.2.2.1, p.2.2.2)

@[simp] def tableDone (p : core.result.Result Unit error.OpError × code.BodyState) :=
  (p.1, p.2, ())

@[simp] def tableFlow :
    ControlFlow (code.OpIterState × Option Usize × signature.ResultType × U32)
      (core.result.Result Unit error.OpError × code.BodyState) →
    ControlFlow (code.OpIterState × Unit × Option Usize × signature.ResultType × U32)
      (core.result.Result Unit error.OpError × code.BodyState × Unit)
  | .cont p => .cont (tableCont p)
  | .done p => .done (tableDone p)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- The extracted loop body with the empty visitor equals `Wasm2.branchTableLoop.body` up to the
visitor component. -/
theorem tableBody_eq (data : Slice U8) (env : module.Env) (profile : ValidationProfile)
    (count : U32) (ois : code.OpIterState) (arity : Option Usize) (first : signature.ResultType)
    (i : U32) :
    code.branch_table_with_loop.body code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env profile count ois () arity first i =
      (do let cf ← Wasm2.branchTableLoop.body data env profile count ois arity first i
          .ok (tableFlow cf)) := by
  simp only [code.branch_table_with_loop.body, Wasm2.branchTableLoop.body, Std.bind_assoc]
  congr 1
  funext x
  obtain ⟨r, st⟩ := x
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      tableFlow, tableDone]
  | Ok pair =>
    obtain ⟨depth, ts⟩ := pair
    simp only [uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.bind_assoc]
    congr 1
    funext first1
    congr 1
    funext r1
    cases r1 with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        tableFlow, tableDone]
    | Ok u =>
      cases u
      simp only [bind_ok]
      by_cases h : i = count <;> cases arity <;>
        simp [h, code.OpVisitor.on_br_table_label.default, code.OpVisitor.on_br_table.default,
          code.visit,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          Std.bind_assoc, tableFlow, tableCont, tableDone]
      all_goals
        congr 1
        funext r
        cases r <;> simp [Std.bind_assoc]
      all_goals try split <;> simp [Std.bind_assoc]
      all_goals
        congr 1
        funext r
        cases r <;> simp [Std.bind_assoc]

end Wasm2

/-- The extracted `code.branch_table_with` with the empty visitor equals `Wasm2.tableCore`. -/
theorem code.branch_table_with.eq_core (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (profile : ValidationProfile) :
    (do let (r, s, _) ← code.branch_table_with code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
          st data env profile (); .ok (r, s)) = Wasm2.tableCore st data env profile := by
  simp only [code.branch_table_with, Wasm2.tableCore,
    Wasm2.branchTableLoop, Std.bind_assoc]
  congr 1
  funext r
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨count, next⟩ := pair
    simp only [uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.bind_assoc]
    congr 1
    funext x
    obtain ⟨r, ois⟩ := x
    cases r <;> simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- The extracted `code.branch_table` equals `Wasm2.tableCore`. -/
theorem code.branch_table.eq_core (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (profile : ValidationProfile) :
    code.branch_table st data env profile = Wasm2.tableCore st data env profile := by
  rw [← code.branch_table_with.eq_core]
  simp only [code.branch_table]

end Itasca

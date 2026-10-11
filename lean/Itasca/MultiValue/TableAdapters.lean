import Itasca.Profile.State
import Itasca.Support.Result

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca

/-- A pure result projection preserves the producer's postcondition. -/
theorem ResultFacts.map_spec {A B : Type} (m : Result A) (f : A → B) (P : B → Prop)
    (h : m ⦃ x => P (f x) ⦄) :
    (do let x ← m; .ok (f x)) ⦃ P ⦄ :=
  WP.spec_bind h (fun _ hx => by simpa only [WP.spec_ok] using hx)

/- Proof-only no-op projections of the shared visiting table loop. The equations
below connect these state views to the actual extracted generic worker. -/

def code.branch_table_loop.body
  (data : Slice Std.U8) (env : _root_.Itasca.module.Env) (count : Std.U32)
  (ois : _root_.Itasca.code.OpIterState)
  (v : alloc.vec.Vec _root_.Itasca.signature.BlockType)
  (arity : Option Std.Usize) (i : Std.U32) :
  Result (ControlFlow (_root_.Itasca.code.OpIterState × (alloc.vec.Vec
    _root_.Itasca.signature.BlockType) × (Option Std.Usize) × Std.U32)
    ((core.result.Result Unit _root_.Itasca.error.OpError) ×
    _root_.Itasca.code.BodyState))
  := do
  let (r, st) ← code.read_multi_value_label { core := ois } data
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ← signature.ResultType.len val env
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      match arity with
      | none =>
        let r2 ← code.check_suffix st.core env val
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          if i = count
          then
            let ois1 ← code.mark_unreachable st.core
            ok (done (core.result.Result.Ok (), { st with core := ois1 }))
          else
            let i1 ← i + 1#u32
            ok (cont (st.core, st.blocks, some val1, i1))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
          ok (done (r3, st))
      | some expected =>
        if expected != val1
        then ok (done (core.result.Result.Err error.OpError.TypeMismatch, st))
        else
          let r2 ← code.check_suffix st.core env val
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            if i = count
            then
              let ois1 ← code.mark_unreachable st.core
              ok (done (core.result.Result.Ok (), { st with core := ois1 }))
            else let i1 ← i + 1#u32
                 ok (cont (st.core, st.blocks, arity, i1))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r3 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame _root_.Itasca.error.OpError)
                residual
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

/-- The legacy state view is a projection of the actual visiting loop. -/
def code.branch_table_loop
  (ois : code.OpIterState) (blocks : alloc.vec.Vec signature.BlockType)
  (data : Slice U8) (env : module.Env) (count : U32) (arity : Option Usize) (i : U32) :
  Result (core.result.Result Unit error.OpError × code.BodyState) := do
  let (r, s, _) ← code.branch_table_with_loop
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor ois data env () count arity i
  .ok (r, s)

def MultiValue.tableCore
  (st : _root_.Itasca.code.BodyState) (data : Slice Std.U8)
  (env : _root_.Itasca.module.Env) :
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
      code.branch_table_loop ois st.blocks data env count none 0#u32
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
      ok (r2, { st with core := ois })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.OpError) residual
    ok (r1, st)


namespace MultiValue

@[simp] def tableCont (p : code.OpIterState × alloc.vec.Vec signature.BlockType × Option Usize × U32) :=
  (p.1, (), p.2.2.1, p.2.2.2)

@[simp] def tableDone (p : core.result.Result Unit error.OpError × code.BodyState) :=
  (p.1, p.2, ())

@[simp] def tableFlow :
    ControlFlow (code.OpIterState × alloc.vec.Vec signature.BlockType × Option Usize × U32)
      (core.result.Result Unit error.OpError × code.BodyState) →
    ControlFlow (code.OpIterState × Unit × Option Usize × U32)
      (core.result.Result Unit error.OpError × code.BodyState × Unit)
  | .cont p => .cont (tableCont p)
  | .done p => .done (tableDone p)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem tableBody_eq (data : Slice U8) (env : module.Env) (count : U32)
    (ois : code.OpIterState) (blocks : alloc.vec.Vec signature.BlockType)
    (arity : Option Usize) (i : U32) :
    code.branch_table_with_loop.body code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env count ois () arity i =
      (do let cf ← code.branch_table_loop.body data env count ois blocks arity i
          .ok (tableFlow cf)) := by
  simp only [code.branch_table_with_loop.body, code.branch_table_loop.body,
    code.read_multi_value_label, Std.bind_assoc]
  congr 1
  funext x
  obtain ⟨r, st⟩ := x
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      tableFlow, tableDone]
  | Ok pair =>
    obtain ⟨depth, ts⟩ := pair
    simp only [uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    by_cases h : i = count <;> cases arity <;>
      simp [h, code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor,
        code.OpVisitor.on_br_table_label.default, code.OpVisitor.on_br_table.default,
        code.visit, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        Std.bind_assoc, tableFlow, tableCont, tableDone]
    all_goals
      congr 1
      funext r
      cases r <;> simp [Std.bind_assoc, tableFlow, tableCont, tableDone]
    all_goals try split <;> simp [Std.bind_assoc, tableFlow, tableCont, tableDone]
    all_goals
      congr 1
      funext r
      cases r <;> simp [Std.bind_assoc, tableFlow, tableCont, tableDone]

end MultiValue

/-- The non-visiting table wrapper executes the same generic reader and loop. -/
theorem code.branch_table.eq_core (st : code.BodyState) (data : Slice U8) (env : module.Env) :
    code.branch_table st data env = MultiValue.tableCore st data env := by
  simp only [code.branch_table, code.branch_table_with, MultiValue.tableCore,
    code.branch_table_loop, Std.bind_assoc]
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
    cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca

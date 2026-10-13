import Itasca.Support.LiteralDispatch
import Itasca.Handler.Control

/-!
# Core visitor steps

`CoreVisitor.Total` states that the hooks of the core instruction subset return normally.
`CoreVisitor.run` models the shape of an extracted `code.step` case, a reader followed by a hook,
and `run.spec` carries a reader postcondition through it. The `code.step_*.of_read` theorems
specialise this to individual opcodes. The core subset is `nop`, `unreachable`, `i32.const`,
`i32.add`, `drop` and the control instructions `block`, `loop`, `if`, `else`, `end`, `br`,
`br_if` and `return`. Covers the Wasm 1.0 step `code.step`.
-/

open Aeneas Aeneas.Std

namespace Itasca.CoreVisitor

/-- The hooks used by the core instruction subset return normally. A hook may still reject. -/
structure Total {V : Type} (visitor : code.OpVisitor V) : Prop where
  nop : ∀ v st, ∃ res v', visitor.on_nop v st = .ok (res, v')
  unreachable : ∀ v st, ∃ res v', visitor.on_unreachable v st = .ok (res, v')
  i32Const : ∀ v st n, ∃ res v', visitor.on_i32_const v st n = .ok (res, v')
  i32Add : ∀ v st, ∃ res v', visitor.on_i32_add v st = .ok (res, v')
  drop : ∀ v st t, ∃ res v', visitor.on_drop v st t = .ok (res, v')
  block : ∀ v st bt, ∃ res v', visitor.on_block v st bt = .ok (res, v')
  loop : ∀ v st bt, ∃ res v', visitor.on_loop v st bt = .ok (res, v')
  if_ : ∀ v st bt, ∃ res v', visitor.on_if v st bt = .ok (res, v')
  else_ : ∀ v st bt, ∃ res v', visitor.on_else v st bt = .ok (res, v')
  end_ : ∀ v st kind bt, ∃ res v', visitor.on_end v st kind bt = .ok (res, v')
  br : ∀ v st depth bt, ∃ res v', visitor.on_br v st depth bt = .ok (res, v')
  brIf : ∀ v st depth bt, ∃ res v', visitor.on_br_if v st depth bt = .ok (res, v')
  return_ : ∀ v st, ∃ res v', visitor.on_return v st = .ok (res, v')

/-- The empty visitor is total on the core instruction subset. -/
theorem empty_total : Total code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor := by
  constructor <;> intros <;> exact ⟨.Ok (), _, rfl⟩

/-- The shape of an extracted instruction step: run a reader, then call a visitor hook on its
output. A reader error skips the hook, and a hook rejection becomes an `OpError.Visitor`. -/
def run {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V) : Result (core.result.Result Unit error.OpError × code.OpIterState × V) := do
  let (res, st) ← read
  let cf ← core.result.Result.Insts.CoreOpsTry.branch res
  match cf with
  | .Continue a =>
    let (vis, v') ← hook v st a
    let vr ← code.visit vis
    let cf' ← core.result.Result.Insts.CoreOpsTry.branch vr
    match cf' with
    | .Continue _ => .ok (.Ok (), st, v')
    | .Break residual =>
      let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame error.OpError) residual
      .ok (r, st, v')
  | .Break residual =>
    let r ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      Unit (core.convert.FromSame error.OpError) residual
    .ok (r, st, v)

/-- A reader postcondition on the state carries through `run` for a total hook, including when the
hook rejects. -/
theorem run.spec {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V) (Q : code.OpIterState → Prop) (P : A → code.OpIterState → Prop)
    (hread : read ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hhook : ∀ st a, ∃ res v', hook v st a = .ok (res, v')) :
    run read hook v ⦃ r => Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  obtain ⟨⟨res, st⟩, hr, hQ, hP⟩ := WP.spec_imp_exists hread
  dsimp only at hQ hP
  cases res with
  | Err e =>
    rw [WP.spec_equiv_exists]
    exact ⟨(.Err e, st, v), by simp [run, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], hQ, by simp⟩
  | Ok a =>
    obtain ⟨vis, v', hv⟩ := hhook st a
    cases vis with
    | Err e =>
      rw [WP.spec_equiv_exists]
      exact ⟨(.Err (.Visitor e), st, v'), by simp [run, hr, hv, code.visit, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], hQ, by simp⟩
    | Ok u =>
      rw [WP.spec_equiv_exists]
      exact ⟨(.Ok (), st, v'), by simp [run, hr, hv, code.visit, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], hQ, fun _ => ⟨a, hP a rfl⟩⟩

end Itasca.CoreVisitor

namespace Itasca

private theorem block_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_BLOCK v =
      CoreVisitor.run (code.read_block st data) (fun v s bt => visitor.on_block v s (Control.signature bt)) v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lifts a `code.read_block` postcondition to `code.step` at `OP_BLOCK` for a total visitor. -/
theorem code.step_block.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : code.BlockType → code.OpIterState → Prop)
    (hread : code.read_block st data ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_BLOCK v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [block_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread (fun s bt => hvisitor.block v s (Control.signature bt))

private theorem loop_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_LOOP v =
      CoreVisitor.run (code.read_loop st data) (fun v s bt => visitor.on_loop v s (Control.signature bt)) v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lifts a `code.read_loop` postcondition to `code.step` at `OP_LOOP` for a total visitor. -/
theorem code.step_loop.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : code.BlockType → code.OpIterState → Prop)
    (hread : code.read_loop st data ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_LOOP v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [loop_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread (fun s bt => hvisitor.loop v s (Control.signature bt))

private theorem if_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_IF v =
      CoreVisitor.run (code.read_if st data) (fun v s bt => visitor.on_if v s (Control.signature bt)) v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lifts a `code.read_if` postcondition to `code.step` at `OP_IF` for a total visitor. -/
theorem code.step_if.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : code.BlockType → code.OpIterState → Prop)
    (hread : code.read_if st data ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_IF v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [if_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread (fun s bt => hvisitor.if_ v s (Control.signature bt))

private theorem else_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_ELSE v =
      CoreVisitor.run (code.read_else st) (fun v s bt => visitor.on_else v s (Control.signature bt)) v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lifts a `code.read_else` postcondition to `code.step` at `OP_ELSE` for a total visitor. -/
theorem code.step_else.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : code.BlockType → code.OpIterState → Prop)
    (hread : code.read_else st ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_ELSE v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [else_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread (fun s bt => hvisitor.else_ v s (Control.signature bt))

private theorem end_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_END v =
      CoreVisitor.run (code.read_end st) (fun v s arg => visitor.on_end v s arg.1 (Control.signature arg.2)) v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lifts a `code.read_end` postcondition to `code.step` at `OP_END` for a total visitor. -/
theorem code.step_end.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : code.LabelKind × code.BlockType → code.OpIterState → Prop)
    (hread : code.read_end st ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_END v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [end_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread ((fun s arg => hvisitor.end_ v s arg.1 (Control.signature arg.2)))

private theorem br_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_BR v =
      CoreVisitor.run (code.read_br st data) (fun v s arg => visitor.on_br v s arg.1 (Control.resultView arg.2)) v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lifts a `code.read_br` postcondition to `code.step` at `OP_BR` for a total visitor. -/
theorem code.step_br.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : U32 × code.BlockType → code.OpIterState → Prop)
    (hread : code.read_br st data ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_BR v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [br_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread ((fun s arg => hvisitor.br v s arg.1 (Control.resultView arg.2)))

private theorem br_if_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_BR_IF v =
      CoreVisitor.run (code.read_br_if st data) (fun v s arg => visitor.on_br_if v s arg.1 (Control.resultView arg.2)) v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lifts a `code.read_br_if` postcondition to `code.step` at `OP_BR_IF` for a total visitor. -/
theorem code.step_br_if.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : U32 × code.BlockType → code.OpIterState → Prop)
    (hread : code.read_br_if st data ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_BR_IF v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [br_if_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread ((fun s arg => hvisitor.brIf v s arg.1 (Control.resultView arg.2)))

private theorem return_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_RETURN v =
      CoreVisitor.run (code.read_return st ctx) (fun v s _ => visitor.on_return v s) v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lifts a `code.read_return` postcondition to `code.step` at `OP_RETURN` for a total visitor. -/
theorem code.step_return.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : Unit → code.OpIterState → Prop)
    (hread : code.read_return st ctx ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_RETURN v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [return_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread ((fun s _ => hvisitor.return_ v s))

private theorem i32_const_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I32_CONST v =
      CoreVisitor.run (code.read_i32_const st data) visitor.on_i32_const v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lifts a `code.read_i32_const` postcondition to `code.step` at `OP_I32_CONST`
for a total visitor. -/
theorem code.step_i32_const.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : I32 → code.OpIterState → Prop)
    (hread : code.read_i32_const st data ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_I32_CONST v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [i32_const_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread (hvisitor.i32Const v)

private theorem drop_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_DROP v =
      CoreVisitor.run (code.read_drop st) visitor.on_drop v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lifts a `code.read_drop` postcondition to `code.step` at `OP_DROP` for a total visitor. -/
theorem code.step_drop.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : code.StackType → code.OpIterState → Prop)
    (hread : code.read_drop st ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_DROP v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [drop_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread (hvisitor.drop v)

private theorem unreachable_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_UNREACHABLE v =
      CoreVisitor.run (code.read_unreachable st) (fun v s _ => visitor.on_unreachable v s) v := by
  simp [global_simps, CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lifts a `code.read_unreachable` postcondition to `code.step` at `OP_UNREACHABLE`
for a total visitor. -/
theorem code.step_unreachable.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : Unit → code.OpIterState → Prop)
    (hread : code.read_unreachable st ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_UNREACHABLE v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [unreachable_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread ((fun s _ => hvisitor.unreachable v s))

private theorem i32_add_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I32_ADD v =
      CoreVisitor.run (code.read_binary st .I32 .I32) (fun v s _ => visitor.on_i32_add v s) v := by
  simp [global_simps, CoreVisitor.run, code.step_numeric, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lifts a `code.read_binary` postcondition to `code.step` at `OP_I32_ADD` for a total visitor. -/
theorem code.step_i32_add.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : Unit → code.OpIterState → Prop)
    (hread : code.read_binary st .I32 .I32 ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_I32_ADD v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [i32_add_dispatch]
  exact CoreVisitor.run.spec _ _ v Q P hread ((fun s _ => hvisitor.i32Add v s))

/-- `code.step` at `OP_NOP` leaves the validator state unchanged for a total visitor, even when the
hook rejects. -/
theorem code.step_nop.total {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (hvisitor : CoreVisitor.Total visitor) :
    code.step visitor st data env ctx code.OP_NOP v ⦃ r => r.2.1 = st ⦄ := by
  obtain ⟨res, v', hr⟩ := hvisitor.nop v st
  cases res with
  | Ok u =>
    rw [WP.spec_equiv_exists]
    exact ⟨(.Ok (), st, v'), by
      simp [hr, code.visit, core.result.Result.Insts.CoreOpsTry.branch], rfl⟩
  | Err e =>
    rw [WP.spec_equiv_exists]
    exact ⟨(.Err (.Visitor e), st, v'), by
      simp [hr, code.visit, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], rfl⟩

end Itasca

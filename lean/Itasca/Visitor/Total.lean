import Itasca.Visitor.Contracts
import Itasca.Support.Translation
import Itasca.Handler.Environment
import Mathlib.Tactic.IntervalCases

/-!
Proofs for Visitor.

This module collects Total, Accepts.
Each section documents its contracts and consumers.
-/

/-! ## Total -/

section

/-! ## Basic -/

section

/-!
# Core visitor steps

`Visitor.Core.Total` states that the hooks of the core instruction subset return normally.
`Visitor.Core.run` models the shape of an extracted `code.step` case, a reader followed by a hook,
and `run.spec` carries a reader postcondition through it. The `code.step_*.of_read` theorems
specialise this to individual opcodes. The core subset is `nop`, `unreachable`, `i32.const`,
`i32.add`, `drop` and the control instructions `block`, `loop`, `if`, `else`, `end`, `br`,
`br_if` and `return`. Covers the scalar step `code.step`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor.Core

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

end Itasca.Visitor.Core

namespace Itasca

private theorem i32_const_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_I32_CONST v =
      Visitor.Core.run (code.read_i32_const st data) visitor.on_i32_const v := by
  simp [global_simps, Visitor.Core.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lifts a `code.read_i32_const` postcondition to `code.step` at `OP_I32_CONST`
for a total visitor. -/
theorem code.step_i32_const.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : I32 → code.OpIterState → Prop)
    (hread : code.read_i32_const st data ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : Visitor.Core.Total visitor) :
    code.step visitor st data env ctx code.OP_I32_CONST v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [i32_const_dispatch]
  exact Visitor.Core.run.spec _ _ v Q P hread (hvisitor.i32Const v)

private theorem drop_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_DROP v =
      Visitor.Core.run (code.read_drop st) visitor.on_drop v := by
  simp [global_simps, Visitor.Core.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lifts a `code.read_drop` postcondition to `code.step` at `OP_DROP` for a total visitor. -/
theorem code.step_drop.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : code.StackType → code.OpIterState → Prop)
    (hread : code.read_drop st ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : Visitor.Core.Total visitor) :
    code.step visitor st data env ctx code.OP_DROP v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [drop_dispatch]
  exact Visitor.Core.run.spec _ _ v Q P hread (hvisitor.drop v)

private theorem unreachable_dispatch {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step visitor st data env ctx code.OP_UNREACHABLE v =
      Visitor.Core.run (code.read_unreachable st) (fun v s _ => visitor.on_unreachable v s) v := by
  simp [global_simps, Visitor.Core.run, core.result.Result.Insts.CoreOpsTry.branch,
    code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext x
  obtain ⟨res, s⟩ := x
  cases res <;> simp
  congr 1

/-- Lifts a `code.read_unreachable` postcondition to `code.step` at `OP_UNREACHABLE`
for a total visitor. -/
theorem code.step_unreachable.of_read {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V)
    (Q : code.OpIterState → Prop) (P : Unit → code.OpIterState → Prop)
    (hread : code.read_unreachable st ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → P a r.2 ⦄)
    (hvisitor : Visitor.Core.Total visitor) :
    code.step visitor st data env ctx code.OP_UNREACHABLE v ⦃ r =>
      Q r.2.1 ∧ (r.1 = .Ok () → ∃ a, P a r.2.1) ⦄ := by
  rw [unreachable_dispatch]
  exact Visitor.Core.run.spec _ _ v Q P hread ((fun s _ => hvisitor.unreachable v s))

/-- `code.step` at `OP_NOP` leaves the validator state unchanged for a total visitor, even when the
hook rejects. -/
theorem code.step_nop.total {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V)
    (hvisitor : Visitor.Core.Total visitor) :
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

end

/-! ## Total -/

section

/-!
# Total visitors

`Visitor.Total` states that every hook of a `code.OpVisitor` returns normally, whether it
accepts or rejects. `Total.to_core` restricts it to `Visitor.Core.Total`, and `Total.visit_numeric`
and `Total.visit_memory` show the numeric and memory dispatch functions return normally. Covers
the hooks of instruction families.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor

/-- The empty visitor is total. -/
theorem empty_total : Total code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor := by
  intro v event
  exact ⟨.Ok (), v, empty_invoke v event⟩

/-- A total visitor is total on the core instruction subset. -/
theorem Total.to_core {V : Type} {visitor : code.OpVisitor V} (h : Total visitor) :
    Visitor.Core.Total visitor :=
  ⟨h.on_nop, h.on_unreachable, h.on_i32_const, h.on_i32_add, h.on_drop,
    h.on_block, h.on_loop, h.on_if, h.on_else, h.on_end, h.on_br, h.on_br_if, h.on_return⟩

set_option maxHeartbeats 4000000 in
/-- `code.visit_numeric` returns normally for a total visitor. -/
theorem Total.visit_numeric {V : Type} {visitor : code.OpVisitor V} (h : Total visitor)
    (v : V) (st : code.OpIterState) (opcode : U8) :
    ∃ res v', code.visit_numeric visitor v st opcode = .ok (res, v') := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n
  case «69» => exact h.on_i32_eqz v st
  case «70» => exact h.on_i32_eq v st
  case «71» => exact h.on_i32_ne v st
  case «72» => exact h.on_i32_lt_s v st
  case «73» => exact h.on_i32_lt_u v st
  case «74» => exact h.on_i32_gt_s v st
  case «75» => exact h.on_i32_gt_u v st
  case «76» => exact h.on_i32_le_s v st
  case «77» => exact h.on_i32_le_u v st
  case «78» => exact h.on_i32_ge_s v st
  case «79» => exact h.on_i32_ge_u v st
  case «80» => exact h.on_i64_eqz v st
  case «81» => exact h.on_i64_eq v st
  case «82» => exact h.on_i64_ne v st
  case «83» => exact h.on_i64_lt_s v st
  case «84» => exact h.on_i64_lt_u v st
  case «85» => exact h.on_i64_gt_s v st
  case «86» => exact h.on_i64_gt_u v st
  case «87» => exact h.on_i64_le_s v st
  case «88» => exact h.on_i64_le_u v st
  case «89» => exact h.on_i64_ge_s v st
  case «90» => exact h.on_i64_ge_u v st
  case «91» => exact h.on_f32_eq v st
  case «92» => exact h.on_f32_ne v st
  case «93» => exact h.on_f32_lt v st
  case «94» => exact h.on_f32_gt v st
  case «95» => exact h.on_f32_le v st
  case «96» => exact h.on_f32_ge v st
  case «97» => exact h.on_f64_eq v st
  case «98» => exact h.on_f64_ne v st
  case «99» => exact h.on_f64_lt v st
  case «100» => exact h.on_f64_gt v st
  case «101» => exact h.on_f64_le v st
  case «102» => exact h.on_f64_ge v st
  case «107» => exact h.on_i32_sub v st
  case «108» => exact h.on_i32_mul v st
  case «109» => exact h.on_i32_div_s v st
  case «110» => exact h.on_i32_div_u v st
  case «111» => exact h.on_i32_rem_s v st
  case «112» => exact h.on_i32_rem_u v st
  case «113» => exact h.on_i32_and v st
  case «114» => exact h.on_i32_or v st
  case «115» => exact h.on_i32_xor v st
  case «116» => exact h.on_i32_shl v st
  case «117» => exact h.on_i32_shr_s v st
  case «118» => exact h.on_i32_shr_u v st
  case «119» => exact h.on_i32_rotl v st
  case «120» => exact h.on_i32_rotr v st
  case «124» => exact h.on_i64_add v st
  case «125» => exact h.on_i64_sub v st
  case «126» => exact h.on_i64_mul v st
  case «127» => exact h.on_i64_div_s v st
  case «128» => exact h.on_i64_div_u v st
  case «129» => exact h.on_i64_rem_s v st
  case «130» => exact h.on_i64_rem_u v st
  case «131» => exact h.on_i64_and v st
  case «132» => exact h.on_i64_or v st
  case «133» => exact h.on_i64_xor v st
  case «134» => exact h.on_i64_shl v st
  case «135» => exact h.on_i64_shr_s v st
  case «136» => exact h.on_i64_shr_u v st
  case «137» => exact h.on_i64_rotl v st
  case «138» => exact h.on_i64_rotr v st
  case «146» => exact h.on_f32_add v st
  case «147» => exact h.on_f32_sub v st
  case «148» => exact h.on_f32_mul v st
  case «149» => exact h.on_f32_div v st
  case «150» => exact h.on_f32_min v st
  case «151» => exact h.on_f32_max v st
  case «152» => exact h.on_f32_copysign v st
  case «160» => exact h.on_f64_add v st
  case «161» => exact h.on_f64_sub v st
  case «162» => exact h.on_f64_mul v st
  case «163» => exact h.on_f64_div v st
  case «164» => exact h.on_f64_min v st
  case «165» => exact h.on_f64_max v st
  case «166» => exact h.on_f64_copysign v st
  case «103» => exact h.on_i32_clz v st
  case «104» => exact h.on_i32_ctz v st
  case «105» => exact h.on_i32_popcnt v st
  case «106» => exact h.on_i32_add v st
  case «121» => exact h.on_i64_clz v st
  case «122» => exact h.on_i64_ctz v st
  case «123» => exact h.on_i64_popcnt v st
  case «139» => exact h.on_f32_abs v st
  case «140» => exact h.on_f32_neg v st
  case «141» => exact h.on_f32_ceil v st
  case «142» => exact h.on_f32_floor v st
  case «143» => exact h.on_f32_trunc v st
  case «144» => exact h.on_f32_nearest v st
  case «145» => exact h.on_f32_sqrt v st
  case «153» => exact h.on_f64_abs v st
  case «154» => exact h.on_f64_neg v st
  case «155» => exact h.on_f64_ceil v st
  case «156» => exact h.on_f64_floor v st
  case «157» => exact h.on_f64_trunc v st
  case «158» => exact h.on_f64_nearest v st
  case «159» => exact h.on_f64_sqrt v st
  case «167» => exact h.on_i32_wrap_i64 v st
  case «168» => exact h.on_i32_trunc_f32_s v st
  case «169» => exact h.on_i32_trunc_f32_u v st
  case «170» => exact h.on_i32_trunc_f64_s v st
  case «171» => exact h.on_i32_trunc_f64_u v st
  case «172» => exact h.on_i64_extend_i32_s v st
  case «173» => exact h.on_i64_extend_i32_u v st
  case «174» => exact h.on_i64_trunc_f32_s v st
  case «175» => exact h.on_i64_trunc_f32_u v st
  case «176» => exact h.on_i64_trunc_f64_s v st
  case «177» => exact h.on_i64_trunc_f64_u v st
  case «178» => exact h.on_f32_convert_i32_s v st
  case «179» => exact h.on_f32_convert_i32_u v st
  case «180» => exact h.on_f32_convert_i64_s v st
  case «181» => exact h.on_f32_convert_i64_u v st
  case «182» => exact h.on_f32_demote_f64 v st
  case «183» => exact h.on_f64_convert_i32_s v st
  case «184» => exact h.on_f64_convert_i32_u v st
  case «185» => exact h.on_f64_convert_i64_s v st
  case «186» => exact h.on_f64_convert_i64_u v st
  case «187» => exact h.on_f64_promote_f32 v st
  case «188» => exact h.on_i32_reinterpret_f32 v st
  case «189» => exact h.on_i64_reinterpret_f64 v st
  case «190» => exact h.on_f32_reinterpret_i32 v st
  case «191» => exact h.on_f64_reinterpret_i64 v st
  all_goals exact ⟨.Ok (), v, rfl⟩

/-- `code.visit_memory` returns normally for a total visitor. -/
theorem Total.visit_memory {V : Type} {visitor : code.OpVisitor V} (h : Total visitor)
    (v : V) (st : code.OpIterState) (opcode : U8) (memarg : code.MemArg) :
    ∃ res v', code.visit_memory visitor v st opcode memarg = .ok (res, v') := by
  unfold code.visit_memory
  split <;> first
  | exact h.on_i32_load v st memarg
  | exact h.on_i64_load v st memarg
  | exact h.on_f32_load v st memarg
  | exact h.on_f64_load v st memarg
  | exact h.on_i32_load8_s v st memarg
  | exact h.on_i32_load8_u v st memarg
  | exact h.on_i32_load16_s v st memarg
  | exact h.on_i32_load16_u v st memarg
  | exact h.on_i64_load8_s v st memarg
  | exact h.on_i64_load8_u v st memarg
  | exact h.on_i64_load16_s v st memarg
  | exact h.on_i64_load16_u v st memarg
  | exact h.on_i64_load32_s v st memarg
  | exact h.on_i64_load32_u v st memarg
  | exact h.on_i32_store v st memarg
  | exact h.on_i64_store v st memarg
  | exact h.on_f32_store v st memarg
  | exact h.on_f64_store v st memarg
  | exact h.on_i32_store8 v st memarg
  | exact h.on_i32_store16 v st memarg
  | exact h.on_i64_store8 v st memarg
  | exact h.on_i64_store16 v st memarg
  | exact h.on_i64_store32 v st memarg
  | exact ⟨.Ok (), v, rfl⟩

end Itasca.Visitor

end

end

/-! ## Accepts -/

section

/-!
# Accepting visitors

`Visitor.Accepts` states that every hook of a `code.OpVisitor` returns normally with `.Ok ()`.
It is the premise under which a visitor leaves validation unchanged. `Accepts.to_total` weakens it
to `Visitor.Total`, and `Accepts.visit_numeric` and `Accepts.visit_memory` cover the numeric
and memory dispatch functions.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor

/-- The empty visitor accepts. -/
theorem empty_accepts : Accepts code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor := by
  intro v event
  exact ⟨v, empty_invoke v event⟩

/-- An accepting visitor is total. -/
theorem Accepts.to_total {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    Total visitor := by
  intro v event
  obtain ⟨next, returned⟩ := h v event
  exact ⟨.Ok (), next, returned⟩

set_option maxHeartbeats 4000000 in
/-- `code.visit_numeric` returns normally and accepts for an accepting visitor. -/
theorem Accepts.visit_numeric {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor)
    (v : V) (st : code.OpIterState) (opcode : U8) :
    ∃ v', code.visit_numeric visitor v st opcode = .ok (.Ok (), v') := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n
  case «69» => exact h.on_i32_eqz v st
  case «70» => exact h.on_i32_eq v st
  case «71» => exact h.on_i32_ne v st
  case «72» => exact h.on_i32_lt_s v st
  case «73» => exact h.on_i32_lt_u v st
  case «74» => exact h.on_i32_gt_s v st
  case «75» => exact h.on_i32_gt_u v st
  case «76» => exact h.on_i32_le_s v st
  case «77» => exact h.on_i32_le_u v st
  case «78» => exact h.on_i32_ge_s v st
  case «79» => exact h.on_i32_ge_u v st
  case «80» => exact h.on_i64_eqz v st
  case «81» => exact h.on_i64_eq v st
  case «82» => exact h.on_i64_ne v st
  case «83» => exact h.on_i64_lt_s v st
  case «84» => exact h.on_i64_lt_u v st
  case «85» => exact h.on_i64_gt_s v st
  case «86» => exact h.on_i64_gt_u v st
  case «87» => exact h.on_i64_le_s v st
  case «88» => exact h.on_i64_le_u v st
  case «89» => exact h.on_i64_ge_s v st
  case «90» => exact h.on_i64_ge_u v st
  case «91» => exact h.on_f32_eq v st
  case «92» => exact h.on_f32_ne v st
  case «93» => exact h.on_f32_lt v st
  case «94» => exact h.on_f32_gt v st
  case «95» => exact h.on_f32_le v st
  case «96» => exact h.on_f32_ge v st
  case «97» => exact h.on_f64_eq v st
  case «98» => exact h.on_f64_ne v st
  case «99» => exact h.on_f64_lt v st
  case «100» => exact h.on_f64_gt v st
  case «101» => exact h.on_f64_le v st
  case «102» => exact h.on_f64_ge v st
  case «107» => exact h.on_i32_sub v st
  case «108» => exact h.on_i32_mul v st
  case «109» => exact h.on_i32_div_s v st
  case «110» => exact h.on_i32_div_u v st
  case «111» => exact h.on_i32_rem_s v st
  case «112» => exact h.on_i32_rem_u v st
  case «113» => exact h.on_i32_and v st
  case «114» => exact h.on_i32_or v st
  case «115» => exact h.on_i32_xor v st
  case «116» => exact h.on_i32_shl v st
  case «117» => exact h.on_i32_shr_s v st
  case «118» => exact h.on_i32_shr_u v st
  case «119» => exact h.on_i32_rotl v st
  case «120» => exact h.on_i32_rotr v st
  case «124» => exact h.on_i64_add v st
  case «125» => exact h.on_i64_sub v st
  case «126» => exact h.on_i64_mul v st
  case «127» => exact h.on_i64_div_s v st
  case «128» => exact h.on_i64_div_u v st
  case «129» => exact h.on_i64_rem_s v st
  case «130» => exact h.on_i64_rem_u v st
  case «131» => exact h.on_i64_and v st
  case «132» => exact h.on_i64_or v st
  case «133» => exact h.on_i64_xor v st
  case «134» => exact h.on_i64_shl v st
  case «135» => exact h.on_i64_shr_s v st
  case «136» => exact h.on_i64_shr_u v st
  case «137» => exact h.on_i64_rotl v st
  case «138» => exact h.on_i64_rotr v st
  case «146» => exact h.on_f32_add v st
  case «147» => exact h.on_f32_sub v st
  case «148» => exact h.on_f32_mul v st
  case «149» => exact h.on_f32_div v st
  case «150» => exact h.on_f32_min v st
  case «151» => exact h.on_f32_max v st
  case «152» => exact h.on_f32_copysign v st
  case «160» => exact h.on_f64_add v st
  case «161» => exact h.on_f64_sub v st
  case «162» => exact h.on_f64_mul v st
  case «163» => exact h.on_f64_div v st
  case «164» => exact h.on_f64_min v st
  case «165» => exact h.on_f64_max v st
  case «166» => exact h.on_f64_copysign v st
  case «103» => exact h.on_i32_clz v st
  case «104» => exact h.on_i32_ctz v st
  case «105» => exact h.on_i32_popcnt v st
  case «106» => exact h.on_i32_add v st
  case «121» => exact h.on_i64_clz v st
  case «122» => exact h.on_i64_ctz v st
  case «123» => exact h.on_i64_popcnt v st
  case «139» => exact h.on_f32_abs v st
  case «140» => exact h.on_f32_neg v st
  case «141» => exact h.on_f32_ceil v st
  case «142» => exact h.on_f32_floor v st
  case «143» => exact h.on_f32_trunc v st
  case «144» => exact h.on_f32_nearest v st
  case «145» => exact h.on_f32_sqrt v st
  case «153» => exact h.on_f64_abs v st
  case «154» => exact h.on_f64_neg v st
  case «155» => exact h.on_f64_ceil v st
  case «156» => exact h.on_f64_floor v st
  case «157» => exact h.on_f64_trunc v st
  case «158» => exact h.on_f64_nearest v st
  case «159» => exact h.on_f64_sqrt v st
  case «167» => exact h.on_i32_wrap_i64 v st
  case «168» => exact h.on_i32_trunc_f32_s v st
  case «169» => exact h.on_i32_trunc_f32_u v st
  case «170» => exact h.on_i32_trunc_f64_s v st
  case «171» => exact h.on_i32_trunc_f64_u v st
  case «172» => exact h.on_i64_extend_i32_s v st
  case «173» => exact h.on_i64_extend_i32_u v st
  case «174» => exact h.on_i64_trunc_f32_s v st
  case «175» => exact h.on_i64_trunc_f32_u v st
  case «176» => exact h.on_i64_trunc_f64_s v st
  case «177» => exact h.on_i64_trunc_f64_u v st
  case «178» => exact h.on_f32_convert_i32_s v st
  case «179» => exact h.on_f32_convert_i32_u v st
  case «180» => exact h.on_f32_convert_i64_s v st
  case «181» => exact h.on_f32_convert_i64_u v st
  case «182» => exact h.on_f32_demote_f64 v st
  case «183» => exact h.on_f64_convert_i32_s v st
  case «184» => exact h.on_f64_convert_i32_u v st
  case «185» => exact h.on_f64_convert_i64_s v st
  case «186» => exact h.on_f64_convert_i64_u v st
  case «187» => exact h.on_f64_promote_f32 v st
  case «188» => exact h.on_i32_reinterpret_f32 v st
  case «189» => exact h.on_i64_reinterpret_f64 v st
  case «190» => exact h.on_f32_reinterpret_i32 v st
  case «191» => exact h.on_f64_reinterpret_i64 v st
  all_goals exact ⟨v, rfl⟩

/-- `code.visit_memory` returns normally and accepts for an accepting visitor. -/
theorem Accepts.visit_memory {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor)
    (v : V) (st : code.OpIterState) (opcode : U8) (memarg : code.MemArg) :
    ∃ v', code.visit_memory visitor v st opcode memarg = .ok (.Ok (), v') := by
  unfold code.visit_memory
  split <;> first
  | exact h.on_i32_load v st memarg
  | exact h.on_i64_load v st memarg
  | exact h.on_f32_load v st memarg
  | exact h.on_f64_load v st memarg
  | exact h.on_i32_load8_s v st memarg
  | exact h.on_i32_load8_u v st memarg
  | exact h.on_i32_load16_s v st memarg
  | exact h.on_i32_load16_u v st memarg
  | exact h.on_i64_load8_s v st memarg
  | exact h.on_i64_load8_u v st memarg
  | exact h.on_i64_load16_s v st memarg
  | exact h.on_i64_load16_u v st memarg
  | exact h.on_i64_load32_s v st memarg
  | exact h.on_i64_load32_u v st memarg
  | exact h.on_i32_store v st memarg
  | exact h.on_i64_store v st memarg
  | exact h.on_f32_store v st memarg
  | exact h.on_f64_store v st memarg
  | exact h.on_i32_store8 v st memarg
  | exact h.on_i32_store16 v st memarg
  | exact h.on_i64_store8 v st memarg
  | exact h.on_i64_store16 v st memarg
  | exact h.on_i64_store32 v st memarg
  | exact ⟨v, rfl⟩

end Itasca.Visitor

end

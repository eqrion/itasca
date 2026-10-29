import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupPreservation
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

private theorem emit_paid {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status,after)) :
    status = .Ok () → after.function.code.val.length = before.function.code.val.length + 1 := by
  intro same; subst status
  simp [compiler_emit_code_success ops law before after instruction accepted]

open Lean Meta Elab Tactic in
elab "paid_fixup_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  evalTactic (← `(tactic| fixup_effect $h using $ops, $law))
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | return
  if lhs.getAppFn.constName? == some ``runtime.compiler.FunctionCompiler.emit then
    evalTactic (← `(tactic| have paid := emit_paid $ops $law _ _ _ _ $h))

macro "paid_fixup_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; fixup_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | (sources_nonterminal $h
     obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try paid_fixup_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | sources_split $h)

theorem compiler_branch_fixup_budget {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (), after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  have growth := compiler_branch_code_mono ops law before after depth skip conditional (.Ok ()) accepted
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch, Bool.false_eq_true, ite_false, ite_true] at accepted
  all_goals repeat' paid_fixup_step accepted using ops, law
  all_goals try paid_fixup_effect accepted using ops, law
  all_goals fixup_close
  all_goals try exact budget.mono (by omega)
  all_goals
    apply (budget.mono (by omega)).set
    have selectedBudget := budget _ (by assumption)
    dsimp only
    try simp_all only [List.length_append, List.length_singleton]
    omega


end Itasca.Runtime.Compiler

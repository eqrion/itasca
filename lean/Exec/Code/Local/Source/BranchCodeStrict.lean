import Exec.Code.Local.Callbacks.Common.CompilerCodeMonotoneTactic
import Exec.Code.Local.Relations.Control.BranchSuccessEmit

namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- A successful actual emission extends the instruction vector strictly. -/
theorem compiler_emit_code_strict_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status,after)) :
    status = .Ok () → before.function.code.val.length < after.function.code.val.length := by
  intro success
  subst status
  obtain ⟨budget,code,sources,rfl,appended,_⟩ := compiler_emit_success ops law before after instruction called
  simp only [appended,List.length_append,List.length_singleton]
  omega

open Lean Meta Elab Tactic in
elab "strict_code_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_,lhs,_) := ty.eq? | throwError "not an equation"
  if lhs.getAppFn.constName? = some ``runtime.compiler.FunctionCompiler.emit then
    evalTactic (← `(tactic| have strictGrowth := compiler_emit_code_strict_result $ops $law _ _ _ _ $h))
  evalTactic (← `(tactic| code_mono_effect $h using $ops, $law))

macro "strict_code_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; code_mono_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (strict_code_effect $h using $ops, $law; code_mono_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; code_mono_close)
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
     try strict_code_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | sources_split $h)


/-- A successful actual branch always emits at least one control instruction,
including loop targets and copies elided by the compiler. -/
theorem compiler_branch_code_strict {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (),after)) :
    before.function.code.val.length < after.function.code.val.length := by
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch,Bool.false_eq_true,ite_false,ite_true] at called <;>
    repeat' strict_code_step called using ops, law

end Exec.Code

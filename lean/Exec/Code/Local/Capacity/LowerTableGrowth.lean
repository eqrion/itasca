import Exec.Code.Local.Capacity.TableGrowth
import Exec.Code.Local.Relations.Table.TableDepths
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open Lean Meta Elab Tactic in
elab "growth_table_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  if lhs.getAppFn.constName? = some ``runtime.compiler.control.FunctionCompiler.lower_table_branches_loop then
    evalTactic (← `(tactic| have effect := compiler_table_loop_growth $ops $law _ _ _ _ $h))
    evalTactic (← `(tactic| obtain ⟨depthsEq, growth⟩ := effect))
  else
    evalTactic (← `(tactic| growth_control_effect $h using $ops, $law))
    if lhs.getAppFn.constName? = some ``runtime.compiler.FunctionCompiler.emit then
      evalTactic (← `(tactic| have depthsEq := compiler_emit_depths $ops _ _ _ _ $h))

macro "growth_table_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (growth_table_effect $h using $ops, $law; growth_close)
  | solve | (simp only [Result.ok.injEq, Prod.mk.injEq] at $h:ident; obtain ⟨_, output⟩ := $h; cases output; growth_close)
  | (obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try growth_table_effect called using $ops, $law
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | split at $h:ident)

end Exec.Code

import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTablePreservation
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Lean Meta Elab Tactic in
elab "indirect_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.compiler.FunctionCompiler.observe =>
      `(tactic| have effect := compiler_observe_indirect $ops $law _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| have effect := compiler_emit_indirect $ops _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| have effect := compiler_copy_indirect $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.lower.FunctionCompiler.finish_op =>
      `(tactic| have effect := compiler_finish_op_indirect $ops $law _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pc => do
      let theoremName := mkIdent `Itasca.Runtime.Code.compiler_pc_indirect
      `(tactic| have effect := $theoremName $ops _ _ _ $h)
    | ``runtime.compiler.control.FunctionCompiler.patch => do
      let theoremName := mkIdent `Itasca.Runtime.Code.compiler_patch_indirect
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 => do
      let theoremName := mkIdent `Itasca.Runtime.Code.compiler_fixups_indirect
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1 => do
      let theoremName := mkIdent `Itasca.Runtime.Code.compiler_fixups_after_if_indirect
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | _ => throwError "not a compiler helper"
  evalTactic tac


macro "indirect_close" : tactic => `(tactic|
  (first | rfl | (simp_all [snapshotCompiler, source_unit_eq]; try omega)))
macro "indirect_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; indirect_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (indirect_effect $h using $ops, $law; indirect_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; indirect_close)
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
     try indirect_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | sources_split $h)


end Itasca.Runtime.Code

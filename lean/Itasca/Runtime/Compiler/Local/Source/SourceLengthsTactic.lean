import Itasca.Runtime.Compiler.Local.Source.SourceLengths
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Tactic.Rename
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Lean Meta Elab Tactic in
elab "sources_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.compiler.FunctionCompiler.observe =>
      `(tactic| have effect := compiler_observe_sources $ops $law _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| have effect := compiler_emit_sources_result $ops $law _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| have effect := compiler_copy_sources_result $ops $law _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pair =>
      `(tactic| have effect := compiler_pair_sources $ops _ _ _ _ _ $h)
    | ``runtime.compiler.lower.FunctionCompiler.finish_op =>
      `(tactic| have effect := compiler_finish_op_sources_result $ops $law _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pc => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_pc_sources
      `(tactic| have effect := $theoremName $ops _ _ _ $h)
    | ``runtime.compiler.control.FunctionCompiler.patch => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_patch_sources
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_fixups_sources
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1 => do
      let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_fixups_after_if_sources
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | _ => throwError "not a compiler helper"
  evalTactic tac

theorem source_unit_eq (value : Unit) : value = () := Subsingleton.elim _ _

macro "sources_close" : tactic => `(tactic|
  (first | rfl | (simp_all [SourceProgress, snapshotCompiler, source_unit_eq]; try omega)))

open Lean Meta Elab Tactic in
elab "sources_nonterminal " h:ident : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  unless lhs.isAppOf ``Aeneas.Std.bind do throwError "not a bind equation"

open Lean Meta Elab Tactic in
elab "sources_terminal " h:ident : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  unless lhs.isAppOf ``Result.ok do throwError "nonterminal equation"

open Lean Meta Elab Tactic in
elab "sources_split " h:ident : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some matcherName := lhs.getAppFn.constName? | throwError "not a matcher"
  unless matcherName == ``ite || matcherName == ``dite || (← isMatcher matcherName) do
    throwError "not a matcher"
  evalTactic (← `(tactic| split at $h:ident))

macro "sources_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; sources_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (sources_effect $h using $ops, $law; sources_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; sources_close)
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
     try sources_effect called using $ops, $law
     try clear called
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | sources_split $h)

end Itasca.Runtime.Compiler

import Exec.Code.Local.Coordinates.SourceCoordinateCallbacks
import Exec.Code.Local.Source.SourceCursorTactic
import Exec.Code.Local.Callbacks.Common.CompilerMetadataTactic

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

macro "coordinates_close" : tactic => `(tactic|
  (first | assumption | (simp_all [SourceCoordinates,compilerOrdinaryMetadata,compilerMetadata,
    snapshotCompiler,Prod.mk.injEq,source_unit_eq]; try omega)))

/- Reduce only the outer parser match. Traversing every inactive branch of
an extracted opcode dispatcher is both unnecessary and expensive. The local
declaration change is checked for definitional equality. -/
open Lean Meta Elab Tactic in
elab "coordinates_head " h:ident : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, rhs) := ty.eq? | throwError "not an equation"
  let reduced ← whnfCore lhs
  if reduced == lhs then throwError "already in head normal form"
  let next ← (← getMainGoal).changeLocalDecl hyp.fvarId! (← mkEq reduced rhs)
  replaceMainGoal [next]

open Lean Meta Elab Tactic in
elab "coordinates_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.compiler.FunctionCompiler.observe =>
      `(tactic| have coordinates := compiler_observe_source_coordinates_result $ops $law _ _ _ _
        $h (by coordinates_close) (by coordinates_close))
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| have coordinates := compiler_emit_source_coordinates_result $ops $law _ _ _ _
        $h (by coordinates_close) (by coordinates_close))
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| have coordinates := compiler_copy_source_coordinates_result $ops $law _ _ _ _ _ _
        $h (by coordinates_close) (by coordinates_close))
    | ``runtime.compiler.lower.FunctionCompiler.finish_op =>
      `(tactic| have coordinates := compiler_finish_op_source_coordinates_result $ops $law _ _ _ _ _
        $h (by coordinates_close) (by coordinates_close) (by coordinates_close))
    | ``runtime.compiler.FunctionCompiler.pair =>
      `(tactic| have coordinates := compiler_pair_source_coordinates $ops _ _ _ _ _ $h (by coordinates_close))
    | ``runtime.compiler.FunctionCompiler.pc =>
      `(tactic| have coordinates := compiler_pc_source_coordinates $ops _ _ _ $h (by coordinates_close))
    | ``runtime.compiler.control.FunctionCompiler.patch =>
      `(tactic| have coordinates := compiler_patch_source_coordinates $ops _ _ _ _ _ $h (by coordinates_close))
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop0 =>
      `(tactic| have coordinates := compiler_fixups_source_coordinates $ops _ _ _ _ _ _ $h (by coordinates_close))
    | ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end_loop1 =>
      `(tactic| have coordinates := compiler_fixups_after_if_source_coordinates $ops _ _ _ _ _ _ $h (by coordinates_close))
    | _ => throwError "not a compiler helper"
  evalTactic tac
  evalTactic (← `(tactic| try metadata_effect $h using $ops, $law))
  evalTactic (← `(tactic| try cursor_effect $h using $ops, $law))

macro "coordinates_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; coordinates_close)
  | coordinates_head $h
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (coordinates_effect $h using $ops, $law; coordinates_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; coordinates_close)
  | (fail_if_no_progress simp only [Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame,bind_ok,bind_tc_ok] at $h:ident)
  | (sources_nonterminal $h
     obtain ⟨value,called,rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue,secondValue⟩)
     | skip
     try coordinates_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | sources_split $h)

end Itasca.Runtime.Code

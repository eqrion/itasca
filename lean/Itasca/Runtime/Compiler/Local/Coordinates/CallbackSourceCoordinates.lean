import Itasca.Runtime.Compiler.Local.Coordinates.ControlSourceCoordinates
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerBranchMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackCursor

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem compiler_branch_source_coordinates_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status,after))
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val) :
    status = .Ok () → SourceCoordinates after := by
  intro accepted
  subst status
  exact compiler_branch_source_coordinates ops law before after depth skip conditional held inside called

open Lean Meta Elab Tactic in
elab "control_coordinates_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  if lhs.getAppFn.constName? = some ``runtime.compiler.control.FunctionCompiler.branch then
    evalTactic (← `(tactic| have coordinates := compiler_branch_source_coordinates_result $ops $law _ _ _ _ _ _ $h
      (by coordinates_close) (by coordinates_close)))
    evalTactic (← `(tactic| have cursor := compiler_branch_cursor_result $ops $law _ _ _ _ _ _ $h))
    evalTactic (← `(tactic| have stable := compiler_branch_stable_result $ops $law _ _ _ _ _ _ $h))
    evalTactic (← `(tactic| have metadataEq := stable.metadata))
  else
    evalTactic (← `(tactic| coordinates_effect $h using $ops, $law))

macro "control_coordinates_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; coordinates_close)
  | coordinates_head $h
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (control_coordinates_effect $h using $ops, $law; coordinates_close)
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
     try control_coordinates_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | sources_split $h)

/-- The actual unreachable callback retains source-coordinate publication bounds. -/
theorem compiler_unreachable_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
      ops before state = .ok (.Ok (),after)) : SourceCoordinates after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable at called
  repeat' control_coordinates_step called using ops, law

/-- The actual return callback retains source-coordinate publication bounds. -/
theorem compiler_return_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (.Ok (),after)) : SourceCoordinates after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return at called
  repeat' control_coordinates_step called using ops, law

/-- The actual br callback retains source-coordinate publication bounds. -/
theorem compiler_br_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (resultType : Itasca.signature.ResultType)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth resultType = .ok (.Ok (),after)) : SourceCoordinates after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at called
  repeat' control_coordinates_step called using ops, law

/-- The actual br_if callback retains source-coordinate publication bounds. -/
theorem compiler_br_if_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (resultType : Itasca.signature.ResultType)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth resultType = .ok (.Ok (),after)) : SourceCoordinates after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at called
  repeat' control_coordinates_step called using ops, law

end Itasca.Runtime.Compiler

import Exec.Code.Local.Source.SourceLengthsTactic
import Exec.Code.Local.Callbacks.Common.ObserveFrame
import Exec.Code.Local.Relations.Common.ObservationLayout
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem compiler_emit_branch_height {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    after.height = before.height := by
  unfold runtime.compiler.FunctionCompiler.emit at accepted
  obtain ⟨⟨pc, current⟩, called, rest⟩ := bind_ok_inv _ _ _ accepted
  have effect := compiler_pc ops before
  rw [called, WP.spec_ok] at effect
  obtain ⟨_, _, budget, currentEq⟩ := effect
  change current = {before with budget} at currentEq
  subst current
  cases pc with
  | Err error => 
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, output⟩ := rest
      subst after
      rfl
  | Ok value =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨charged, budget1⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
    cases charged with
    | Err error => 
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, output⟩ := rest
        subst after
        rfl
    | Ok value =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨pushed, budget2, code⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
      cases pushed with
      | Err error => 
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
          obtain ⟨_, output⟩ := rest
          subst after
          rfl
      | Ok value =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨coordinate, _, rest⟩ := bind_ok_inv _ _ _ rest
        obtain ⟨⟨result, budget3, sources⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
        simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, output⟩ := rest
        subst after
        rfl

theorem compiler_copy_branch_height {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (dst src count : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (status, after)) :
    after.height = before.height := by
  unfold runtime.compiler.FunctionCompiler.copy at accepted
  split at accepted
  · have same : before = after := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
    subst after
    rfl
  · split at accepted
    · have same : before = after := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
      subst after
      rfl
    · obtain ⟨instruction, _, emitted⟩ := bind_ok_inv _ _ _ accepted
      exact compiler_emit_branch_height ops before after instruction status emitted

theorem compiler_pc_branch_height {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) :
    after.height = before.height := by
  have effect := compiler_pc ops before
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨_, _, budget, same⟩ := effect
  exact congrArg (fun c => c.height) same
/-- Patching only replaces an instruction; all function and control metadata
survive every normal return, including a rejected patch site. -/
theorem compiler_patch_branch_height {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    after.height = before.height := by
  rcases compiler_patch_cases ops before after pc target status accepted with rfl | ⟨_, _, rfl, _⟩ <;>
    rfl



open Lean Meta Elab Tactic in
elab "branch_height_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| have effect := compiler_emit_branch_height $ops _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| have effect := compiler_copy_branch_height $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pc => do
      let theoremName := mkIdent `Exec.Code.compiler_pc_branch_height
      `(tactic| have effect := $theoremName $ops _ _ _ $h)
    | ``runtime.compiler.control.FunctionCompiler.patch => do
      let theoremName := mkIdent `Exec.Code.compiler_patch_branch_height
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ $h)
    | _ => throwError "not a compiler helper"
  evalTactic tac


macro "branch_height_close" : tactic => `(tactic|
  (first | rfl | (simp_all [snapshotCompiler, source_unit_eq]; try omega)))
macro "branch_height_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; branch_height_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (branch_height_effect $h using $ops, $law; branch_height_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; branch_height_close)
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
     try branch_height_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | sources_split $h)




theorem compiler_branch_height_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    after.height = before.height := by
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch, Bool.false_eq_true, ite_false, ite_true] at accepted <;>
    repeat' branch_height_step accepted using ops, law

end Exec.Code

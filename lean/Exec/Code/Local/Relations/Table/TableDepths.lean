import Exec.Code.Local.Callbacks.Common.CompilerOrdinaryResults
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Tactic.Rename
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem compiler_emit_depths {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    after.table_depths = before.table_depths := by
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

theorem compiler_copy_depths {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (dst src count : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (status, after)) :
    after.table_depths = before.table_depths := by
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
      exact compiler_emit_depths ops before after instruction status emitted

theorem compiler_pc_depths {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) :
    after.table_depths = before.table_depths := by
  have effect := compiler_pc ops before
  rw [accepted, WP.spec_ok] at effect
  obtain ⟨_, _, budget, same⟩ := effect
  exact congrArg (fun c => c.table_depths) same
/-- Patching only replaces an instruction; all function and control metadata
survive every normal return, including a rejected patch site. -/
theorem compiler_patch_depths {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    after.table_depths = before.table_depths := by
  rcases compiler_patch_cases ops before after pc target status accepted with rfl | ⟨_, _, rfl, _⟩ <;>
    rfl


open Lean Meta Elab Tactic in
elab "depths_effect " h:ident " using " ops:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  let some functionName := lhs.getAppFn.constName? | throwError "not a named helper"
  let tac ← match functionName with
    | ``runtime.compiler.FunctionCompiler.emit =>
      `(tactic| have effect := compiler_emit_depths $ops _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.copy =>
      `(tactic| have effect := compiler_copy_depths $ops _ _ _ _ _ _ $h)
    | ``runtime.compiler.FunctionCompiler.pc =>
      `(tactic| have effect := compiler_pc_depths $ops _ _ _ $h)
    | ``runtime.compiler.control.FunctionCompiler.patch =>
      `(tactic| have effect := compiler_patch_depths $ops _ _ _ _ _ $h)
    | ``runtime.compiler.control.FunctionCompiler.branch => do
      let theoremName := mkIdent `Exec.Code.compiler_branch_depths
      `(tactic| have effect := $theoremName $ops _ _ _ _ _ _ $h)
    | _ => throwError "not a compiler helper"
  evalTactic tac

macro "depths_close" : tactic => `(tactic| first | rfl | simp_all only [Prod.mk.injEq])
macro "depths_step " h:ident " using " ops:term : tactic => `(tactic|
  first
  | solve | (depths_effect $h using $ops; depths_close)
  | solve | (simp only [Result.ok.injEq, Prod.mk.injEq] at $h:ident; obtain ⟨_, output⟩ := $h; cases output; depths_close)
  | (obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try depths_effect called using $ops
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | split at $h:ident)

theorem compiler_branch_depths {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    after.table_depths = before.table_depths := by
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch, Bool.false_eq_true, ite_false, ite_true] at accepted <;>
    repeat' depths_step accepted using ops

theorem compiler_table_branch_depths {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (index : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (status, after)) :
    after.table_depths = before.table_depths := by
  unfold runtime.compiler.control.FunctionCompiler.table_branch at accepted
  repeat' depths_step accepted using ops
end Exec.Code

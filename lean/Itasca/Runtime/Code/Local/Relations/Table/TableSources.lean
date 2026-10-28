import Itasca.Runtime.Code.Local.Callbacks.Calls.CallbackSources
import Itasca.Runtime.Code.Local.Relations.Table.TableDepths
import Itasca.Runtime.Code.Local.Source.SourceStartFrame
import Itasca.Runtime.Code.Local.Source.SourceCursor
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
def snapshotStatus {A : Type} (output : CompilerSnapshot A) :
    core.result.Result Unit Itasca.error.VisitError :=
  let (_, _, _, _, _, _, _, _, _, _, _, _, result) := output
  result

theorem compiler_table_branch_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (), after)) :
    SourceProgress before after := by
  unfold runtime.compiler.control.FunctionCompiler.table_branch at accepted
  repeat' control_sources_step accepted using ops, law

theorem compiler_table_loop_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches_loop
      ops before index status = .ok output) :
    snapshotStatus output = .Ok () →
      status = .Ok () ∧ SourceProgress before (snapshotCompiler output) := by
  intro successful
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index status with
  | h n ih =>
    unfold runtime.compiler.control.FunctionCompiler.lower_table_branches_loop at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.body,
      bind_ok] at accepted
    split at accepted
    · rename_i inside
      have indexBound : index.val < before.table_depths.val.length := by scalar_tac
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        simp [snapshotStatus] at successful
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨⟨result, middle⟩, patched, tail⟩ := bind_ok_inv _ _ _ accepted
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.control.FunctionCompiler.lower_table_branches_loop
            ops middle nextIndex result = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.control.FunctionCompiler.lower_table_branches_loop,
            runtime.compiler.control.FunctionCompiler.lower_table_branches_loop.body,
            core.result.Result.is_ok] using tail
        obtain ⟨resultOk, restSources⟩ := ih _ smaller middle nextIndex result tail' rfl
        subst result
        exact ⟨rfl, (compiler_table_branch_sources ops law before middle index patched).trans restSources⟩
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      exact ⟨successful, SourceProgress.refl _⟩

open Lean Meta Elab Tactic in
elab "table_sources_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  if lhs.getAppFn.constName? = some ``runtime.compiler.control.FunctionCompiler.lower_table_branches_loop then
    evalTactic (← `(tactic| have effect := compiler_table_loop_sources $ops $law _ _ _ _ $h))
  else
    evalTactic (← `(tactic| control_sources_effect $h using $ops, $law))

macro "table_sources_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; sources_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (table_sources_effect $h using $ops, $law; sources_close)
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
     try table_sources_effect called using $ops, $law
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

theorem compiler_lower_table_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (), after)) :
    SourceProgress before after := by
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches at accepted
  repeat' table_sources_step accepted using ops, law
  rename_i middle unit emitted signatures tail loopEffect
  have result := (Prod.mk.inj (Result.ok.injEq.mp accepted)).1
  have result' : snapshotStatus (signatures, tail) = .Ok () := result
  have finalSource := (loopEffect result').2
  have same := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
  change snapshotCompiler (signatures, tail) = after at same
  rw [same] at finalSource
  exact (emitted (by cases unit; rfl)).trans finalSource
theorem compiler_table_label_source_frame {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (status, after)) :
    SourceStartFrame before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label at accepted
  obtain ⟨⟨result, budget⟩, _, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    obtain ⟨_, output⟩ := rest
    subst after
    rfl
  | Ok value =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨result, budget, depths⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
    simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at rest
    obtain ⟨_, output⟩ := rest
    subst after
    rfl

theorem compiler_br_table_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (default : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state default types = .ok (.Ok (), after)) :
    SourceProgress before after ∧ after.next_source = state.pos := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at accepted
  obtain ⟨⟨result, labeled⟩, labelCalled, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    cases value
    have labeledSources := (compiler_table_label_source_frame ops before labeled state default (.Ok ()) labelCalled).sources
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    split at rest
    · obtain ⟨⟨result, lowered⟩, lowerCalled, rest⟩ := bind_ok_inv _ _ _ rest
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok value =>
        cases value
        have loweredSources := compiler_lower_table_sources ops law labeled lowered lowerCalled
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨cleared, _, observed⟩ := bind_ok_inv _ _ _ rest
        have finalSources := compiler_observe_sources ops law {lowered with reachable := false, table_depths := cleared}
          after state (.Ok ()) observed
        have cursor := compiler_observe_cursor ops law {lowered with reachable := false, table_depths := cleared}
          after state (.Ok ()) observed rfl
        exact ⟨labeledSources.trans (loweredSources.trans finalSources), cursor⟩
    · obtain ⟨cleared, _, observed⟩ := bind_ok_inv _ _ _ rest
      have finalSources := compiler_observe_sources ops law {labeled with table_depths := cleared}
        after state (.Ok ()) observed
      have cursor := compiler_observe_cursor ops law {labeled with table_depths := cleared}
        after state (.Ok ()) observed rfl
      exact ⟨labeledSources.trans finalSources, cursor⟩

end Itasca.Runtime.Code


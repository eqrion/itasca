import Exec.Code.Local.Source.SourceLengthsTactic
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Function entry and local declarations preserve the scheduler signature tables and batch origin. -/
def FunctionEnvironment {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  (after.signatures, after.func_param_slots, after.batch_start) =
    (before.signatures, before.func_param_slots, before.batch_start)

theorem FunctionEnvironment.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : FunctionEnvironment before middle) (second : FunctionEnvironment middle after) :
    FunctionEnvironment before after := Eq.trans second first

open Lean Meta Elab Tactic in
elab "environment_frame_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  if lhs.getAppFn.constName? = some ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop then
    let theoremName := mkIdent `Exec.Code.compiler_locals_environment_frame
    evalTactic (← `(tactic| have effect := $theoremName $ops $law _ _ _ _ _ $h))
  else
    throwError "not local declaration loop"

macro "environment_frame_close" : tactic => `(tactic|
  (first | rfl | (simp_all [FunctionEnvironment, snapshotCompiler, source_unit_eq])))
macro "environment_frame_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; environment_frame_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (environment_frame_effect $h using $ops, $law; environment_frame_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; environment_frame_close)
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
     try environment_frame_effect called using $ops, $law
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

theorem compiler_add_local_environment_frame {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (ty : Itasca.types.ValueType) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.add_local ops before ty = .ok (status, after)) :
    FunctionEnvironment before after := by
  unfold runtime.compiler.FunctionCompiler.add_local at accepted
  repeat' environment_frame_step accepted using ops, law
theorem compiler_locals_environment_frame {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (ctx : Itasca.code.Context) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop
      ops before ctx index status = .ok output) :
    FunctionEnvironment before (snapshotCompiler output) := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index status with
  | h n ih =>
    unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop.body,
      bind_ok] at accepted
    split at accepted
    · cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        rfl
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨site, _, rest⟩ := bind_ok_inv _ _ _ accepted
        obtain ⟨⟨result, middle⟩, patched, tail⟩ := bind_ok_inv _ _ _ rest
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop
            ops middle ctx nextIndex result = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop,
            runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop.body,
            core.result.Result.is_ok] using tail
        exact (compiler_add_local_environment_frame ops law before middle site result patched).trans
          (ih _ smaller middle nextIndex result tail' rfl)
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      rfl


theorem compiler_function_start_environment_frame {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (start finish : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops before ctx typeIndex start finish = .ok (status, after)) :
    FunctionEnvironment before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start at accepted
  repeat' environment_frame_step accepted using ops, law

end Exec.Code

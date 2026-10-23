import Exec.Code.Local.Callbacks.Common.CompilerOrdinaryResults
import Exec.Code.Local.Initializer.InitializerExpression
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
theorem compiler_emit_code_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (.Ok (), after)) :
    after.function.code.val = before.function.code.val ++ [instruction] := by
  unfold runtime.compiler.FunctionCompiler.emit at accepted
  obtain ⟨⟨pc, current⟩, called, rest⟩ := bind_ok_inv _ _ _ accepted
  have effect := compiler_pc ops before
  rw [called, WP.spec_ok] at effect
  obtain ⟨_, _, budget, currentEq⟩ := effect
  change current = {before with budget} at currentEq
  subst current
  cases pc with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨charged, budget1⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
    cases charged with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok value =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨pushed, budget2, code⟩, pushedEq, rest⟩ := bind_ok_inv _ _ _ rest
      cases pushed with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok value =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨coordinate, _, rest⟩ := bind_ok_inv _ _ _ rest
        obtain ⟨⟨result, budget3, sources⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
        simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, output⟩ := rest
        subst after
        exact (budget_push_success ops law budget1 budget2 before.function.code code instruction pushedEq).2

/-- Every normal checked append either keeps the vector or appends its value. -/
theorem budget_push_code_result {A T : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget afterBudget : runtime.compiler.Budget A)
    (before after : alloc.vec.Vec T) (value : T)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.Budget.push ops budget before value = .ok (status, afterBudget, after)) :
    after.val = before.val ∨ after.val = before.val ++ [value] := by
  obtain ⟨answer, reserve⟩ := law.reserve_eq before 1#usize
  unfold runtime.compiler.Budget.push at accepted
  rw [reserve, bind_ok] at accepted
  cases answer with
  | false =>
    simp only [uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte, runtime.compiler.Budget.reject,
      bind_ok, Result.ok.injEq, Prod.mk.injEq] at accepted
    exact Or.inl (congrArg (fun v : alloc.vec.Vec T => v.val) accepted.2.2).symm
  | true =>
    simp only [uncurry_apply_pair, ↓reduceIte, alloc.vec.Vec.push] at accepted
    split at accepted
    · simp only [bind_ok, Result.ok.injEq, Prod.mk.injEq] at accepted
      apply Or.inr
      simpa only [alloc.vec.Vec.from_val, List.concat_eq_append] using
        (congrArg (fun v : alloc.vec.Vec T => v.val) accepted.2.2).symm
    · simp only [bind_fail, fail_not_ok] at accepted

theorem compiler_emit_growth {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status, after)) :
    after.function.code.val.length ≤ before.function.code.val.length + 1 := by
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
      simp only; omega
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
        simp only; omega
    | Ok value =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨pushed, budget2, code⟩, pushedEq, rest⟩ := bind_ok_inv _ _ _ rest
      have growth := budget_push_code_result ops law budget1 budget2 before.function.code code instruction pushed pushedEq
      cases pushed with
      | Err error => 
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
          obtain ⟨_, output⟩ := rest
          subst after
          rcases growth with kept | appended <;> simp_all only [List.length_append, List.length_singleton, Nat.le_refl] <;> omega
      | Ok value =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨coordinate, _, rest⟩ := bind_ok_inv _ _ _ rest
        obtain ⟨⟨result, budget3, sources⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
        simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, output⟩ := rest
        subst after
        rcases growth with kept | appended <;> simp_all only [List.length_append, List.length_singleton, Nat.le_refl] <;> omega

theorem compiler_observe_code_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
    after.function.code = before.function.code := by
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  exact congrArg (fun c => c.function.code) frame

theorem compiler_copy_growth {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (dst src count : U32) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (status, after)) :
    after.function.code.val.length ≤ before.function.code.val.length + 1 := by
  unfold runtime.compiler.FunctionCompiler.copy at accepted
  split at accepted
  · have same : before = after := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
    subst after
    omega
  · split at accepted
    · have same : before = after := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
      subst after
      omega
    · obtain ⟨instruction, _, emitted⟩ := bind_ok_inv _ _ _ accepted
      exact compiler_emit_growth ops law before after instruction status emitted

theorem compiler_pair_code_result {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (a b : U32)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pair ops before a b = .ok (status, after)) :
    after.function.code = before.function.code := by
  unfold runtime.compiler.FunctionCompiler.pair at accepted
  obtain ⟨result, _, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => 
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, output⟩ := rest
      subst after
      rfl
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨result, budget, pairs⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
    cases result with
    | Err error => 
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, output⟩ := rest
        subst after
        rfl
    | Ok value =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨_, output⟩ := rest
      subst after
      rfl

/-- Computing a program counter never modifies code, including rejection. -/
theorem compiler_pc_code_result {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) :
    after.function.code = before.function.code := by
  have effect := compiler_pc ops before
  rw [accepted, WP.spec_ok] at effect
  exact congrArg (fun f => f.code) effect.1

end Exec.Code

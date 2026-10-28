import Exec.Code.Local.Relations.Common.EmissionSources
import Exec.Code.Local.Relations.Control.ControlHeightSuccess
import Exec.Code.Local.Lowering.Common.Copy
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
/-- Exact successful emission needs no separate vector-capacity or coordinate premise. -/
theorem compiler_emit_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (.Ok (), after)) :
    Emitted before after instruction := by
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
        cases value
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨coordinate, coordinateEq, rest⟩ := bind_ok_inv _ _ _ rest
        obtain ⟨⟨result, budget3, sources⟩, sourcesPushed, rest⟩ := bind_ok_inv _ _ _ rest
        simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨rfl, output⟩ := rest
        subst after
        have codeEq := (budget_push_success ops law budget1 budget2 before.function.code code instruction pushedEq).2
        have sourceEq := (budget_push_success ops law budget2 budget3 before.function.source_offsets sources coordinate sourcesPushed).2
        have coord := control_add_success coordinateEq
        exact ⟨budget3, code, sources, rfl, codeEq, by simp [sourceEq, coord]⟩

theorem compiler_copy_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (dst src count : U32) (nonempty : count ≠ 0#u32) (different : src ≠ dst)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (.Ok (), after)) :
    Emitted before after (transferInstruction dst src count) := by
  unfold runtime.compiler.FunctionCompiler.copy at accepted
  rw [if_neg nonempty, if_neg different] at accepted
  split at accepted
  · simp only [bind_ok] at accepted
    simpa [transferInstruction, UScalar.val] using compiler_emit_success ops law before after (.Copy dst src) accepted
  · simp only [bind_ok] at accepted
    simpa [transferInstruction, UScalar.val] using compiler_emit_success ops law before after (.Copy2 dst src) accepted
  · rename_i notOne notTwo
    simp only [bind_ok] at accepted
    have h1 : count.val ≠ 1 := by intro eq; apply notOne; apply UScalar.eq_of_val_eq; exact eq
    have h2 : count.val ≠ 2 := by intro eq; apply notTwo; apply UScalar.eq_of_val_eq; exact eq
    simpa [transferInstruction, h1, h2] using compiler_emit_success ops law before after (.CopyN dst src count) accepted
end Itasca.Runtime.Code

import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentProgram

/-!
Successful emission determines the appended instruction without a separate capacity premise: the actual checked vector append supplies that bound.

Main declarations: `initializer_emit_success` and `initializer_offset_success`. A direct consumer is `Compiler.Local.Relations.Segments.SegmentData`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Successful emission determines the appended instruction without a separate
capacity premise: the actual checked vector append supplies that bound. -/
theorem initializer_emit_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget afterBudget : runtime.compiler.Budget A)
    (before after : alloc.vec.Vec runtime.bytecode.Instr) (instruction : runtime.bytecode.Instr)
    (success : runtime.compiler.initialize.emit ops budget before instruction = .ok (.Ok (), afterBudget, after)) :
    after.val = before.val ++ [instruction] := by
  unfold runtime.compiler.initialize.emit at success
  obtain ⟨⟨result, charged⟩, charge, rest⟩ := initializer_bind_success success
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    exact (budget_push_success ops law charged afterBudget before after instruction rest).2

/-- Integer offsets have a single instruction and no literal-pool allocation. -/
theorem initializer_offset_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget afterBudget : runtime.compiler.Budget A)
    (before after : runtime.bytecode.CompiledFunction) (expr : Itasca.wasm_types.ConstExpr)
    (offset : (∃ bits, expr = .I32 bits) ∨ (∃ index, expr = .GlobalGet index))
    (success : runtime.compiler.initialize.constant ops budget before expr .I32 0#u32 =
      .ok (.Ok (), afterBudget, after)) :
    ∃ instruction, after = {before with code := after.code} ∧
      after.code.val = before.code.val ++ [instruction] ∧
      ConstantInstruction after 0#u32 expr .I32 instruction := by
  rcases offset with ⟨bits, rfl⟩ | ⟨index, rfl⟩
  all_goals
    simp only [runtime.compiler.initialize.constant, lift, bind_ok] at success
    obtain ⟨⟨result, charged, instructions⟩, emitted, rest⟩ := initializer_bind_success success
    have output := Result.ok_injective rest
    have resultEq := congrArg Prod.fst output
    dsimp only at resultEq
    subst result
    have fields := congrArg (fun out => out.2.2) output
    dsimp only at fields
    subst after
    have values := initializer_emit_success ops law budget charged before.code instructions _ emitted
    refine ⟨_, rfl, values, ?_⟩
    first | exact .i32 _ _ | exact .global _ _ (by intro h; cases h)

end Itasca.Runtime.Compiler

import Itasca.Runtime.Compiler.Local.Relations.Segments.SegmentEmit

/-!
Validated data offsets and emitted data-initializer programs.

Main declarations: `valid_offset_shape` and `emit_data_program`. A direct consumer is `Compiler.Local.Relations.Segments.SegmentFinish`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

theorem valid_offset_shape {env : Itasca.module.Env} {expr : Itasca.types.ConstExpr}
    (valid : Itasca.ModuleConstants.Valid env expr .I32) :
    (∃ bits, expr = .I32 bits) ∨ (∃ index, expr = .GlobalGet index) := by
  cases expr with
  | I32 bits => exact .inl ⟨bits, rfl⟩
  | GlobalGet index => exact .inr ⟨index, rfl⟩
  | I64 _ | F32 _ | F64 _ | V128 _ _ | RefFunc _ => cases valid
  | RefNull ty => cases ty <;> cases valid

theorem emit_data_program {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A)
    (before after : runtime.bytecode.CompiledFunction) (index : Usize)
    (segment : Itasca.module.Data)
    (found : module.module.tail.data.val[index.val]? = some segment)
    (valid : ∀ memory offset, segment.mode = .Active memory offset →
      Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.emit_data ops module budget before index =
      .ok (.Ok (), afterBudget, after)) :
    ∃ instructions, DataProgram after index.val segment instructions ∧
      after.code.val = before.code.val ++ instructions ∧
      after = {before with code := after.code, slot_count := after.slot_count} ∧
      (instructions = [] ∧ after.slot_count = before.slot_count ∨
        instructions.length = 5 ∧ after.slot_count = 3#u32) := by
  unfold runtime.compiler.initialize.emit_data at success
  simp only [runtime.compiler.ExecutableModule.tail,
    Itasca.module.Module.impl.tail, bind_ok] at success
  rw [initializer_vec_index _ _ segment found, bind_ok] at success
  cases mode : segment.mode with
  | Passive =>
    simp only [mode] at success
    have output := Result.ok_injective success
    have same := congrArg (fun out => out.2.2) output
    dsimp only at same
    subst after
    exact ⟨[], .passive mode, by simp, rfl, .inl ⟨rfl, rfl⟩⟩
  | Active memory offset =>
    simp only [mode] at success
    obtain ⟨⟨result, b1, first⟩, constant, rest⟩ := initializer_bind_success success
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unitValue =>
      cases unitValue
      obtain ⟨instruction, firstFields, firstCode, firstInstruction⟩ :=
        initializer_offset_success ops law budget b1 {before with slot_count := 3#u32} first offset
          (valid_offset_shape (valid memory offset mode)) constant
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨result, b2, second⟩, emit1, rest⟩ := initializer_bind_success rest
      cases result with
      | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unitValue =>
        cases unitValue
        have code1 := initializer_emit_success ops law b1 b2 first.code second _ emit1
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨result, boundedLen, rest⟩ := initializer_bind_success rest
        cases result with
        | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok length =>
          have countSpec := bounded_index (alloc.vec.Vec.len segment.init)
          rw [boundedLen, WP.spec_ok] at countSpec
          have count := countSpec length rfl
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
          obtain ⟨⟨result, b3, third⟩, emit2, rest⟩ := initializer_bind_success rest
          cases result with
          | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
          | Ok unitValue =>
            cases unitValue
            have code2 := initializer_emit_success ops law b2 b3 second third _ emit2
            simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
            obtain ⟨result, boundedIndex, rest⟩ := initializer_bind_success rest
            cases result with
            | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
            | Ok word =>
              have indexSpec := bounded_index index
              rw [boundedIndex, WP.spec_ok] at indexSpec
              have encoded := indexSpec word rfl
              simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
              obtain ⟨⟨result, b4, fourth⟩, emit3, rest⟩ := initializer_bind_success rest
              cases result with
              | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
              | Ok unitValue =>
                cases unitValue
                have code3 := initializer_emit_success ops law b3 b4 third fourth _ emit3
                simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                obtain ⟨⟨result, b5, fifth⟩, emit4, rest⟩ := initializer_bind_success rest
                cases result with
                | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
                | Ok unitValue =>
                  cases unitValue
                  have code4 := initializer_emit_success ops law b4 b5 fourth fifth _ emit4
                  simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                  have output := Result.ok_injective rest
                  have fields := congrArg (fun out => out.2.2) output
                  dsimp only at fields
                  subst after
                  refine ⟨[instruction, .Const32 1#u32 0#u32, .Const32 2#u32 length,
                    .MemoryInit 0#u32 word, .DataDrop word], ?_, ?_, ?_, ?_⟩
                  · exact .active memory offset mode word length encoded count instruction (firstInstruction.change_code rfl)
                  · simp [code4, code3, code2, code1, firstCode, List.append_assoc]
                  · rw [firstFields]
                  · exact .inr ⟨rfl, by rw [firstFields]⟩

end Itasca.Runtime.Code

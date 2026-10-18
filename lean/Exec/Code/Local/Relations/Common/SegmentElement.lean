import Exec.Code.Local.Relations.Common.SegmentData

namespace Exec.Code
open Aeneas Aeneas.Std

theorem emit_element_program {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A)
    (before after : runtime.bytecode.CompiledFunction) (index : Usize)
    (segment : Itasca.module.Element)
    (found : module.module.env.elements.val[index.val]? = some segment)
    (valid : ∀ table offset, segment.mode = .Active table offset →
      Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.emit_element ops module budget before index =
      .ok (.Ok (), afterBudget, after)) :
    ∃ instructions, ElementProgram after index.val segment instructions ∧
      after.code.val = before.code.val ++ instructions ∧
      after = {before with code := after.code, slot_count := after.slot_count, indirect := after.indirect} ∧
      after.indirect.val.take before.indirect.length = before.indirect.val ∧
      (instructions.length ≤ 1 ∧ after.slot_count = before.slot_count ∨
        instructions.length = 5 ∧ after.slot_count = 3#u32) := by
  unfold runtime.compiler.initialize.emit_element at success
  simp only [runtime.compiler.ExecutableModule.env, Exec.module.Module.env,
    Itasca.module.Module.impl.env, Exec.module.Env.elements, Itasca.module.Env.impl.elements, bind_ok] at success
  rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using found), bind_ok] at success
  cases mode : segment.mode with
  | Passive =>
    simp only [mode] at success
    have output := Result.ok_injective success
    have same := congrArg (fun out => out.2.2) output
    dsimp only at same
    subst after
    exact ⟨[], .passive mode, by simp, rfl, by simp, .inl ⟨by simp, rfl⟩⟩
  | Declarative =>
    simp only [mode] at success
    obtain ⟨result, boundedIndex, rest⟩ := initializer_bind_success success
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok word =>
      have indexSpec := bounded_index index
      rw [boundedIndex, WP.spec_ok] at indexSpec
      have encoded := indexSpec word rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨result, b1, instructions⟩, emitted, rest⟩ := initializer_bind_success rest
      have output := Result.ok_injective rest
      have resultEq := congrArg Prod.fst output
      dsimp only at resultEq
      subst result
      have fields := congrArg (fun out => out.2.2) output
      dsimp only at fields
      subst after
      have code := initializer_emit_success ops law budget b1 before.code instructions _ emitted
      exact ⟨[.ElemDrop word], .declarative mode word encoded, code, rfl, by simp, .inl ⟨by simp, rfl⟩⟩
  | Active table offset =>
    simp only [mode] at success
    obtain ⟨⟨result, b1, first⟩, constant, rest⟩ := initializer_bind_success success
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unitValue =>
      cases unitValue
      obtain ⟨instruction, firstFields, firstCode, firstInstruction⟩ :=
        initializer_offset_success ops law budget b1 {before with slot_count := 3#u32} first offset
          (valid_offset_shape (valid table offset mode)) constant
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
            obtain ⟨result, boundedEntry, rest⟩ := initializer_bind_success rest
            cases result with
            | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
            | Ok entry =>
              have entrySpec := bounded_index (alloc.vec.Vec.len first.indirect)
              rw [boundedEntry, WP.spec_ok] at entrySpec
              have entryEncoded := entrySpec entry rfl
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
                obtain ⟨⟨result, b4, indirect⟩, pushed, rest⟩ := initializer_bind_success rest
                cases result with
                | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
                | Ok unitValue =>
                  cases unitValue
                  have indirectValues := (budget_push_success ops law b3 b4 first.indirect indirect (word, table) pushed).2
                  simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                  obtain ⟨⟨result, b5, fourth⟩, emit3, rest⟩ := initializer_bind_success rest
                  cases result with
                  | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
                  | Ok unitValue =>
                    cases unitValue
                    have code3 := initializer_emit_success ops law b4 b5 third fourth _ emit3
                    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                    obtain ⟨⟨result, b6, fifth⟩, emit4, rest⟩ := initializer_bind_success rest
                    cases result with
                    | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
                    | Ok unitValue =>
                      cases unitValue
                      have code4 := initializer_emit_success ops law b5 b6 fourth fifth _ emit4
                      have output := Result.ok_injective rest
                      have fields := congrArg (fun out => out.2.2) output
                      dsimp only at fields
                      subst after
                      refine ⟨[instruction, .Const32 1#u32 0#u32, .Const32 2#u32 length,
                        .TableInit 0#u32 entry, .ElemDrop word], ?_, ?_, ?_, ?_, ?_⟩
                      · exact .active table offset mode word length entry encoded count
                          (by simp [indirectValues, entryEncoded]) instruction (firstInstruction.change_code rfl)
                      · simp [code4, code3, code2, code1, firstCode, List.append_assoc]
                      · rw [firstFields]
                      · have same := congrArg runtime.bytecode.CompiledFunction.indirect firstFields
                        dsimp only at same
                        simp [indirectValues, same]
                      · exact .inr ⟨rfl, by rw [firstFields]⟩

end Exec.Code

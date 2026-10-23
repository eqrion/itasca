import Exec.Code.Local.Relations.Table.BranchTableLoopSafety
import Exec.Code.Local.Lowering.Common.NumericSafety
namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[step] theorem compiler_lower_table_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (aligned : SourceAligned compiler)
    (depths : ∀ depth ∈ compiler.table_depths.val, depth.val < compiler.frames.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (room : compiler.function.code.val.length + 1 + 2*compiler.table_depths.val.length ≤ Usize.max)
    (tables : compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length)
    (coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.lower_table_branches ops compiler ⦃ _ => True ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches
  step as ⟨startResult,_⟩
  cases startResult with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok start =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step as ⟨lengthResult,_⟩
    cases lengthResult with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok length =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      step with compiler_operand_total ops compiler 1#usize as ⟨operandResult,_⟩
      cases operandResult with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok selector =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        step with compiler_emit ops law compiler (.JumpTable selector start length)
          (by omega) (by rw [aligned]; omega) coordinate as ⟨status,emitted,effect⟩
        cases status with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok unit =>
          cases unit
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
          obtain ⟨budget,code,sources,rfl,codeEq,sourcesEq⟩ := effect rfl
          have size : code.val.length = compiler.function.code.val.length+1 := by simp [codeEq]
          have sourceSize : sources.val.length = compiler.function.source_offsets.val.length+1 := by
            have := congrArg List.length sourcesEq
            simpa only [List.length_map,List.length_append,List.length_singleton] using this
          let next := {compiler with budget,function := {compiler.function with code,source_offsets := sources}}
          have safe : TableLoopSafe next 0 Usize.max := by
            refine ⟨?_,depths,fixups.mono (by dsimp [next]; omega),?_,?_,coordinate⟩
            · change sources.val.length = code.val.length
              rw [sourceSize,size,aligned]
            · change code.val.length + 2*(compiler.table_depths.val.length-0) ≤ Usize.max
              simpa only [size,Nat.sub_zero] using room
            · change compiler.function.jump_tables.val.length ≤ code.val.length
              omega
          step with compiler_table_loop_total ops law next 0#usize (.Ok ()) Usize.max (Nat.le_refl _) (fun _ => safe)
end Exec.Code

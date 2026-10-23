import Exec.Code.Local.Relations.Control.BranchSkipSafety
import Exec.Code.Local.Relations.Table.BranchTableCallback
namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[step] theorem compiler_table_branch_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (index frameIndex : Usize) (depth : U32) (frame : runtime.compiler.Frame)
    (depthAt : compiler.table_depths.val[index.val]? = some depth)
    (frameAt : compiler.frames.val[frameIndex.val]? = some frame)
    (position : frameIndex.val + depth.val + 1 = compiler.frames.val.length)
    (tableFits : compiler.function.jump_tables.val.length < Usize.max)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.table_branch ops compiler index ⦃ _ => True ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.table_branch
  step with compiler_pc ops compiler as ⟨status,current,_,_,budget,same⟩
  subst current
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pc =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with budget_push ops law budget compiler.function.jump_tables pc tableFits as
      ⟨status,budget,table,effect⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      have inside := (List.getElem?_eq_some_iff.mp depthAt).1
      step as ⟨actual,found⟩
      have same : actual = depth := found.trans (List.getElem?_eq_some_iff.mp depthAt).2
      subst actual
      rw [(List.getElem?_eq_some_iff.mp depthAt).2]
      exact compiler_branch_skip_total ops law
        {compiler with budget,function := {compiler.function with jump_tables := table}}
        frame frameIndex depth 1#u32 frameAt position fixupsFit codeFits sourceFits coordinateFits

private theorem charge_branch_total {A} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) :
    runtime.compiler.Budget.charge ops budget .BranchTableEntries ⦃ _ => True ⦄ := by
  simp only [runtime.compiler.Budget.charge]
  split
  · simp [runtime.compiler.Budget.reject]
  · step

@[step] theorem compiler_table_label_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32)
    (fits : compiler.table_depths.val.length < Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops compiler state depth ⦃ _ => True ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
  step with charge_branch_total ops compiler.budget as ⟨status,budget⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok unit =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with budget_push ops law budget compiler.table_depths depth fits
end Exec.Code

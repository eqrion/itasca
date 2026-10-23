import Exec.Code.Local.Relations.Table.BranchTableArguments
import Exec.Code.Local.Relations.Table.BranchTableSuccess
import Exec.Code.Local.Relations.Table.BranchTableHeight
import Exec.Code.Local.Relations.Table.ControlTablePreservation
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Exact syntactic effect of a table arm. Forward destinations retain their
new relocation site; loop arms retain the already resolved backedge. -/
inductive TableTargetCode {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (depth : U32) : Prop where
  | loop (index : Usize) (frame : runtime.compiler.Frame) (source : U32)
      (lookup : before.frames.val[index.val]? = some frame)
      (position : index.val + depth.val + 1 = before.frames.val.length)
      (kind : frame.kind = .Loop)
      (operands : source.val + frame.params.val + 1 = before.height.val)
      (code : after.function.code.val = before.function.code.val ++
        branchInstructions frame.height source frame.params frame.start_pc)
      (frames : after.frames = before.frames) : TableTargetCode before after depth
  | forward (index : Usize) (frame : runtime.compiler.Frame) (source : U32)
      (fixups : alloc.vec.Vec Usize) (site : Usize)
      (lookup : before.frames.val[index.val]? = some frame)
      (position : index.val + depth.val + 1 = before.frames.val.length)
      (kind : frame.kind ≠ .Loop)
      (operands : source.val + frame.results.val + 1 = before.height.val)
      (code : after.function.code.val = before.function.code.val ++
        branchInstructions frame.height source frame.results core.num.U32.MAX)
      (frames : after.frames.val = before.frames.val.set index.val {frame with end_reachable := true,fixups})
      (appended : fixups.val = frame.fixups.val ++ [site])
      (sitePosition : site.val = before.function.code.val.length +
        (if frame.results = 0#u32 ∨ source = frame.height then 0 else 1)) :
      TableTargetCode before after depth

/-- Successful actual arm lowering establishes the complete exact code/fixup
certificate, including source operand safety from its accepted checked arithmetic. -/
theorem compiler_table_target_code {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]? = some depth)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    ∃ target,
      target.val = before.function.code.val.length ∧
      after.function.jump_tables.val = before.function.jump_tables.val ++ [target] ∧
      after.height = before.height ∧
      TableTargetCode before after depth := by
  obtain ⟨target,budget,table,targetEq,tableEq,branchCall⟩ :=
    compiler_table_branch_success ops law before after index depth lookup accepted
  let staged := {before with budget,function := {before.function with jump_tables := table}}
  change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (.Ok (),after) at branchCall
  have tables := compiler_branch_tables ops law staged after depth 1#u32 false branchCall
  have tableAfter := congrArg CompilerTables.jumpTables tables
  change after.function.jump_tables.val = table.val at tableAfter
  have height := compiler_branch_height_result ops law staged after depth 1#u32 false (.Ok ()) branchCall
  obtain ⟨frameIndex,frame,source,found,position,operands⟩ :=
    compiler_branch_arguments_success ops staged after depth 1#u32 branchCall
  refine ⟨target,targetEq,tableAfter.trans tableEq,height,?_⟩
  by_cases isLoop : frame.kind = .Loop
  · have width : source.val + frame.params.val + (1#u32).val = staged.height.val := by
      simpa only [frameBranchWidth,isLoop] using operands
    obtain ⟨code,frames⟩ := compiler_branch_loop_skip_success ops law staged frame frameIndex depth source 1#u32
      found position isLoop width after branchCall
    exact .loop frameIndex frame source found position isLoop width code frames
  · have width : source.val + frame.results.val + (1#u32).val = staged.height.val := by
      cases kind : frame.kind <;> simp_all [frameBranchWidth]
    obtain ⟨fixups,frames,_,code,site,sitePosition,appended⟩ := compiler_branch_forward_skip_success ops law staged frame frameIndex depth source 1#u32
      found position isLoop width after branchCall
    exact .forward frameIndex frame source fixups site found position isLoop width code frames appended sitePosition
end Exec.Code

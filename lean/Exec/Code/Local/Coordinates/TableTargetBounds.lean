import Exec.Code.Local.Source.JumpTableBounds
import Exec.Code.Local.Source.BranchCodeStrict
import Exec.Code.Local.Relations.Table.BranchTableSafetyEffects

namespace Exec.Code
open Aeneas Aeneas.Std

/-- A table stub records its PC before lowering its branch. Actual branch code
then grows strictly, putting the recorded target inside the resulting vector. -/
theorem compiler_table_branch_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]? = some depth)
    (held : JumpTableBounds before)
    (called : runtime.compiler.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    JumpTableBounds after := by
  obtain ⟨target,budget,table,position,appended,branch⟩ := compiler_table_branch_success ops law before after index depth lookup called
  let staged := {before with budget,function := {before.function with jump_tables := table}}
  change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (.Ok (),after) at branch
  have growth := compiler_branch_code_strict ops law staged after depth 1#u32 false branch
  have tables := congrArg CompilerTables.jumpTables (compiler_branch_tables ops law staged after depth 1#u32 false branch)
  change after.function.jump_tables.val = table.val at tables
  intro entry member
  rw [tables,appended] at member
  simp only [List.mem_append,List.mem_singleton] at member
  rcases member with prior | rfl
  · exact (held entry prior).trans (by simpa only [staged] using growth)
  · simpa only [position,staged] using growth

/-- Every actual branch in the finite lowering loop retains bounded targets. -/
theorem TableBranchRun.jumpTableBounds {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index : Nat} (run : TableBranchRun ops before index after) (held : JumpTableBounds before) :
    JumpTableBounds after := by
  induction run with
  | done => exact held
  | @cons before middle after index inbounds called rest ih =>
    let depth := before.table_depths.val[index.val]
    exact ih (compiler_table_branch_target_bounds ops law before middle index depth
      (List.getElem?_eq_getElem inbounds) held called)

/-- The actual dispatch emission and complete stub loop establish all jump-table
bounds without assuming loop acceptance or a completed code certificate. -/
theorem compiler_lower_table_target_bounds {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (held : JumpTableBounds before)
    (called : runtime.compiler.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    JumpTableBounds after := by
  obtain ⟨start,len,selector,emitted,_,_,_,emission,run⟩ := compiler_lower_table_success ops law before after called
  exact run.jumpTableBounds law (emission.jumpTableBounds held)

end Exec.Code

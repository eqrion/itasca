import Exec.Code.Local.Callbacks.Common.FixupBudget
import Exec.Code.Local.Capacity.BranchTableGrowth
import Exec.Code.Local.Relations.Table.BranchTableFrames
import Exec.Code.Local.Relations.Table.BranchTableMetadata
import Exec.Code.Local.Relations.Control.ControlCursor
import Exec.Code.Local.Relations.Table.TableSources
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000

theorem TableTargetCode.fixup_budget {A} {before after : runtime.compiler.FunctionCompiler A}
    {depth : U32} (effect : TableTargetCode before after depth)
    (budget : FixupBudget before.frames.val before.function.code.val.length) :
    FixupBudget after.frames.val after.function.code.val.length := by
  obtain ⟨fragment,code,growth⟩ := effect.code_prefix
  have larger : before.function.code.val.length + 1 ≤ after.function.code.val.length := by
    simp only [code,List.length_append]; omega
  cases effect with
  | loop index frame source lookup position kind operands code frames =>
    rw [frames]
    exact budget.mono (by omega)
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    rw [frames]
    exact budget.branch index.val frame fixups lookup (by simp [appended]) larger

theorem compiler_table_branch_cursor {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]? = some depth)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    after.next_source = before.next_source := by
  obtain ⟨target,budget,table,_,_,called⟩ :=
    compiler_table_branch_success ops law before after index depth lookup accepted
  let staged := {before with budget,function := {before.function with jump_tables := table}}
  change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (.Ok (),after) at called
  exact compiler_branch_cursor ops law staged after depth 1#u32 false called
/-- Allocation room retained while lowering a finite list of table targets. -/
structure TableLoopSafe {A} (compiler : runtime.compiler.FunctionCompiler A)
    (index limit : Nat) : Prop where
  aligned : SourceAligned compiler
  depths : ∀ depth ∈ compiler.table_depths.val, depth.val < compiler.frames.val.length
  fixups : FixupBudget compiler.frames.val compiler.function.code.val.length
  room : compiler.function.code.val.length + 2 * (compiler.table_depths.val.length - index) ≤ limit
  tables : compiler.function.jump_tables.val.length ≤ compiler.function.code.val.length
  coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max

theorem TableLoopSafe.advance {A} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {before after : runtime.compiler.FunctionCompiler A} {index : Usize} {limit : Nat}
    (safe : TableLoopSafe before index.val limit)
    (inside : index.val < before.table_depths.val.length)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    TableLoopSafe after (index.val+1) limit := by
  let depth := before.table_depths.val[index.val]
  have lookup : before.table_depths.val[index.val]? = some depth := by simp [depth,inside]
  obtain ⟨target,targetPC,appended,height,effect⟩ :=
    compiler_table_target_code ops law before after index depth lookup accepted
  have same := compiler_table_branch_depths ops before after index (.Ok ()) accepted
  have growth := effect.code_growth
  obtain ⟨fragment,code,positive⟩ := effect.code_prefix
  have grows : before.function.code.val.length + 1 ≤ after.function.code.val.length := by
    simp only [code,List.length_append]; omega
  have metadata := (compiler_table_branch_fixed ops law before after index depth lookup accepted).stable.fields
  have cursor := compiler_table_branch_cursor ops law before after index depth lookup accepted
  refine ⟨(compiler_table_branch_sources ops law before after index accepted).aligned safe.aligned,
    ?_,effect.fixup_budget safe.fixups,?_,?_,?_⟩
  · rw [same,effect.frame_length]
    exact safe.depths
  · rw [same]
    have room := safe.room
    omega
  · simp only [appended,List.length_append,List.length_singleton]
    have tables := safe.tables
    omega
  · rw [metadata.2.2.2.2.2.2.2.1,cursor]
    exact safe.coordinate
end Itasca.Runtime.Code

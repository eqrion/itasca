import Exec.Code.Local.Checking.TableDispatchInstructionPrefix
import Exec.Code.Local.Source.TableTransferBounds
import Exec.Code.Local.Checking.LoopBranchInstructionPrefix
import Exec.Code.Local.Relations.Table.BranchTableSafetyEffects

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- One actual table arm appends a checked transfer and an owned or backward
jump. Its source transfer interval and allocation room are retained separately
from the temporarily incomplete dispatch instruction. -/
theorem compiler_table_branch_instruction_effect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (limit : Nat)
    (lookup : before.table_depths.val[index.val]? = some depth)
    (safe : TableLoopSafe before index.val limit) (limitFits : limit ≤ Usize.max)
    (transfers : TableTransferBounds before)
    (heightFits : before.height.val ≤ before.function.slot_count.val)
    (called : runtime.compiler.control.FunctionCompiler.table_branch ops before index = .ok (.Ok (),after)) :
    InstructionAppendEffect before after := by
  obtain ⟨target,budget,table,_,appended,branch⟩ :=
    compiler_table_branch_success ops law before after index depth lookup called
  let staged := {before with budget,function := {before.function with jump_tables := table}}
  change runtime.compiler.control.FunctionCompiler.branch ops staged depth 1#u32 false = .ok (.Ok (),after) at branch
  obtain ⟨selected,frame,source,found,position,operands⟩ :=
    compiler_branch_arguments_success ops staged after depth 1#u32 branch
  have geometry := transfers depth (List.mem_of_getElem? lookup) selected frame found position
  have inside := (List.getElem?_eq_some_iff.mp lookup).1
  have room := safe.room
  have codeFits : before.function.code.val.length+2 ≤ Usize.max := by omega
  have aligned := safe.aligned
  change before.function.source_offsets.val.length = before.function.code.val.length at aligned
  have offsetsFit : before.function.source_offsets.val.length+2 ≤ Usize.max := by omega
  have prepared := instruction_append_effect_jump_table before budget table target appended
  apply prepared.prepend_unchanged rfl
  have sourcePosition : source.val+(frameBranchWidth frame).val+1 = before.height.val := operands
  by_cases loop : frame.kind = .Loop
  · have width : frameBranchWidth frame = frame.params := by simp [frameBranchWidth,loop]
    rw [width] at sourcePosition geometry
    exact compiler_branch_loop_instruction_effect ops law staged after frame selected depth source 1#u32
      found position loop sourcePosition (by omega) (by simpa only [staged] using (show source.val+frame.params.val ≤ before.function.slot_count.val by omega))
      (geometry.2 loop) codeFits offsetsFit safe.coordinate branch
  · have width : frameBranchWidth frame = frame.results := by
      cases kind : frame.kind <;> simp_all [frameBranchWidth]
    rw [width] at sourcePosition geometry
    exact compiler_branch_forward_instruction_effect ops law staged after frame selected depth source 1#u32
      found position loop sourcePosition (by omega) (by simpa only [staged] using (show source.val+frame.results.val ≤ before.function.slot_count.val by omega))
      (safe.fixups.lookup found (by omega)) codeFits offsetsFit safe.coordinate branch

end Itasca.Runtime.Code
